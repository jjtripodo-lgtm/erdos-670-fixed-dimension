"""Read-only checks of the exact finite-result Lean inputs and recorded build scope."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    manifest = json.loads((HERE / 'SOURCE_MANIFEST.json').read_text())
    require(manifest['schema_version'] == 1, 'Unsupported manifest schema')
    expected = manifest['lean_input_files_sha256']
    actual = {}
    for path in (ROOT / 'lean').rglob('*'):
        relative = path.relative_to(ROOT)
        if '.lake' in relative.parts or '__pycache__' in relative.parts:
            continue
        require(not path.is_symlink(), f'Symlink: {relative}')
        if path.is_file():
            actual[relative.as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    require(actual == expected, 'Lean input file inventory or hashes differ')
    require(len(actual) == 70, 'Expected 70 Lean input files')
    map_hash = hashlib.sha256(json.dumps(actual, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    require(map_hash == manifest['lean_input_map_sha256'], 'Input-map hash differs')
    records = manifest['lean_modules']
    modules = {record['module']: record for record in records}
    require(len(modules) == len(records) == 66, 'Expected 66 unique modules')
    for module, record in modules.items():
        relative = 'lean/' + module.replace('.', '/') + '.lean'
        require(relative == record['path'], f'Module path differs: {module}')
        raw = (ROOT / relative).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == record['sha256'], f'Module hash differs: {module}')
        require(hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == record['git_blob'], f'Git blob differs: {module}')
        imports = [name for line in re.findall(r'^import\s+(.+)$', raw.decode(), re.M) for name in line.split()]
        require(imports == record['imports'], f'Imports differ: {module}')
    visited = set()
    def visit(module):
        require(module in modules, f'Missing local import: {module}')
        if module in visited:
            return
        visited.add(module)
        for dependency in modules[module]['imports']:
            if dependency.startswith(('Erdos488.', 'Erdos287.', 'Erdos708.')):
                visit(dependency)
    visit(manifest['root_module'])
    require(visited == set(modules), 'Module set is not the exact root closure')
    require(sum(m.split('.')[-1].startswith('Pass5') for m in modules) == 16, 'Expected 16 Pass5 modules')
    lock = json.loads((ROOT / 'lean/lake-manifest.json').read_text())
    require(len(lock['packages']) == 9, 'Expected nine pinned dependencies')
    mathlib = [p for p in lock['packages'] if p['name'] == 'mathlib']
    require(len(mathlib) == 1 and mathlib[0]['rev'] == manifest['mathlib_rev'], 'Mathlib pin differs')
    require((ROOT / 'lean/lean-toolchain').read_text().strip() == manifest['lean_toolchain'], 'Lean pin differs')
    lakefile = (ROOT / 'lean/lakefile.toml').read_text()
    require(manifest['root_module'] in lakefile and '--trust=0' in lakefile, 'Build target or trust setting differs')
    receipt = json.loads((HERE / 'LEAN_BUILD.json').read_text())
    require(receipt['status'] == 'PASS' and receipt['lean_input_map_sha256'] == map_hash, 'Build summary source identity differs')
    require(receipt['lean_input_file_count'] == 70 and receipt['local_module_count'] == 66, 'Build summary count differs')
    require(receipt['initial_local_project_object_count'] == 0 and receipt['fresh_local_modules_built'] == 66, 'Build summary closure scope differs')
    require(receipt['lake_build']['exit_code'] == receipt['axiom_audit']['exit_code'] == 0, 'Recorded command failure')
    require(receipt['final_endpoint_axioms'] == ['propext', 'Classical.choice', 'Quot.sound'], 'Axiom allowlist differs')
    require(receipt['upstream_dependency_cache_reused'] is True and receipt['same_cloud_computer'] is True, 'Cache or machine scope differs')
    require(receipt['clean_upstream_rebuild'] == receipt['second_machine_replay'] == 'NOT_RUN', 'Unsubstantiated replay scope')
    print('PASS: 70 exact Lean inputs; 66-module transitive closure; pinned dependencies; source-bound build summary')


if __name__ == '__main__':
    main()
