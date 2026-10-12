#!/usr/bin/env python3
"""Read-only verification of the fixed #670 source closure and frozen release."""
import argparse,hashlib,json,pathlib,re,sys

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify(package,freeze=True):
    repo=package.parent; evidence=repo/'verification/fixed670'
    manifest=json.loads((evidence/'SOURCE_MANIFEST.json').read_text())
    errors=[]; expected={r['path']:r for r in manifest['modules']}
    if manifest['module_count']!=len(expected):errors.append('Manifest module count differs')
    by_module={r['module']:r for r in manifest['modules']}
    reachable=set()
    def visit(module):
        if module in reachable:return
        row=by_module.get(module)
        if row is None:
            errors.append(f'Missing project import: {module}');return
        reachable.add(module)
        for dep in row['imports']:
            if dep.startswith('Erdos488.'):visit(dep)
    visit(manifest['root_module'])
    if reachable!=set(by_module):errors.append('Manifest contains modules outside final import closure')
    actual={str(p.relative_to(package)) for p in (package/'Erdos488').rglob('*.lean')}
    if actual!=set(expected):errors.append('Source module inventory differs from manifest')
    for rel,row in expected.items():
        p=package/rel
        if not p.is_file():errors.append(f'Missing {rel}');continue
        raw=p.read_bytes()
        if digest(p)!=row['sha256']:errors.append(f'SHA256 mismatch: {rel}')
        blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        if blob!=row['git_blob']:errors.append(f'Git blob mismatch: {rel}')
        imports=[m for line in re.findall(r'^import\s+(.+)$',raw.decode(),re.M) for m in line.split()]
        if imports!=row['imports']:errors.append(f'Import graph mismatch: {rel}')
    lock=json.loads((package/'lake-manifest.json').read_text())
    if lock['packages']!=manifest['external_dependencies']:errors.append('Locked dependency versions differ')
    upstream=json.loads((evidence/'upstream-lake-manifest.json').read_text())
    if upstream['packages']!=manifest['external_dependencies']:errors.append('Upstream dependency lock differs')
    if lock['name']!='erdos670_fixed':errors.append('Standalone Lake package name differs')
    if (package/'lean-toolchain').read_bytes()!=(evidence/'upstream-lean-toolchain').read_bytes():errors.append('Toolchain differs')
    if freeze:
        frozen=evidence/'FROZEN_FILES_SHA256.json'
        if not frozen.is_file():errors.append('Release freeze is absent')
        else:
            for rel,h in json.loads(frozen.read_text()).items():
                p=repo/rel
                if not p.is_file() or digest(p)!=h:errors.append(f'Frozen file mismatch: {rel}')
    return errors

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--sources-only',action='store_true');ap.add_argument('--package',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parent);args=ap.parse_args()
    errors=verify(args.package,freeze=not args.sources_only)
    for e in errors:print(e,file=sys.stderr)
    if errors:raise SystemExit(1)
    count=json.loads((args.package.parent/'verification/fixed670/SOURCE_MANIFEST.json').read_text())['module_count']
    print(f'PASS: {count} exported module hashes/imports and closure, exact dependency lock and toolchain'+('' if args.sources_only else ', candidate source-file hashes'))
