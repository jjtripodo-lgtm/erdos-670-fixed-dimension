"""Read-only verification of the public package with version-specific paper checks."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    manifest = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_text())
    require(manifest['schema_version'] == 1, 'Unsupported package manifest')
    actual = {}
    for path in ROOT.rglob('*'):
        rel = path.relative_to(ROOT)
        if any(part in {'.git', '.lake', '__pycache__'} for part in rel.parts):
            continue
        require(not path.is_symlink(), f'Unexpected symlink: {rel}')
        if not path.is_file() or rel.as_posix() == 'SOURCE_MANIFEST.json':
            continue
        if rel.as_posix() in {'paper/fixed_dimension_670.aux', 'paper/fixed_dimension_670.log', 'paper/fixed_dimension_670.out'} or (rel.parent.as_posix() == 'paper/2026-10-20' and rel.suffix in {'.aux', '.log', '.out'}):
            continue
        raw = path.read_bytes()
        actual[rel.as_posix()] = {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}
    require(actual == manifest['files'], 'Package file inventory, sizes, or hashes differ')
    record = json.loads((ROOT / 'verification/manuscript670/PAPER_VALIDATION.json').read_text())
    for field, path in [('source', 'paper/fixed_dimension_670.tex'), ('pdf', 'paper/fixed_dimension_670.pdf'), ('source_zip', 'paper/fixed_dimension_670_source.zip')]:
        require(actual[path]['sha256'] == record[field + '_sha256'], f'Paper receipt {field} hash differs')
    source = (ROOT / 'paper/fixed_dimension_670.tex').read_bytes()
    with zipfile.ZipFile(ROOT / 'paper/fixed_dimension_670_source.zip') as archive:
        require(archive.namelist() == ['orthogonal_circles.tex'], 'Unexpected source ZIP inventory')
        require(archive.read('orthogonal_circles.tex') == source, 'Source ZIP and TeX differ')
    require((ROOT / 'paper/fixed_dimension_670.pdf').read_bytes().startswith(b'%PDF-'), 'Invalid PDF header')
    text = source.decode()
    require(text.count('The author thanks Boon Suan Ho for helpful comments on an earlier draft of this manuscript.') == 1, 'Acknowledgment differs')
    require('f1604c368efce996a9af4d46f581e676e49054f5' in text, 'Current proof pin missing')
    require('36354' in text and '81794' in text and r'\frac{147}{200}' in text, 'Finite theorem fields missing')
    subprocess.run([sys.executable, str(ROOT / 'verification/finite670/verify_sources.py')], check=True)
    subprocess.run([sys.executable, str(ROOT / 'paper/2026-10-20/verification/verify_paper.py')], check=True)
    print(f'PASS: {len(actual)} public package files, unchanged finite paper and new version-specific manuscript checks')


if __name__ == '__main__':
    main()
