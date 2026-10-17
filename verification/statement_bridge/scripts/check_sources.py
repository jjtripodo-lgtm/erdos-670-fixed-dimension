#!/usr/bin/env python3
"""Offline exact statement, source-closure and frozen-input checks; not a Lean replay."""
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
 b=p.read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
expected_blobs={'670.lean.txt':'1ae473043edcd960c0b9eed81ccd6e82994f2a22','lean-toolchain':'a8afa7d1b02d96f0671eba854a8dc4b416beb473','lake-manifest.json':'fae5d498d3f9dc3f6d1efd7c2adc03dd5bb6c8d6'}
for name,digest in expected_blobs.items():assert blob(root/'upstream'/name)==digest,name
upstream=(root/'upstream/670.lean.txt').read_text();statement=(root/'lean/Erdos670Bridge/Statement.lean').read_text();bridge=(root/'lean/Erdos670Bridge/Bridge.lean').read_text()
definition=lambda s:re.search(r'def HasSeparatedDistances .*?(?=\n\n)',s,re.S).group()
prop=re.search(r'theorem erdos_670 :\n(.*?) := by\n  sorry',upstream,re.S).group(1)
assert definition(statement)==definition(upstream)
assert re.search(r'def FixedDimensionStatement : Prop :=\n(.*?)(?=\n\nend Erdos670)',statement,re.S).group(1)==prop
shown=re.search(r'theorem erdos_670_negated :\n    ¬ \((.*?)\) :=\n',bridge,re.S).group(1)
assert ' '.join(shown.replace('Erdos670.HasSeparatedDistances','HasSeparatedDistances').split())==' '.join(prop.split())
original=json.loads((root/'verification/ORIGINAL_SOURCE_MANIFEST.json').read_text());records=original['lean_modules']
assert len(records)==66
modules={r['module']:root/r['path'] for r in records}
for r in records:assert sha(root/r['path'])==r['sha256'],r['path']
for name in ['lean-toolchain','lake-manifest.json']:assert sha(root/'lean'/name)==original['lean_input_files_sha256']['lean/'+name]
modules.update({n:root/'lean'/Path(*n.split('.')).with_suffix('.lean') for n in ['Erdos670Bridge.Statement','Erdos670Bridge.Bridge']})
seen=set()
def visit(n):
 if n in seen:return
 seen.add(n)
 for imported in re.findall(r'^import\s+(\S+)',modules[n].read_text(),re.M):
  if imported.startswith(('Erdos488.','Erdos670Bridge.')):
   assert imported in modules,imported
   visit(imported)
visit('Erdos670Bridge.Bridge');assert seen==set(modules)
for p in (root/'lean').rglob('*.lean'):
 if '.lake' in p.parts:continue
 code=re.sub(r'/-.*?-/','',p.read_text(),flags=re.S);code=re.sub(r'--[^\n]*','',code)
 assert not re.search(r'\b(sorry|admit|axiom)\b',code),p
 assert not re.search(r'^\s*(?:public )?import FormalConjectures',code,re.M),p
manifest=root/'verification/SOURCE_MANIFEST.json'
if manifest.exists():
 expected=json.loads(manifest.read_text())['input_sha256']
 actual={p.relative_to(root).as_posix():sha(p) for p in (root/'lean').rglob('*') if p.is_file() and '.lake' not in p.parts}
 assert actual==expected
 assert len(actual)==72
print('PASS: exact pinned definition/proposition/negation; 66 unchanged geometric modules; complete 68-module closure; no local proof holes or new axioms; exact 72 input files when frozen')
