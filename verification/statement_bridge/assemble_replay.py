#!/usr/bin/env python3
"""Copy the exact verified inputs into a new external directory, without downloading."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys
package=Path(__file__).resolve().parent
public_root=package.parents[1]
def require(c,m):
 if not c:raise ValueError(m)
require(len(sys.argv)==2,'Usage: python3 assemble_replay.py /absolute/new/replay-directory')
dest=Path(sys.argv[1]).resolve()
require(not dest.exists(),'Destination already exists; use a new directory')
require(not dest.is_relative_to(public_root),'Keep generated replay files outside the public checkout')
subprocess.run([sys.executable,str(package/'verify_package.py')],check=True)
inputs=json.loads((package/'verification/SOURCE_MANIFEST.json').read_text())['input_sha256']
selected={}
for rel,digest in inputs.items():
 source=package/rel if (package/rel).is_file() else public_root/rel
 require(source.is_file() and not source.is_symlink(),f'Missing/unsafe source: {rel}')
 require(hashlib.sha256(source.read_bytes()).hexdigest()==digest,f'Changed source: {rel}')
 selected[rel]=source
for directory in ['scripts','upstream']:
 for p in (package/directory).iterdir():
  if p.is_file():selected[p.relative_to(package).as_posix()]=p
for name in ['SOURCE_MANIFEST.json','ORIGINAL_SOURCE_MANIFEST.json','TOOLCHAIN.json','VERIFICATION_CODE_MANIFEST.json']:
 selected['verification/'+name]=package/'verification'/name
dest.mkdir(parents=True)
for rel,source in selected.items():
 target=dest/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
shutil.copyfile(public_root/'LICENSE',dest/'LICENSE-proof')
subprocess.run([sys.executable,str(dest/'scripts/check_sources.py')],check=True)
print(f'Assembled {len(inputs)} exact Lean/config inputs at {dest}; no Lean build or download performed.')
print('Next: cd to that directory; python3 scripts/bootstrap.py; python3 scripts/run_verification.py')
