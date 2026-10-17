#!/usr/bin/env python3
"""Install the pinned official Linux x86_64 Lean release and locked public sources.
Network access and approximately 12 GiB of free disk are required. No credentials,
package upgrades, hosted CI, or paid service are configured by this script.
"""
from pathlib import Path
import hashlib,json,platform,shutil,subprocess,urllib.request
root=Path(__file__).resolve().parents[1]
assert platform.system()=='Linux' and platform.machine()=='x86_64'
pin=json.loads((root/'verification/TOOLCHAIN.json').read_text())
assert pin['sha256']=='055f1780f20f9774bbe270d5d4cf7561fb26ee6734c0917ba6cfb867e33cb99e'
assert pin['url']=='https://github.com/leanprover/lean4/releases/download/v4.31.0-rc1/lean-4.31.0-rc1-linux.tar.zst'
target=root/'.toolchain/lean-4.31.0-rc1-linux'
if not target.exists():
 assert shutil.disk_usage(root).free>=12*1024**3,'At least 12 GiB free required before bootstrap'
 archive=root/'downloads/lean-4.31.0-rc1-linux.tar.zst';archive.parent.mkdir(exist_ok=True)
 if not archive.exists():
  with urllib.request.urlopen(pin['url']) as source, archive.open('xb') as dest:
   while block:=source.read(4*1024**2):
    assert shutil.disk_usage(root).free>1024**3,'Stopping before reserve is exhausted'
    dest.write(block)
 assert archive.stat().st_size==pin['bytes']
 with archive.open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==pin['sha256']
 entries=subprocess.check_output(['tar','--zstd','-tf',str(archive)],text=True).splitlines()
 assert all(not x.startswith('/') and '..' not in Path(x).parts and x.startswith('lean-4.31.0-rc1-linux/') for x in entries)
 target.parent.mkdir(exist_ok=True)
 subprocess.run(['tar','--zstd','-xf',str(archive),'-C',str(target.parent)],check=True)
version=subprocess.check_output([str(target/'bin/lean'),'--version'],text=True).strip()
assert version==pin['version'],version
print(version)
subprocess.run(['python3',str(root/'scripts/fetch_dependencies.py')],check=True)
