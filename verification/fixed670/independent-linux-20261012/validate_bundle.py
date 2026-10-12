from pathlib import Path
import hashlib,json,re
B=Path(__file__).resolve().parent
manifest=json.loads((B/'MANIFEST_SHA256.json').read_text())
for row in manifest['files']:
 p=B/row['path']
 assert p.is_file(),row['path']
 assert p.stat().st_size==row['bytes'],row['path']
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],row['path']
r=json.loads((B/'replay/RECEIPT.json').read_text())
s=json.loads((B/'source-pins/SOURCE_MANIFEST.json').read_text())
assert r['status']=='PASS' and r['module_count']==54 and r['clean_project_olean_count_before']==0
modules=[m['module'] for m in s['modules']]
assert len(modules)==54 and len(r['commands'])==56
assert r['produced_project_oleans']==sorted('.lake/build/lib/lean/'+m.replace('.','/')+'.olean' for m in modules)
for i,row in enumerate(r['commands']):
 assert row['exit_code']==0
 assert hashlib.sha256((B/'replay'/row['log']).read_bytes()).hexdigest()==row['log_sha256']
 if i<54: assert row['command']==['lake','--no-cache','build',modules[i]]
assert r['commands'][-2]['command']==['lake','--no-cache','build']
assert r['commands'][-1]['command']==['lake','env','lean','--trust=0','AxiomAudit.lean']
a=(B/'replay'/r['commands'][-1]['log']).read_text()
p=re.findall(r"^'([^']+)' depends on axioms:\s*\[([^]]*)\]",a,re.M)
d=re.findall(r'^#print axioms\s+(\S+)',(B/'source-pins/AxiomAudit.lean').read_text(),re.M)
assert len(p)==6 and [n for n,_ in p]==d
assert all({v.strip() for v in axs.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,axs in p)
k=json.loads((B/'FRESH_KERNEL_REPLAY_RECEIPT.json').read_text())
assert k['status']=='PASS' and k['exit_code']==0
assert hashlib.sha256((B/k['stdout_stderr_log']).read_bytes()).hexdigest()==k['stdout_stderr_log_sha256']
assert k['command']==['lake','env','leanchecker','--fresh',s['root_module']]
release=json.loads((B/'logs/official-release-provenance.json').read_text())
assert release['asset']['digest']=='sha256:'+k['toolchain_distribution_sha256']
print(f"PASS: {len(manifest['files'])} evidence-file hashes, 56 successful command records, six standard-only axiom records, and successful pinned fresh-kernel record")
print('This validates archived evidence integrity and consistency; it does not execute Lean or independently authenticate the recorded execution.')
