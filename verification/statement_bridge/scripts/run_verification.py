#!/usr/bin/env python3
"""Fresh local-source build, official fresh-kernel replay, and transitive axiom audit."""
from pathlib import Path
import hashlib,json,os,re,shutil,signal,subprocess,sys,time
root=Path(__file__).resolve().parents[1];lean=root/'lean';v=root/'verification';v.mkdir(exist_ok=True)
env=dict(os.environ);env['PATH']=str(root/'.toolchain/lean-4.31.0-rc1-linux/bin')+':'+env['PATH']
env.update(LEAN_NUM_THREADS='2',MATHLIB_CACHE_DIR=str(root/'.cache/mathlib'),MATHLIB_NO_CACHE_ON_UPDATE='1',GIT_TERMINAL_PROMPT='0')
def utc():return time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def objects():return list((lean/'.lake/build/lib/lean').glob('Erdos*/**/*.olean'))
receipt_path=v/'BUILD_RECEIPT.json';assert not receipt_path.exists(),'Preserve each attempted run separately; do not overwrite a receipt'
subprocess.run([sys.executable,str(root/'scripts/check_sources.py')],check=True)
assert len(objects())==0,'This replay requires zero initial local project objects'
manifest_digest=digest(v/'SOURCE_MANIFEST.json')
receipt={'status':'RUNNING','started_utc':utc(),'reconstruction_after_lost_ephemeral_workspace':True,'prior_pass_receipts_reused':False,'source_manifest_sha256':manifest_digest,'initial_local_project_olean_count':0,'reserve_bytes':512*1024**2,'upstream_dependency_cache_reused':True,'same_cloud_computer':True,'clean_upstream_source_rebuild':'NOT_RUN','independent_second_machine_replay':'NOT_RUN','independent_external_kernel':'NOT_RUN','current_formal_conjectures_full_project_build':'NOT_RUN','commands':[]}
def save():receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
def process_cpu(pid):
 # All processes of this command are visible in this wrapper's PID namespace.
 rows={}
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   s=(p/'stat').read_text().rsplit(')',1)[1].split();rows[int(p.name)]=(int(s[1]),sum(float(s[i]) for i in [11,12,13,14])/os.sysconf('SC_CLK_TCK'))
  except (OSError,ValueError,IndexError):pass
 selected={pid}
 while True:
  added={n for n,(parent,_) in rows.items() if parent in selected}-selected
  if not added:break
  selected|=added
 return sum(rows[n][1] for n in selected if n in rows)
imports=sorted({m for p in lean.rglob('*.lean') if '.lake' not in p.parts for m in re.findall(r'^import\s+(Mathlib\S*)',p.read_text(),re.M)})
commands=[('cache',['lake','--no-cache','exe','cache','get',*imports]),('build',['lake','--verbose','--no-cache','build']),('fresh-kernel',['lake','env','leanchecker','--fresh','--verbose','Erdos670Bridge.Bridge']),('axioms',['lake','env','lean','--trust=0','AxiomAudit.lean'])]
save()
for label,argv in commands:
 start=time.monotonic();minimum=shutil.disk_usage(root).free;log=v/(label+'.log');assert minimum>1024**3
 record={'label':label,'argv':argv,'started_utc':utc(),'log':str(log.relative_to(root))};receipt['active_command']=record;save();print('START',label,utc(),flush=True)
 with log.open('w') as output:
  child=subprocess.Popen(argv,cwd=lean,env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
  beat=0
  while child.poll() is None:
   minimum=min(minimum,shutil.disk_usage(root).free)
   if minimum<576*1024**2:
    os.killpg(child.pid,signal.SIGTERM);receipt['status']='STOPPED_DISK_RESERVE';save();raise SystemExit('Stopped before disk reserve exhausted')
   if time.monotonic()-beat>10:
    (v/'LIVE_STATUS.json').write_text(json.dumps({'sampled_utc':utc(),'command':label,'elapsed_seconds':time.monotonic()-start,'process_tree_cpu_seconds':process_cpu(child.pid),'free_disk_bytes':shutil.disk_usage(root).free,'log_bytes':log.stat().st_size},indent=2)+'\n');beat=time.monotonic()
   time.sleep(.5)
  code=child.wait()
 record.update(exit_code=code,elapsed_seconds=time.monotonic()-start,completed_utc=utc(),minimum_observed_free_bytes=minimum,log_sha256=digest(log));receipt['commands'].append(record);receipt.pop('active_command',None);save();print('END',label,'exit',code,utc(),flush=True)
 if code:receipt['status']='FAIL';save();raise SystemExit(code)
 assert digest(v/'SOURCE_MANIFEST.json')==manifest_digest
subprocess.run([sys.executable,str(root/'scripts/check_sources.py')],check=True)
subprocess.run([sys.executable,str(root/'scripts/check_axioms.py')],check=True)
assert len(objects())==68
text=(v/'build.log').read_text();built=re.findall(r'Built (Erdos\S+)',text);assert len(built)==len(set(built))==68
assert sum(n.startswith('Erdos488.') for n in built)==66
assert len(re.findall(r'^trace:.*?/bin/lean --trust=0 .*?/lean/Erdos',text,re.M))==68
axes={n:[a.strip() for a in raw.split(',') if a.strip()] for n,raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",(v/'axioms.log').read_text())}
receipt.update(status='PASS',completed_utc=utc(),final_local_project_olean_count=68,fresh_local_modules_built=68,geometric_proof_modules_unchanged=66,local_source_trust_level=0,build_jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',text).group(1)),endpoint_transitive_axioms=axes,fresh_kernel_safe_declaration_closure_replay='PASS',fresh_replay_scope='Official same-kernel replay of final module and loaded imported safe, non-partial declarations into a fresh environment; unsafe/partial metaprograms skipped',record_type='New source-bound local execution record after lost ephemeral workspace; not an independent certificate')
save();print('PASS: NEW complete source-bound build, fresh-kernel replay and axiom audit',flush=True)
