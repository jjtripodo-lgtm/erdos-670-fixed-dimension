#!/usr/bin/env python3
"""Fetch only the nine public dependencies at their original lockfile revisions."""
from pathlib import Path
import json,os,re,subprocess,time
root=Path(__file__).resolve().parents[1]
packages=root/'lean/.lake/packages';packages.mkdir(parents=True,exist_ok=True)
lock=json.loads((root/'lean/lake-manifest.json').read_text());records=[]
env=dict(os.environ,GIT_TERMINAL_PROMPT='0')
for p in lock['packages']:
 assert p['url'].startswith('https://github.com/') and re.fullmatch('[0-9a-f]{40}',p['rev'])
 target=packages/p['name'];target.mkdir(exist_ok=True)
 if not (target/'.git').exists():
  subprocess.run(['git','init','-q',str(target)],check=True,env=env)
  subprocess.run(['git','-C',str(target),'remote','add','origin',p['url']],check=True,env=env)
  subprocess.run(['git','-C',str(target),'fetch','--depth=1','origin',p['rev']],check=True,env=env)
  subprocess.run(['git','-C',str(target),'checkout','--detach','-q','FETCH_HEAD'],check=True,env=env)
 actual=subprocess.check_output(['git','-C',str(target),'rev-parse','HEAD'],text=True).strip()
 assert actual==p['rev']
 assert not subprocess.check_output(['git','-C',str(target),'status','--porcelain'],text=True)
 records.append({'name':p['name'],'url':p['url'],'revision':actual,'tracked_worktree_clean':True})
 (root/'verification/DEPENDENCIES.json').write_text(json.dumps(records,indent=2)+'\n')
 print('PINNED',p['name'],actual,flush=True)
assert len(records)==9
