#!/usr/bin/env python3
"""Offline source/config integrity and local import closure checks; not a Lean run."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:raise ValueError(message)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def strip_comments(text):
    # Lean nested block comments and line comments; preserve newlines.
    out=[];i=0;depth=0
    while i<len(text):
        if text[i:i+2]=='/-':depth+=1;i+=2;continue
        if depth and text[i:i+2]=='-/':depth-=1;i+=2;continue
        if not depth and text[i:i+2]=='--':
            while i<len(text) and text[i]!='\n':i+=1
            continue
        if not depth:out.append(text[i])
        elif text[i]=='\n':out.append('\n')
        i+=1
    require(depth==0,'Unclosed Lean comment')
    return ''.join(out)

def main():
    manifest=json.loads((ROOT/'SOURCE_MANIFEST.json').read_text())
    for project,record in manifest.items():
        modules=record['sources'];require(len(modules)==record['module_count'],'Module count differs')
        graph={}
        for module,row in modules.items():
            rel=Path(row['path']);require(not rel.is_absolute() and '..' not in rel.parts,'Unsafe path')
            require(rel==Path(*module.split('.')).with_suffix('.lean'),'Noncanonical module path')
            p=ROOT/project/rel;b=p.read_bytes()
            require(digest(p)==row['sha256'],f'Source changed: {project}/{rel}')
            require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob'],'Blob mismatch')
            code=strip_comments(b.decode())
            require(not re.search(r'\b(sorry|admit|axiom|unsafe)\b',code),f'Forbidden token: {p}')
            imports=[]
            for line in code.splitlines():
                if line.startswith('import '):imports.extend(line[7:].split())
            local=[x for x in imports if not x.startswith(('Mathlib.','Lean.','Std.','Batteries.')) and x not in ('Mathlib','Lean','Std','Batteries')]
            require(all(x in modules for x in local),f'Missing import: {module} {local}')
            graph[module]=local
        todo=[record['target']];seen=set()
        while todo:
            m=todo.pop()
            if m not in seen:seen.add(m);todo.extend(graph[m])
        require(seen==set(modules),f'Nonminimal import closure: {project}')
    files=json.loads((ROOT/'PACKAGE_MANIFEST.json').read_text())['files'];actual={}
    for p in ROOT.rglob('*'):
        rel=p.relative_to(ROOT)
        if any(x in ('.lake','__pycache__','.git') for x in rel.parts):continue
        require(not p.is_symlink(),f'Unexpected symlink: {rel}')
        if not p.is_file() or str(rel)=='PACKAGE_MANIFEST.json':continue
        actual[str(rel)]={'sha256':digest(p),'bytes':p.stat().st_size}
    require(actual==files,'Package inventory differs')
    print('PASS: exact 60-module R29 and 80-module epsilon closures; package integrity; no proof placeholders. Lean execution is separate.')
if __name__=='__main__':main()
