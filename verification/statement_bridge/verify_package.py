#!/usr/bin/env python3
"""Read-only artifact/source/log integrity check. Does not execute Lean."""
from pathlib import Path
import hashlib,json,re
package=Path(__file__).resolve().parent;public_root=package.parents[1]
def require(c,m):
 if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(rel):return json.loads((package/rel).read_text())
inventory=read('PACKAGE_MANIFEST.json')
actual={}
for p in package.rglob('*'):
 rel=p.relative_to(package)
 if '__pycache__' in rel.parts:continue
 require(not p.is_symlink(),f'Unexpected symlink: {rel}')
 if p.is_file() and str(rel)!='PACKAGE_MANIFEST.json':actual[rel.as_posix()]={'bytes':p.stat().st_size,'sha256':sha(p)}
require(actual==inventory['files'],'Package inventory/bytes/hash mismatch')
manifest=read('verification/SOURCE_MANIFEST.json');inputs=manifest['input_sha256']
require(len(inputs)==manifest['input_file_count']==72,'Unexpected input count')
for rel,digest in inputs.items():
 p=package/rel if (package/rel).is_file() else public_root/rel
 require(p.is_file() and not p.is_symlink() and sha(p)==digest,f'Frozen input mismatch: {rel}')
original=read('verification/ORIGINAL_SOURCE_MANIFEST.json')
require(len(original['lean_modules'])==66,'Original closure count')
for row in original['lean_modules']:require(inputs[row['path']]==row['sha256'],'Changed original proof')
for rel,digest in read('verification/VERIFICATION_CODE_MANIFEST.json')['sha256'].items():require(sha(package/rel)==digest,'Changed verification code')
receipt=read('verification/BUILD_RECEIPT.json')
require(receipt['status']=='PASS','No complete passing execution receipt')
require(receipt['source_manifest_sha256']==sha(package/'verification/SOURCE_MANIFEST.json'),'Receipt/source mismatch')
require(receipt['initial_local_project_olean_count']==0 and receipt['final_local_project_olean_count']==68,'Local object boundary')
require(receipt['fresh_local_modules_built']==68 and receipt['geometric_proof_modules_unchanged']==66,'Module counts')
require(receipt['local_source_trust_level']==0 and receipt['fresh_kernel_safe_declaration_closure_replay']=='PASS','Trust/replay boundary')
require(receipt['prior_pass_receipts_reused'] is False,'Old receipt reuse')
commands=receipt['commands'];require([r['label'] for r in commands]==['cache','build','fresh-kernel','axioms'],'Command sequence')
normalized=read('verification/LOG_NORMALIZATION.json')['logs']
for row in commands:
 require(row['exit_code']==0,'Unsuccessful command')
 item=normalized[row['log']]
 require(item['raw_sha256']==row['log_sha256'],'Raw log/receipt hash mismatch')
 require(item['published_sha256']==sha(package/row['log']),'Published log hash mismatch')
expected=['Erdos488.Geometry.SeparatedDistances.FixedDimension.pass5_fixed_dimension_erdos_670']+['Erdos670Bridge.'+n for n in ['hasSeparatedDistances_image','finite_counterexample','not_fixedDimensionStatement','erdos_670_negated']]
axes=receipt['endpoint_transitive_axioms'];require(set(axes)==set(expected),'Endpoint set')
require(all(v==['propext','Classical.choice','Quot.sound'] for v in axes.values()),'Nonstandard axioms')
log=(package/'verification/axioms.log').read_text()
parsed={n:[a.strip() for a in names.split(',') if a.strip()] for n,names in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)}
require(parsed==axes,'Axiom output/receipt mismatch')
require('replaying Erdos670Bridge.Bridge with --fresh' in (package/'verification/fresh-kernel.log').read_text(),'Fresh log target')
print(f'PASS: {len(actual)} package files; 72 frozen inputs, unchanged original 66-module proof, new build/fresh-replay/axiom receipt and log hashes.')
print('This is an offline integrity check, not a new Lean execution or independent certification.')
