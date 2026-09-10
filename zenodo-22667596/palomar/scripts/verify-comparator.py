#!/usr/bin/env python3
"""Build pinned trusted tools and run Comparator WITH NanoDa, retaining logs.

Requires installed Lean/lake, Cargo, Go, Git, and network access. It intentionally
fails when prerequisites are missing. This script is not a service submission.
No project source or publication metadata is rewritten by a successful run.
"""
from __future__ import annotations
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parents[1];ROOT=P
from verify import static_checks, input_hashes as source_hashes

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=P/'.verification/comparator');parser.add_argument('--cached-tools',action='store_true',help='Use clean locally cached checkouts at exactly the recorded tool revisions')
 parser.add_argument('--tools-dir',type=Path,default=P/'.verification/tools',help='Cache for the pinned verification tools')
 a=parser.parse_args();out=a.out.resolve();out.mkdir(parents=True,exist_ok=True)
 result={'comparator_passed':False,'nanoda_passed':False,'registered':False,
         'all_orders_theorem_formalized':False,'scope':'39 pursuit/structural root selections plus 24 supplementary game regression statements (not a second submission)'}
 def finish(code,reason):
  result.update(exit_code=code,reason=reason)
  (out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));return code
 missing=[x for x in ('lake','git','cargo','go') if not shutil.which(x)]
 if missing:return finish(127,'Missing required executables: '+', '.join(missing))
 pins=json.loads((P/'tool-pins.json').read_text());result['pins']=pins
 cache=a.tools_dir.resolve();cache.mkdir(parents=True,exist_ok=True)
 bindir=cache/'bin';bindir.mkdir(exist_ok=True);counter=0
 def run(cmd,cwd,env=None):
  nonlocal counter
  counter+=1
  r=subprocess.run([str(x) for x in cmd],cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  (out/f'{counter:02d}.log').write_text('$ '+' '.join(map(str,cmd))+'\n'+r.stdout)
  if r.returncode:raise RuntimeError(f'Exit {r.returncode}; see {counter:02d}.log')
  return r.stdout
 def checkout(repo,key):
  d=cache/key
  if not d.exists():run(['git','clone','--filter=blob:none','--no-checkout','https://github.com/'+repo+'.git',d],ROOT)
  assert (d/'.git').is_dir(),'Tool cache is not a git checkout'
  origin=run(['git','remote','get-url','origin'],d).strip()
  assert origin=='https://github.com/'+repo+'.git','Unexpected tool-cache origin'
  if not a.cached_tools:
   run(['git','fetch','--depth','1','origin',pins[key]],d)
   run(['git','checkout','--detach',pins[key]],d)
  else:
   run(['git','diff','--exit-code','HEAD'],d)
  assert run(['git','rev-parse','HEAD'],d).strip()==pins[key]
  return d
 try:
  static_checks()
  result['input_hashes']=source_hashes()
  ver=run(['lake','env','lean','--version'],P)
  if 'version 4.32.0 ' not in ver and 'version 4.32.0,' not in ver:raise RuntimeError('Expected Lean 4.32.0')
  exporter=checkout('leanprover/lean4export','lean4export')
  assert (exporter/'lean-toolchain').read_text().strip()==(P/'lean-toolchain').read_text().strip()
  comparator=checkout('leanprover/comparator','comparator');nanoda=checkout('robsimmons/nanoda_lib','nanoda')
  env=os.environ.copy();env['GOBIN']=str(bindir)
  if a.cached_tools:
   info=run(['go','version','-m',bindir/'landrun'],ROOT)
   assert pins['landrun'][:12] in info,'Landrun cached binary revision mismatch'
  else:
   run(['go','install','github.com/zouuup/landrun/cmd/landrun@'+pins['landrun']],ROOT,env)
  run(['lake','build','comparator'],comparator)
  run(['lake','build','lean4export'],exporter)
  run(['cargo','build','--release','--locked'],nanoda)
  env.update(PALOMAR_LANDRUN_BIN=str(bindir/'landrun'),
             COMPARATOR_LEAN4EXPORT=str(exporter/'.lake/build/bin/lean4export'),
             COMPARATOR_NANODA=str(nanoda/'target/release/nanoda_bin'),
             COMPARATOR_LANDRUN=str(P/'scripts/landrun-wrapper.py'))
  result['configurations']=[]
  for label,relative in [('unified','comparator.json'),('game','verification/game-comparator.json')]:
   cfg=json.loads((P/relative).read_text());cfg['enable_nanoda']=True
   protected=out/(label+'-protected.json');protected.write_text(json.dumps(cfg,indent=2)+'\n')
   run(['lake','env',comparator/'.lake/build/bin/comparator',protected],P,env)
   result['configurations'].append({'config':relative,'selected_declarations':len(cfg['theorem_names']),
     'comparator_passed':True,'nanoda_passed':True,'sha256':hashlib.sha256(protected.read_bytes()).hexdigest()})
  assert result['input_hashes']==source_hashes(),'Proof inputs changed during independent verification'
  result.update(comparator_passed=True,nanoda_passed=True,all_orders_theorem_formalized=True)
  return finish(0,'Pinned Comparator completed successfully with NanoDa required and configured; inspect retained logs.')
 except (AssertionError,RuntimeError,OSError) as e:return finish(1,str(e))
if __name__=='__main__':sys.exit(main())
