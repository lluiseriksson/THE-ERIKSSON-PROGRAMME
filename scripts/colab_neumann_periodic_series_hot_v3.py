"""Bounded HOT only after independently verified cold parent; no source edits."""
import argparse, hashlib, json, os, signal, subprocess, sys, tarfile, time
from pathlib import Path
import urllib.request

SOURCE='0bdb056bad23b77adda9d6b13a4917386836e174'
BASE='24dc691e451ab9b6684f950a3fdd5a78e913997f'
ROOT=Path('/content/hrpoly-neumann-physical-periodic-transfer-promoted-cold-v1')
OUT=Path('/content/neumann-periodic-series-hot-v3')
PINS={
 'tmp/NeumannPeriodicSummabilityRepro.lean':'2f77706d8f22744ef45f765ce585cdd26027cb832f0ae9b034998ee24bbb9bca',
 'tmp/NeumannPhysicalPeriodicSeriesDraft.lean':'a20ac331d1a69ab393df813c4b66bbe5bdc177a6c645383bdef8fa7aff054e18',
 'tmp/NeumannPhysicalPeriodicSummabilityDraft.lean':'fa02f186d4730b6a40022b987e2b38bab87530a22baf21e486f3065e1dfb207b',
 'scripts/verify_neumann_physical_periodic_transfer_promoted_cold.py':'7b8855c954ec181e37e74318d7243cf940056ac5dfa5f603f5d12d0fcd03afff',
 'scripts/verify_cmp99_full_green_residue_cold.py':'558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c',
 'scripts/full_green_owner_exact_axiom_gate.py':'016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'}
def sha(b): return hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--parent-sha256',required=True)
 args=ap.parse_args();assert not OUT.exists(),'NO_REEXECUTION';OUT.mkdir()
 records=[];status='FAIL';error=None
 env=os.environ.copy()
 bins=list(Path('/content/lean-4.29.0-rc6-linux').glob('**/bin/lake'))
 assert len(bins)==1,'TOOLCHAIN_LOCATION'
 env['PATH']=str(bins[0].parent)+':'+env['PATH']
 def run(stage,cmd,limit=120):
  start=time.monotonic();timed=False
  with (OUT/(stage+'.log')).open('xb') as f:
   p=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
   print('STAGE='+stage+' PID='+str(p.pid),flush=True)
   try: code=p.wait(timeout=limit)
   except subprocess.TimeoutExpired:
    timed=True;os.killpg(p.pid,signal.SIGKILL);code=p.wait()
  b=(OUT/(stage+'.log')).read_bytes()
  records.append(dict(stage=stage,command=cmd,exit=code,timed_out=timed,seconds=time.monotonic()-start,sha256=sha(b)))
  print(b.decode(errors='replace'),flush=True)
  assert code==0 and not timed,'FIRST_ERROR='+stage
  return b.decode()
 try:
  for path,digest in PINS.items():
   b=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/'+path,timeout=60).read()
   assert sha(b)==digest,'BLOB='+path
   (OUT/Path(path).name).write_bytes(b)
  run('parent_verify',[sys.executable,str(OUT/'verify_neumann_physical_periodic_transfer_promoted_cold.py'),'--helpers',str(OUT),'--archive',str(ROOT)+'-evidence.tar.gz','--sha256',args.parent_sha256])
  assert run('head',['git','rev-parse','HEAD']).strip()==BASE
  run('clean_before',['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json'])
  sys.path.insert(0,str(OUT))
  from full_green_owner_exact_axiom_gate import exact_axioms
  run('repro',['lake','env','lean',str(OUT/'NeumannPeriodicSummabilityRepro.lean')],60)
  run('prerequisite',['lake','build','YangMills.RG.NeumannActualFullGreenReflectionSummability'],900)
  names={
   'series':['neumannPeriodicTranslate_tsum_reindex','neumannPhysicalGreen_periodicImage_tsum'],
   'summability':['neumannPeriodicSourceDifference_injective','summable_neumannPeriodicSource_of_decay','summable_neumannActualFullGreen_periodicSource']}
  audits={}
  for stage,file in [('series','NeumannPhysicalPeriodicSeriesDraft.lean'),('summability','NeumannPhysicalPeriodicSummabilityDraft.lean')]:
   text=run(stage,['lake','env','lean','--root='+str(OUT),'-o',str(OUT/(stage+'.olean')),str(OUT/file)])
   audits[stage]=exact_axioms(text,{'YangMills.RG.'+n for n in names[stage]})
  (OUT/'audits.json').write_text(json.dumps(audits,sort_keys=True)+'\n')
  run('clean_after',['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json'])
  status='PASS'
 except Exception as exc: error=repr(exc);print('ERROR='+error,flush=True)
 finally:
  (OUT/'runner.py').write_bytes(Path(__file__).read_bytes())
  (OUT/'result.json').write_text(json.dumps(dict(status=status,error=error,source=SOURCE,base=BASE,parent_sha256=args.parent_sha256,records=records,cold_seal=False),sort_keys=True)+'\n')
  files={p.name:sha(p.read_bytes()) for p in OUT.iterdir() if p.is_file()}
  (OUT/'manifest.json').write_text(json.dumps(files,sort_keys=True)+'\n')
  archive=Path(str(OUT)+'.tar.gz')
  with tarfile.open(archive,'w:gz') as t:
   for name in sorted(set(files)|{'manifest.json'}):
    t.add(OUT/name,arcname=OUT.name+'/'+name,recursive=False)
  print('FINAL_STATUS='+status+' COLD_SEAL=0',flush=True)
  print('ARCHIVE='+str(archive)+' SHA256='+sha(archive.read_bytes()),flush=True)
 return 0 if status=='PASS' else 1
if __name__=='__main__':raise SystemExit(main())
