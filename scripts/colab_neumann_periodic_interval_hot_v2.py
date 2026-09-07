"""Bounded M1/M2 HOT diagnostic after verified cold series parent. Never a cold seal."""
import argparse, hashlib, json, os, signal, subprocess, sys, tarfile, time
from pathlib import Path
import urllib.request

SOURCE='1b222f64aa3034861a3eee17e02c56b5d452eb44'
BASE='d16030e70abeee9eb77e28f5dc6a222ffdfd8200'
ROOT=Path('/content/hrpoly-neumann-physical-periodic-series-promoted-cold-v1')
OUT=Path('/content/neumann-periodic-interval-hot-v2')
PINS={
 'tmp/NeumannPeriodicIntervalCoverageDraft.lean':'7ae964c13ae9288525606a35837f69a1e58cf36fca792fe1b57dcb081c3b3a8a',
 'scripts/verify_neumann_physical_periodic_series_promoted_cold.py':'368b8c05d346571b04dbbd11447db203f4741b1247d9f0ad191b58698f69ec1f',
 'scripts/verify_cmp99_full_green_residue_cold.py':'558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c',
 'scripts/full_green_owner_exact_axiom_gate.py':'016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'}
NAMES={
 'neumannPeriodicInterval_periodQuotient','neumannPeriodicInterval_periodRemainder',
 'neumannPeriodicIntervalFamily_injective','neumannPeriodicIntervalFamily_surjective',
 'neumannPeriodicIntervalFamily_bijective','neumannIntegerPeriodicOwner'}

def sha(b): return hashlib.sha256(b).hexdigest()

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--parent-sha256',required=True)
 args=ap.parse_args();assert not OUT.exists(),'NO_REEXECUTION';OUT.mkdir()
 records=[];status='FAIL';error=None
 env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
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
  run('parent_verify',[sys.executable,str(OUT/'verify_neumann_physical_periodic_series_promoted_cold.py'),'--helpers',str(OUT),'--archive',str(ROOT)+'-evidence.tar.gz','--sha256',args.parent_sha256])
  assert run('head',['git','rev-parse','HEAD']).strip()==BASE
  run('clean_before',['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json'])
  sys.path.insert(0,str(OUT));sys.dont_write_bytecode=True
  from full_green_owner_exact_axiom_gate import exact_axioms
  draft=(OUT/'NeumannPeriodicIntervalCoverageDraft.lean').read_text()
  imported='import YangMills.RG.NeumannImageIntervalCoverage'
  namespace='namespace YangMills.RG\n'
  assert draft.count(imported)==1 and draft.count(namespace)==1,'REPRO_TRANSFORM'
  repro=draft.replace(imported,'import Mathlib.Data.Int.DivMod\nimport Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.Ring')
  repro=repro.replace(namespace,namespace+'\ndef neumannImageIntervalPoint (m : ℤ) := {n : ℤ // 0 ≤ n ∧ n < m}\n',1)
  (OUT/'PeriodicIntervalMathlibRepro.lean').write_text(repro)
  expected={'YangMills.RG.'+n for n in NAMES}
  audits={}
  audits['repro']=exact_axioms(run('repro',['lake','env','lean',str(OUT/'PeriodicIntervalMathlibRepro.lean')],60),expected)
  run('prerequisite',['lake','build','YangMills.RG.NeumannImageIntervalCoverage'],900)
  audits['interval']=exact_axioms(run('interval',['lake','env','lean','--root='+str(OUT),'-o',str(OUT/'interval.olean'),str(OUT/'NeumannPeriodicIntervalCoverageDraft.lean')]),expected)
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


