"""Independent HOT contract reader. No compiler or child processes."""
import argparse, hashlib, json, math
from pathlib import Path
import verify_neumann_periodic_interval_promoted_cold as cold
from verify_neumann_counting_reflection_diagnostic_v2 import unpack

SOURCE='4d6cd7ea7880feafe5b1161fa3ab2d1822334323'
BASE='633511137319dec3aeccb350af0e875da9f659c8'
OUT='/content/neumann-mixed-coordinate-hot-v1'
ROOT='/content/hrpoly-neumann-periodic-interval-promoted-cold-v1'
RUNNER='93209a9268436e9ba575e697b307d78ee4c9bbf4587a960c10de0475c1afdd2d'
PINS={
 'NeumannMixedCoordinateCoverageDraft.lean':'83f655a6d9c7510ee3c360894381ab6d72fb0915ba2ab1c0e1abd63c2af45d28',
 'verify_neumann_periodic_interval_promoted_cold.py':'e1bc45e8391e264c4887ff455c8486f4a0bbba770f76460e7e3dede04ca7fea7',
 'verify_cmp99_full_green_residue_cold.py':'558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c',
 'full_green_owner_exact_axiom_gate.py':'016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'}
NAMES={'mixed':{'YangMills.RG.'+n for n in ['neumannMixedCoordinateImage_bijective','neumannMixedCoordinateEquiv','neumannMixedCoordinateFamilyEquiv','neumannMixedCoordinateFamilyEquiv_apply','neumannMixedCoordinateFamily_bijective']}}
def sha(b):return hashlib.sha256(b).hexdigest()
def require(c,m):
 if not c:raise ValueError(m)
def commands(parent_hash,python):
 lean=['lake','env','lean','--root='+OUT]
 return {
 'parent_verify':[python,OUT+'/verify_neumann_periodic_interval_promoted_cold.py','--helpers',OUT,'--archive',ROOT+'-evidence.tar.gz','--sha256',parent_hash],
 'head':['git','rev-parse','HEAD'],
 'clean_before':['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json'],
 'mixed':lean+['-o',OUT+'/mixed.olean',OUT+'/NeumannMixedCoordinateCoverageDraft.lean'],
 'clean_after':['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json']}
def verify(files,parent,parent_hash,gate):
 manifest=json.loads(files['manifest.json'])
 require(set(manifest)==set(files)-{'manifest.json'},'MANIFEST_SET')
 for n,h in manifest.items():require(sha(files[n])==h,'HASH='+n)
 require(sha(files['runner.py'])==RUNNER,'RUNNER')
 for n,h in PINS.items():require(sha(files[n])==h,'PIN='+n)
 data=json.loads(files['result.json'])
 for k,v in dict(status='PASS',error=None,source=SOURCE,base=BASE,parent_sha256=parent_hash,cold_seal=False).items():require(data.get(k)==v,'RESULT='+k)
 records=data['records'];require(len(records)==5,'RECORD_COUNT')
 python=records[0]['command'][0]
 require(python in ['/usr/bin/python3','/usr/bin/python','/usr/local/bin/python3'],'PYTHON')
 cmds=commands(parent_hash,python)
 require([r['stage'] for r in records]==list(cmds),'STAGE_ORDER')
 for r in records:
  s=r['stage'];require(r['command']==cmds[s] and r.get('cwd')==ROOT,'COMMAND='+s)
  require(r['exit']==0 and r['timed_out'] is False,'EXIT='+s)
  require(math.isfinite(r['seconds']) and r['seconds']>=0,'TIME='+s)
  require(sha(files[s+'.log'])==r['sha256'],'LOG='+s)
 require(files['head.log'].decode().strip()==BASE,'HEAD')
 report_text=files['parent_verify.log'].decode()
 decoder=json.JSONDecoder();observed,end=decoder.raw_decode(report_text.lstrip())
 require(observed==parent,'PARENT_REPORT')
 require(report_text.lstrip()[end:].strip()=='NEUMANN_PERIODIC_INTERVAL_COLD_EVIDENCE_VERIFIED','PARENT_MARKER')
 audits={s:gate.exact_axioms(files[s+'.log'].decode(),ns) for s,ns in NAMES.items()}
 require(json.loads(files['audits.json'])==audits,'AUDIT_RECORD')
 expected=set(PINS)|{'runner.py','result.json','manifest.json','audits.json','mixed.olean'}|{s+'.log' for s in cmds}
 require(set(files)==expected,'FILE_SET')
 return dict(status='PASS',cold_seal=False,source=SOURCE,parent_sha256=parent_hash,audits=audits,records=records,outputs={n:sha(files[n]) for n in ['mixed.olean']})
def main():
 ap=argparse.ArgumentParser()
 for n in ['archive','parent-archive','helpers']:ap.add_argument('--'+n,type=Path,required=True)
 for n in ['sha256','parent-sha256']:ap.add_argument('--'+n,required=True)
 a=ap.parse_args()
 old=cold.helper(a.helpers,'verify_cmp99_full_green_residue_cold.py',PINS['verify_cmp99_full_green_residue_cold.py'])
 gate=cold.helper(a.helpers,'full_green_owner_exact_axiom_gate.py',PINS['full_green_owner_exact_axiom_gate.py'])
 old.PREFIX='hrpoly-'+cold.REV+'-evidence'
 parent=cold.verify(old.read_archive(a.parent_archive,a.parent_sha256),gate,old)
 parent['archive_sha256']=a.parent_sha256.lower()
 raw=a.archive.read_bytes();require(sha(raw)==a.sha256.lower(),'ARCHIVE_HASH')
 rawfiles=unpack(raw);prefix=Path(OUT).name+'/'
 require(all(n.startswith(prefix) for n in rawfiles),'PREFIX')
 files={n[len(prefix):]:v for n,v in rawfiles.items()}
 print(json.dumps(verify(files,parent,a.parent_sha256,gate),sort_keys=True,indent=2))
 print('MIXED_COORDINATE_HOT_EVIDENCE_VERIFIED')
if __name__=='__main__':main()
