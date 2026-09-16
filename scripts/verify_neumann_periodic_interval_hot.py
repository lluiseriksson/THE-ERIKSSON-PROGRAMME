"""Independent HOT contract reader. No compiler or child processes."""
import argparse, hashlib, json, math
from pathlib import Path
import verify_neumann_physical_periodic_series_promoted_cold as cold
from verify_neumann_counting_reflection_diagnostic_v2 import unpack

SOURCE='e7bfd29f609408eccd6f296c1f96e04425320d8c'
BASE='d16030e70abeee9eb77e28f5dc6a222ffdfd8200'
OUT='/content/neumann-periodic-interval-hot-v1'
ROOT='/content/hrpoly-neumann-physical-periodic-series-promoted-cold-v1'
RUNNER='c003e2ce10f40d3861fb96d9feeac22e39383adbeb1922ca396ba9160259841e'
PINS={
 'NeumannPeriodicIntervalCoverageDraft.lean':'9aa0a966041bdbaa720135127cf69691ded82c394705eb9a536582c398da8020',
 'verify_neumann_physical_periodic_series_promoted_cold.py':'368b8c05d346571b04dbbd11447db203f4741b1247d9f0ad191b58698f69ec1f',
 'verify_cmp99_full_green_residue_cold.py':'558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c',
 'full_green_owner_exact_axiom_gate.py':'016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'}
NAMES={s:{'YangMills.RG.'+n for n in [
 'neumannPeriodicInterval_periodQuotient','neumannPeriodicInterval_periodRemainder',
 'neumannPeriodicIntervalFamily_injective','neumannPeriodicIntervalFamily_surjective',
 'neumannPeriodicIntervalFamily_bijective','neumannIntegerPeriodicOwner']}
 for s in ['repro','interval']}
def sha(b):return hashlib.sha256(b).hexdigest()
def require(c,m):
 if not c:raise ValueError(m)
def commands(parent_hash,python):
 lean=['lake','env','lean','--root='+OUT]
 return {
 'parent_verify':[python,OUT+'/verify_neumann_physical_periodic_series_promoted_cold.py','--helpers',OUT,'--archive',ROOT+'-evidence.tar.gz','--sha256',parent_hash],
 'head':['git','rev-parse','HEAD'],
 'clean_before':['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json'],
 'repro':['lake','env','lean',OUT+'/PeriodicIntervalMathlibRepro.lean'],
 'prerequisite':['lake','build','YangMills.RG.NeumannImageIntervalCoverage'],
 'interval':lean+['-o',OUT+'/interval.olean',OUT+'/NeumannPeriodicIntervalCoverageDraft.lean'],
 'clean_after':['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json']}
def verify(files,parent,parent_hash,gate):
 manifest=json.loads(files['manifest.json'])
 require(set(manifest)==set(files)-{'manifest.json'},'MANIFEST_SET')
 for n,h in manifest.items():require(sha(files[n])==h,'HASH='+n)
 require(sha(files['runner.py'])==RUNNER,'RUNNER')
 for n,h in PINS.items():require(sha(files[n])==h,'PIN='+n)
 draft=files['NeumannPeriodicIntervalCoverageDraft.lean'].decode()
 repro=draft.replace('import YangMills.RG.NeumannImageIntervalCoverage','import Mathlib.Data.Int.DivMod\nimport Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.Ring')
 repro=repro.replace('namespace YangMills.RG\n','namespace YangMills.RG\n\ndef neumannImageIntervalPoint (m : ℤ) := {n : ℤ // 0 ≤ n ∧ n < m}\n',1)
 require(files['PeriodicIntervalMathlibRepro.lean'].decode()==repro,'REPRO_BODY')
 data=json.loads(files['result.json'])
 for k,v in dict(status='PASS',error=None,source=SOURCE,base=BASE,parent_sha256=parent_hash,cold_seal=False).items():require(data.get(k)==v,'RESULT='+k)
 records=data['records'];require(len(records)==7,'RECORD_COUNT')
 python=records[0]['command'][0]
 require(python in ['/usr/bin/python3','/usr/bin/python','/usr/local/bin/python3'],'PYTHON')
 cmds=commands(parent_hash,python)
 require([r['stage'] for r in records]==list(cmds),'STAGE_ORDER')
 for r in records:
  s=r['stage'];require(r['command']==cmds[s],'COMMAND='+s)
  require(r['exit']==0 and r['timed_out'] is False,'EXIT='+s)
  require(math.isfinite(r['seconds']) and r['seconds']>=0,'TIME='+s)
  require(sha(files[s+'.log'])==r['sha256'],'LOG='+s)
 require(files['head.log'].decode().strip()==BASE,'HEAD')
 report_text=files['parent_verify.log'].decode()
 decoder=json.JSONDecoder();observed,end=decoder.raw_decode(report_text.lstrip())
 require(observed==parent,'PARENT_REPORT')
 require(report_text.lstrip()[end:].strip()=='NEUMANN_PHYSICAL_PERIODIC_SERIES_COLD_EVIDENCE_VERIFIED','PARENT_MARKER')
 audits={s:gate.exact_axioms(files[s+'.log'].decode(),ns) for s,ns in NAMES.items()}
 require(json.loads(files['audits.json'])==audits,'AUDIT_RECORD')
 expected=set(PINS)|{'PeriodicIntervalMathlibRepro.lean','runner.py','result.json','manifest.json','audits.json','interval.olean'}|{s+'.log' for s in cmds}
 require(set(files)==expected,'FILE_SET')
 return dict(status='PASS',cold_seal=False,source=SOURCE,parent_sha256=parent_hash,audits=audits,records=records,outputs={n:sha(files[n]) for n in ['interval.olean']})
def configure_v2():
 global SOURCE,OUT,RUNNER
 SOURCE='1b222f64aa3034861a3eee17e02c56b5d452eb44'
 OUT='/content/neumann-periodic-interval-hot-v2'
 RUNNER='56ecc0d581760d527f22f56fb654e1ce47115eb79a5d2e251ec01dc31edfaa79'
 PINS['NeumannPeriodicIntervalCoverageDraft.lean']='7ae964c13ae9288525606a35837f69a1e58cf36fca792fe1b57dcb081c3b3a8a'

def main():
 ap=argparse.ArgumentParser()
 ap.add_argument('--revision',choices=['v1','v2'],default='v1')
 for n in ['archive','parent-archive','helpers']:ap.add_argument('--'+n,type=Path,required=True)
 for n in ['sha256','parent-sha256']:ap.add_argument('--'+n,required=True)
 a=ap.parse_args()
 if a.revision=='v2':configure_v2()
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
 print('PERIODIC_INTERVAL_HOT_EVIDENCE_VERIFIED')
if __name__=='__main__':main()
