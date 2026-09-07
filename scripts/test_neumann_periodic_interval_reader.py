import sys,json,subprocess
sys.path.insert(0,'scripts')
import verify_neumann_periodic_interval_hot as v
import full_green_owner_exact_axiom_gate as gate
if '--v2' in sys.argv:v.configure_v2()
files={}
for n in v.PINS:
 p=('tmp/' if n.endswith('.lean') else 'scripts/')+n
 files[n]=subprocess.check_output(['git','cat-file','blob',v.SOURCE+':'+p])
runner='4d3f72c5a2d26843cf8b5d86639be597f6a7b744:scripts/colab_neumann_periodic_interval_hot.py'
if '--v2' in sys.argv:runner='a0c37f556e0a92e3ec94a436344cc024ac62f53a:scripts/colab_neumann_periodic_interval_hot_v2.py'
files['runner.py']=subprocess.check_output(['git','cat-file','blob',runner])
draft=files['NeumannPeriodicIntervalCoverageDraft.lean'].decode()
repro=draft.replace('import YangMills.RG.NeumannImageIntervalCoverage','import Mathlib.Data.Int.DivMod\nimport Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.Ring')
repro=repro.replace('namespace YangMills.RG\n','namespace YangMills.RG\n\ndef neumannImageIntervalPoint (m : ℤ) := {n : ℤ // 0 ≤ n ∧ n < m}\n',1)
files['PeriodicIntervalMathlibRepro.lean']=repro.encode()
cmds=v.commands('parenthash','/usr/bin/python3');records=[];audits={}
for s,c in cmds.items():
 text=''
 if s=='head':text=v.BASE+'\n'
 if s=='parent_verify':text='{}\nNEUMANN_PHYSICAL_PERIODIC_SERIES_COLD_EVIDENCE_VERIFIED\n'
 if s in v.NAMES:
  text='\n'.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in sorted(v.NAMES[s]))
  audits[s]=gate.exact_axioms(text,v.NAMES[s])
 files[s+'.log']=text.encode();records.append(dict(stage=s,command=c,exit=0,timed_out=False,seconds=.1,sha256=v.sha(text.encode())))
files['result.json']=json.dumps(dict(status='PASS',error=None,source=v.SOURCE,base=v.BASE,parent_sha256='parenthash',cold_seal=False,records=records)).encode()
files['audits.json']=json.dumps(audits).encode()
for n in ['interval.olean']:files[n]=b'synthetic'
files['manifest.json']=json.dumps({n:v.sha(b) for n,b in files.items()}).encode()
v.verify(files,{},'parenthash',gate)
rejected=0
for name in ['runner.py','head.log','interval.olean','audits.json']:
 bad=dict(files);bad[name]+=b'corrupt'
 try:v.verify(bad,{},'parenthash',gate)
 except Exception:rejected+=1
 else:raise AssertionError(name)
print('READER_SYNTHETIC_PASS positive=1 rejected='+str(rejected))

for field,value in [('status','FAIL'),('source','wrong')]:
 bad=dict(files);data=json.loads(bad['result.json']);data[field]=value
 bad['result.json']=json.dumps(data).encode()
 bad['manifest.json']=json.dumps({n:v.sha(b) for n,b in bad.items() if n!='manifest.json'}).encode()
 try:v.verify(bad,{},'parenthash',gate)
 except Exception:rejected+=1
 else:raise AssertionError(field)
print('SEMANTIC_REJECTIONS_PASS total='+str(rejected))
bad=dict(files);bad['__pycache__/unexpected.pyc']=b'extra'
try:v.verify(bad,{},'parenthash',gate)
except Exception:rejected+=1
else:raise AssertionError('unmanifested bytecode')
bad['manifest.json']=json.dumps({n:v.sha(b) for n,b in bad.items() if n!='manifest.json'}).encode()
try:v.verify(bad,{},'parenthash',gate)
except Exception:rejected+=1
else:raise AssertionError('manifested unexpected bytecode')
print('ARCHIVE_SET_REJECTIONS_PASS total='+str(rejected))


for label in ['cold_upgrade','wrong_repro','forbidden_axiom']:
 bad=dict(files)
 data=json.loads(bad['result.json'])
 if label=='cold_upgrade':
  data['cold_seal']=True
 elif label=='wrong_repro':
  bad['PeriodicIntervalMathlibRepro.lean']+=b'\n-- changed'
 else:
  bad['interval.log']=bad['interval.log'].replace(b'Quot.sound',b'sorryAx')
  for r in data['records']:
   if r['stage']=='interval':r['sha256']=v.sha(bad['interval.log'])
 bad['result.json']=json.dumps(data).encode()
 bad['manifest.json']=json.dumps({n:v.sha(b) for n,b in bad.items() if n!='manifest.json'}).encode()
 try:v.verify(bad,{},'parenthash',gate)
 except Exception:rejected+=1
 else:raise AssertionError(label)
print('PERIODIC_INTERVAL_READER_SELF_TEST_PASS synthetic=1 rejected='+str(rejected))
