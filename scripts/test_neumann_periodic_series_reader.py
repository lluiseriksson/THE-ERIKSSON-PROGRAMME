import sys,json,subprocess
sys.path.insert(0,'scripts')
import verify_neumann_periodic_series_hot as v
import full_green_owner_exact_axiom_gate as gate
files={}
for n in v.PINS:
 p=('tmp/' if n.endswith('.lean') else 'scripts/')+n
 files[n]=subprocess.check_output(['git','cat-file','blob',v.SOURCE+':'+p])
files['runner.py']=subprocess.check_output(['git','cat-file','blob','89cdaaed0:scripts/colab_neumann_periodic_series_hot.py'])
cmds=v.commands('parenthash','/usr/bin/python3');records=[];audits={}
for s,c in cmds.items():
 text=''
 if s=='head':text=v.BASE+'\n'
 if s=='parent_verify':text='{}\nNEUMANN_PHYSICAL_PERIODIC_TRANSFER_COLD_EVIDENCE_VERIFIED\n'
 if s in v.NAMES:
  text='\n'.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in sorted(v.NAMES[s]))
  audits[s]=gate.exact_axioms(text,v.NAMES[s])
 files[s+'.log']=text.encode();records.append(dict(stage=s,command=c,exit=0,timed_out=False,seconds=.1,sha256=v.sha(text.encode())))
files['result.json']=json.dumps(dict(status='PASS',error=None,source=v.SOURCE,base=v.BASE,parent_sha256='parenthash',cold_seal=False,records=records)).encode()
files['audits.json']=json.dumps(audits).encode()
for n in ['series.olean','summability.olean']:files[n]=b'synthetic'
files['manifest.json']=json.dumps({n:v.sha(b) for n,b in files.items()}).encode()
v.verify(files,{},'parenthash',gate)
rejected=0
for name in ['runner.py','head.log','series.olean','audits.json']:
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
