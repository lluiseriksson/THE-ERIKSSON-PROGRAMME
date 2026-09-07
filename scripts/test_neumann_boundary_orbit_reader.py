from pathlib import Path
import types,json,subprocess,copy
v=types.ModuleType('reader')
exec(compile(Path('scripts/verify_neumann_boundary_orbit_hot.py').read_bytes(),'reader','exec'),v.__dict__)
g=types.ModuleType('gate')
gb=subprocess.check_output(['git','cat-file','blob',v.BASE+':scripts/full_green_owner_exact_axiom_gate.py'])
assert v.sha(gb)=='016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
exec(compile(gb,'gate','exec'),g.__dict__)
files={'runner.py':subprocess.check_output(['git','cat-file','blob','5d36ed1cb:scripts/colab_neumann_boundary_orbit_hot.py']),
'NeumannBoundaryOrbitPermutationRepro.lean':subprocess.check_output(['git','cat-file','blob',v.SOURCE+':tmp/NeumannBoundaryOrbitPermutationRepro.lean']),
'parent-review.json':b'{"synthetic":true}','orbit.olean':b'synthetic only'}
records=[]
for stage,cmd in v.COMMANDS.items():
 text='synthetic'
 if stage=='head':text=v.BASE
 if stage=='mathlib':text='07642720480157414db592fa85b626dafb71355b'
 if stage.endswith('_version'):text='4.29.0-rc6'
 if stage=='orbit':text='\n'.join("'"+n+"' depends on axioms: [propext,\n Classical.choice, Quot.sound]" for n in sorted(v.NAMES))
 files[stage+'.log']=text.encode()
 r=dict(stage=stage,command=cmd,cwd=v.ROOT,exit=0,seconds=.01,timed_out=False,timeout_seconds=120,log_sha256=v.sha(text.encode()))
 records.append(r);files[stage+'.json']=json.dumps(r).encode()
data=dict(status='PASS',error=None,source=v.SOURCE,base=v.BASE,pin=v.PIN,revision=v.REV,cold_seal=False,names=sorted(v.NAMES),parent_archive_sha256='a'*64,records=records,audits=g.exact_axioms(files['orbit.log'].decode(),v.NAMES),outputs={'orbit.olean':v.sha(files['orbit.olean'])})
files['result.json']=json.dumps(data).encode()
v.verify(files,{'synthetic':True},'a'*64,g)
bad=[]
f=dict(files);f['orbit.olean']+=b'bad';bad.append(f)
f=dict(files);f['parent-review.json']=b'{}';bad.append(f)
f=dict(files);d=copy.deepcopy(data);d['records'][-2]['exit']=1;f['result.json']=json.dumps(d).encode();f['orbit.json']=json.dumps(d['records'][-2]).encode();bad.append(f)
f=dict(files);d=copy.deepcopy(data);d['source']='wrong';f['result.json']=json.dumps(d).encode();bad.append(f)
f=dict(files);del f['clean_after.log'];bad.append(f)
f=dict(files);d=copy.deepcopy(data);f['orbit.log']=f['orbit.log'].replace(b'Quot.sound',b'sorryAx');d['records'][-2]['log_sha256']=v.sha(f['orbit.log']);f['orbit.json']=json.dumps(d['records'][-2]).encode();f['result.json']=json.dumps(d).encode();bad.append(f)
for f in bad:
 try:v.verify(f,{'synthetic':True},'a'*64,g)
 except (ValueError,RuntimeError,KeyError):continue
 raise AssertionError('CORRUPTION_ACCEPTED')
print('BOUNDARY_READER_SYNTHETIC=PASS valid=1 rejected='+str(len(bad))+' COMPILER_CHECKED=0')

