"""Synthetic fixtures, never Lean evidence. No network or compiler."""
import ast
import copy
import json
from pathlib import Path
import subprocess
import types
import verify_neumann_coordinate_precision_diagnostic as v

def gitblob(ref,path):
    return subprocess.check_output(['git','cat-file','blob',ref+':'+path],timeout=5)
runner=gitblob('1f5443d50fbfb21d02a4f817137a3798de05ab0a','scripts/colab_neumann_coordinate_precision_diagnostic.py')
tree=ast.parse(runner)
main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
q=next(n.value for n in ast.walk(main) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Attribute) and t.attr=='QUEUE' for t in n.targets))
queue=eval(compile(ast.Expression(q),'queue','eval'),{'lib':'.lake/build/lib/lean','NAMES':{s:frozenset(ns) for s,ns in v.NAMES.items()},'PINS':v.PINS})
assert {s:c for s,c,_ in queue}==v.COMMANDS
assert [s for s,_,_ in queue]==list(v.COMMANDS)
assert {s:sorted(ns) for s,_,ns in queue if ns}==v.NAMES
f={'runner.py':runner,'durable-base.py':gitblob('ddf6fdc1882edddbf063389aab4d455a8ed30801','scripts/colab_cmp99_full_green_arbitrary_residue_cold.py'),
   'axiom-gate.py':gitblob(v.SOURCE,'scripts/full_green_owner_exact_axiom_gate.py')}
for p in v.PINS:f[Path(p).name]=gitblob(v.SOURCE,p)
outputs={n:b'SYNTHETIC NOT AN OLEAN' for n in ["NeumannCoordinateProductRepro.olean","NeumannHalfCellPhaseRepro.olean","NeumannEntireAverageHalfCellPhaseDraft.olean","NeumannCoordinateAliasReflectionDraft.olean","NeumannCoordinateMomentumCarryDraft.olean","NeumannCoordinateAveragePhaseDraft.olean"]}
f.update(outputs)
contract=dict(source=v.SOURCE,revision=v.REV,scope=v.SCOPE,cold_seal=False,pins=v.PINS,names=v.NAMES,
    queue=[[s,c,v.NAMES.get(s)] for s,c in v.COMMANDS.items()],base='ddf6fdc1882edddbf063389aab4d455a8ed30801',base_hash=v.BASE_HASH,gate_hash=v.GATE_HASH,
    outputs={n:v.sha(b) for n,b in outputs.items()})
f['coordinate-contract.json']=json.dumps(contract).encode()
f['gate-contract.json']=json.dumps(dict(source_sha=v.SOURCE,project_build_cache_restored=False,expected_axiom_names=sorted(n for ns in v.NAMES.values() for n in ns),base_runner_sha256='2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e')).encode()
f['preflight.json']=json.dumps([dict(actual_exit=e,expected_exit=e,seconds=.01) for e in (0,7)]).encode()
records=[]
for s in v.REQUIRED:
    text='synthetic'
    if s=='head':text=v.SOURCE
    if s=='mathlib_pin':text=v.MATHLIB
    if s in ('lean_version','lake_version'):text='4.29.0-rc6'
    if s in v.NAMES:text='\n'.join("'"+n+"' depends on axioms: [propext,\n Classical.choice, Quot.sound]" for n in v.NAMES[s])
    cmd=v.COMMANDS.get(s,['synthetic',s])
    if s=='checkout':cmd=['git','checkout','--detach',v.SOURCE]
    f[s+'.log']=text.encode()
    r=dict(stage=s,command=cmd,cwd=v.ROOT,exit=0,seconds=.01,timed_out=False,timeout_seconds=120 if s in v.NAMES else 3600,log_file=s+'.log',output_sha256=v.sha(f[s+'.log']))
    records.append(r);f[s+'.json']=json.dumps(r).encode()
data=dict(status='PASS',source_sha=v.SOURCE,runner_rev=v.REV,mathlib_sha=v.MATHLIB,toolchain_asset_sha256=v.ASSET,source_blobs=v.PINS,minimum_ram_gib=40.0,gpu_runtime_authorized=False,records=records)
f['evidence.json']=json.dumps(data).encode()
assert v.verify(f)['status']=='VERIFIED_DIAGNOSTIC_PASS'
rejected=0
def reject(g):
    global rejected
    try:v.verify(g)
    except (ValueError,KeyError):rejected+=1
    else:raise AssertionError('INVALID_FIXTURE_ACCEPTED')
for key,value in [('status','FAIL'),('source_sha','0'*40),('minimum_ram_gib',12.0)]:
    g=copy.deepcopy(f);d=copy.deepcopy(data);d[key]=value;g['evidence.json']=json.dumps(d).encode();reject(g)
for key,value in [('exit',7),('timed_out',True),('command',['lake','build','Wrong']),('seconds',float('nan'))]:
    g=copy.deepcopy(f);d=copy.deepcopy(data);d['records'][-2][key]=value;g['phase_physical.json']=json.dumps(d['records'][-2]).encode();g['evidence.json']=json.dumps(d).encode();reject(g)
for replacement in ('sorryAx','ofReduceBool','Unknown.axiom'):
    g=copy.deepcopy(f);d=copy.deepcopy(data);g['phase_physical.log']=g['phase_physical.log'].replace(b'Quot.sound',replacement.encode());d['records'][-2]['output_sha256']=v.sha(g['phase_physical.log']);g['phase_physical.json']=json.dumps(d['records'][-2]).encode();g['evidence.json']=json.dumps(d).encode();reject(g)
for key in ('physical_prerequisites.log','NeumannCoordinateProductRepro.olean'):
    g=copy.deepcopy(f);del g[key];reject(g)
g=copy.deepcopy(f);g['extra.log']=b'';reject(g)
g=copy.deepcopy(f);g['NeumannCoordinateProductRepro.lean']+=b'\n-- altered source\n';reject(g)
g=copy.deepcopy(f);g['NeumannCoordinateProductRepro.olean']+=b'corrupt';reject(g)
g=copy.deepcopy(f);c=copy.deepcopy(contract);c['cold_seal']=True;g['coordinate-contract.json']=json.dumps(c).encode();reject(g)
g=copy.deepcopy(f);d=copy.deepcopy(data);d['records'][12:14]=reversed(d['records'][12:14]);g['evidence.json']=json.dumps(d).encode();reject(g)
print('COORDINATE_PRECISION_DIAGNOSTIC_READER_SYNTHETIC=PASS valid=1 rejected='+str(rejected)+' PRODUCER_QUEUE_AST=PASS COMPILER_CHECKED=0')
