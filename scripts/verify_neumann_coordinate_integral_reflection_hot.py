"""Independent pinned PASS reader for integer endpoint coordinate phases HOT."""
import argparse
import json
import math
from pathlib import Path
import types
from verify_neumann_counting_reflection_diagnostic_v2 import unpack, require
from verify_neumann_coordinate_precision_diagnostic import sha, GATE_HASH
REV='neumann-coordinate-integral-reflection-hot-v1'
SOURCE='76e777daccc7282628c0187810cde8477cf0a3b0'
BASE='95c757465455c7e8cffcfcd6d9d18aa56f6d5083'
ROOT='/content/hrpoly-neumann-coordinate-precision-diagnostic-v1'
PIN='e3c0fa979a32033284f496acc925c2005851cc2b6cece7c136421fc6717d16e1'
RUNNER='0cc1ea6579244cd077ded3bec829092a153afb989a779bdf48b97d2bc38c6ec6'
ARCHIVE='f6d55616d7f6a9d6fc1ded3ae9e2483f1cf7d2209ad9b588df4b6b166d703e5b'
NAMES=['YangMills.RG.neumannIntervalCoordinateReflection_insertNth','YangMills.RG.neumannIntegral_coordinateReflection']

PARENTS={}

def verify(files):
    for n,h in [('runner.py',RUNNER),('axiom-gate.py',GATE_HASH),('NeumannCoordinateIntegralReflectionDraft.lean',PIN)]:require(sha(files[n])==h,'INPUT='+n)
    d=json.loads(files['result.json'])
    for k,v in dict(status='PASS',cold_seal=False,source=SOURCE,base=BASE,pin=PIN,gate=GATE_HASH,revision=REV,names=NAMES,error=None).items():require(d.get(k)==v,'RESULT='+k)
    cmds={'head':['git','rev-parse','HEAD'],'mathlib':['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],
        'lean_version':['lean','--version'],'lake_version':['lake','--version'],
        'prerequisites':['lake','build','YangMills.RG.IntervalIntegralPiCoordinateTransport'],
        'physical':['lake','env','lean','-o','/content/'+REV+'/NeumannCoordinateIntegralReflectionDraft.olean','tmp/'+REV+'/NeumannCoordinateIntegralReflectionDraft.lean']}
    cmds['clean_after']=['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json']
    require([r['stage'] for r in d['records']]==list(cmds),'STAGES')
    allowed={'runner.py','axiom-gate.py','result.json','NeumannCoordinateIntegralReflectionDraft.lean','NeumannCoordinateIntegralReflectionDraft.olean','lean-sha256.txt','lake-sha256.txt'}
    for r in d['records']:
        s=r['stage'];require(r['command']==cmds[s] and r['cwd']==ROOT,'COMMAND')
        require(r['exit']==0 and r['timed_out'] is False,'EXIT')
        require(math.isfinite(r['seconds']) and 0<=r['seconds']<(605 if s=='prerequisites' else 125),'TIME')
        require(r['timeout_seconds']==(600 if s=='prerequisites' else 120),'TIMEOUT')
        require(sha(files[s+'.log'])==r['log_sha256'] and json.loads(files[s+'.json'])==r,'LOG')
        allowed|={s+'.log',s+'.json'}
    require(files['head.log'].decode().strip()==BASE,'BASE')
    require(files['mathlib.log'].decode().strip()=='07642720480157414db592fa85b626dafb71355b','MATHLIB')
    for exe in ('lean','lake'):
        require('4.29.0-rc6' in files[exe+'_version.log'].decode(),'VERSION')
        require(len(files[exe+'-sha256.txt'].decode().strip())==64,'EXE_HASH')
    op='NeumannCoordinateIntegralReflectionDraft.olean';require(d['outputs']=={op:sha(files[op])} and bool(files[op]),'OUTPUT')
    gate=types.ModuleType('gate');exec(compile(files['axiom-gate.py'],'gate','exec'),gate.__dict__)
    audits=gate.exact_axioms(files['physical.log'].decode(),set(NAMES));require(audits==d['audits'],'AUDITS')
    require(json.loads(files['parents.json'])==PARENTS,'PARENTS')
    allowed.add('parents.json')
    for n,h in PARENTS.items():
        key='parent-'+n+'.bin'; require(sha(files[key])==h,'PARENT='+n); allowed.add(key)
    require(set(files)==allowed,'FILES')
    return dict(status='VERIFIED_HOT_PASS',cold_seal=False,source=SOURCE,records=d['records'],audits=audits,outputs=d['outputs'],scope='coordinate product integral reflection with explicit integrability; not physical Green, B0 or window15')

def main():
    p=argparse.ArgumentParser();p.add_argument('--archive',type=Path,required=True);p.add_argument('--destination',type=Path,required=True);a=p.parse_args()
    require(a.archive.stat().st_size<32*2**20,'SIZE');b=a.archive.read_bytes();require(sha(b)==ARCHIVE,'ARCHIVE')
    raw=unpack(b);prefix=REV+'/';require(all(n.startswith(prefix) and '/' not in n[len(prefix):] for n in raw),'PREFIX')
    files={n[len(prefix):]:v for n,v in raw.items()};r=verify(files);r['archive_sha256']=ARCHIVE
    payload=(json.dumps(r,sort_keys=True,indent=2)+'\n').encode();require(not a.destination.exists(),'NO_OVERWRITE');a.destination.mkdir()
    for n,v in files.items():(a.destination/n).write_bytes(v)
    (a.destination/a.archive.name).write_bytes(b);(a.destination/'independent-verification.json').write_bytes(payload)
    print('STATUS='+r['status']);print('REPORT_SHA256='+sha(payload));print(json.dumps(r['outputs']));print(json.dumps(r['records'][-1]))

if __name__=='__main__':main()
