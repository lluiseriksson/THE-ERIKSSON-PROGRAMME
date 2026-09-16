"""Independent pinned PASS reader for integer endpoint coordinate phases HOT."""
import argparse
import json
import math
from pathlib import Path
import types
from verify_neumann_counting_reflection_diagnostic_v2 import unpack, require
from verify_neumann_coordinate_precision_diagnostic import sha, GATE_HASH
REV='neumann-coordinate-endpoint-phase-hot-v1'
SOURCE='1421eb6a8d619f41b598f79f01957b2dfd11a277'
BASE='95c757465455c7e8cffcfcd6d9d18aa56f6d5083'
ROOT='/content/hrpoly-neumann-coordinate-precision-diagnostic-v1'
PIN='b434a91d6e9b8a7a037ab61d1974f4bb1b400ef1ecb4a923ed127dec4b7fd6f9'
RUNNER='33f8961d643b7362adf8fa6124a4e20b4e615f39145c1eaadb71aa12eaa39b45'
ARCHIVE='63fc5a2fe1d33e321d5fbb3d99a410c50d3aad272e8d5d28505af69457dfb0f4'
NAMES=['YangMills.RG.neumannFineEndpointCoordinateReflection_involutive','YangMills.RG.neumannCoordinateEndpointPhase_identity','YangMills.RG.neumannAliasTargetPhase_coordinateReflection','YangMills.RG.neumannAliasSourcePhase_coordinateReflection']

PARENTS={
    "NeumannCoordinateProductRepro.olean": "4741a866c6b292fe9455853c1e0ce2eb6a65dc93b2e535d9d2ba73ba585ae72d",
    "NeumannHalfCellPhaseRepro.olean": "dc7a88c613978aa2120ca07bf330cadb51ed7d11738c91f200ec11b1ab842482",
    "NeumannEntireAverageHalfCellPhaseDraft.olean": "be24be4bc25693d70280afce4b31ff4f8ae6bb9411cf09fdca7e47ac6a324744",
    "NeumannCoordinateAliasReflectionDraft.olean": "ef02028360f190459616eb8ecbef56a70e53c11e0cdd14f9ce55bc193ea41be2",
    "NeumannCoordinateMomentumCarryDraft.olean": "8e9d176f4a642aeeae7e286dd693d394aa4165be349f840eecab115edd86f383",
    "NeumannCoordinateAveragePhaseDraft.olean": "f3439e2babe80464003ddfc014dad9b09c085e81efcebf3db0094b2b14c6ca45",
    "NeumannDiagonalTransportRepro.olean": "82718ecc7622064cb47e9f683fa4014c65361ea8d53c2495199216195cca32fc"
}

def verify(files):
    for n,h in [('runner.py',RUNNER),('axiom-gate.py',GATE_HASH),('NeumannCoordinateEndpointPhaseDraft.lean',PIN)]:require(sha(files[n])==h,'INPUT='+n)
    d=json.loads(files['result.json'])
    for k,v in dict(status='PASS',cold_seal=False,source=SOURCE,base=BASE,pin=PIN,gate=GATE_HASH,revision=REV,names=NAMES,error=None).items():require(d.get(k)==v,'RESULT='+k)
    cmds={'head':['git','rev-parse','HEAD'],'mathlib':['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],
        'lean_version':['lean','--version'],'lake_version':['lake','--version'],
        'prerequisites':['lake','build','YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointAliasPhase'],
        'physical':['lake','env','lean','-o','/content/'+REV+'/NeumannCoordinateEndpointPhaseDraft.olean','tmp/'+REV+'/NeumannCoordinateEndpointPhaseDraft.lean']}
    cmds['clean_after']=['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json']
    require([r['stage'] for r in d['records']]==list(cmds),'STAGES')
    allowed={'runner.py','axiom-gate.py','result.json','NeumannCoordinateEndpointPhaseDraft.lean','NeumannCoordinateEndpointPhaseDraft.olean','lean-sha256.txt','lake-sha256.txt'}
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
    op='NeumannCoordinateEndpointPhaseDraft.olean';require(d['outputs']=={op:sha(files[op])} and bool(files[op]),'OUTPUT')
    gate=types.ModuleType('gate');exec(compile(files['axiom-gate.py'],'gate','exec'),gate.__dict__)
    audits=gate.exact_axioms(files['physical.log'].decode(),set(NAMES));require(audits==d['audits'],'AUDITS')
    require(json.loads(files['parents.json'])==PARENTS,'PARENTS')
    allowed.add('parents.json')
    for n,h in PARENTS.items():
        key='parent-'+n+'.bin'; require(sha(files[key])==h,'PARENT='+n); allowed.add(key)
    require(set(files)==allowed,'FILES')
    return dict(status='VERIFIED_HOT_PASS',cold_seal=False,source=SOURCE,records=d['records'],audits=audits,outputs=d['outputs'],scope='integer endpoint target/source phases with full alias period; not Green reflection, B0 or window15')

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
