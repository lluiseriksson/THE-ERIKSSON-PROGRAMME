"""Independent pinned PASS reader for literal full Green integrand HOT."""
import argparse
import json
import math
from pathlib import Path
import types
from verify_neumann_counting_reflection_diagnostic_v2 import unpack, require
from verify_neumann_coordinate_precision_diagnostic import sha, GATE_HASH
REV='neumann-actual-coordinate-integrand-hot-v1'
SOURCE='a1b305c8071cdf06db72b67604db36bf964b51a7'
BASE='95c757465455c7e8cffcfcd6d9d18aa56f6d5083'
ROOT='/content/hrpoly-neumann-coordinate-precision-diagnostic-v1'
PIN='afc23e63378eb311516300eb73438d5dc3855b4297c3e86a8de89af446aeb0d5'
RUNNER='c9f4b18be4b4b2e2d1d48baef4bb376e5a6d4090b40b097bb5b2c759e75b1885'
ARCHIVE='f574c0d1532511bfe441c5ac5140fe41e6d064c5de0ac7e5d899d8f9423f77a7'
NAMES=['YangMills.RG.neumannActualPointSource_coordinateTransport','YangMills.RG.neumannActualPointSolution_coordinateReflection','YangMills.RG.neumannActualFineGreenIntegrand_coordinateReflection']

PARENTS={
    "NeumannCoordinateProductRepro.olean": "4741a866c6b292fe9455853c1e0ce2eb6a65dc93b2e535d9d2ba73ba585ae72d",
    "NeumannHalfCellPhaseRepro.olean": "dc7a88c613978aa2120ca07bf330cadb51ed7d11738c91f200ec11b1ab842482",
    "NeumannEntireAverageHalfCellPhaseDraft.olean": "be24be4bc25693d70280afce4b31ff4f8ae6bb9411cf09fdca7e47ac6a324744",
    "NeumannCoordinateAliasReflectionDraft.olean": "ef02028360f190459616eb8ecbef56a70e53c11e0cdd14f9ce55bc193ea41be2",
    "NeumannCoordinateMomentumCarryDraft.olean": "8e9d176f4a642aeeae7e286dd693d394aa4165be349f840eecab115edd86f383",
    "NeumannCoordinateAveragePhaseDraft.olean": "f3439e2babe80464003ddfc014dad9b09c085e81efcebf3db0094b2b14c6ca45",
    "NeumannDiagonalTransportRepro.olean": "82718ecc7622064cb47e9f683fa4014c65361ea8d53c2495199216195cca32fc",
    "NeumannActualCoordinateSolutionDraft.olean":"8e4eb8490780cd16ccd70f690253b019922a32611232b089e34e0c836556c1df",
    "NeumannCoordinateEndpointPhaseDraft.olean":"4471ab587680400d9b76d0af102964dbf4dcbea8fb826e6f81e2cbe50091e1fe"
}

def verify(files):
    for n,h in [('runner.py',RUNNER),('axiom-gate.py',GATE_HASH),('NeumannActualCoordinateGreenIntegrandDraft.lean',PIN)]:require(sha(files[n])==h,'INPUT='+n)
    d=json.loads(files['result.json'])
    for k,v in dict(status='PASS',cold_seal=False,source=SOURCE,base=BASE,pin=PIN,gate=GATE_HASH,revision=REV,names=NAMES,error=None).items():require(d.get(k)==v,'RESULT='+k)
    cmds={'head':['git','rev-parse','HEAD'],'mathlib':['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],
        'lean_version':['lean','--version'],'lake_version':['lake','--version'],
        'prerequisites':['lake','build','YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointAliasPhase'],
        'physical':['lake','env','lean','-o','/content/'+REV+'/NeumannActualCoordinateGreenIntegrandDraft.olean','tmp/'+REV+'/NeumannActualCoordinateGreenIntegrandDraft.lean']}
    cmds['clean_after']=['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json']
    require([r['stage'] for r in d['records']]==list(cmds),'STAGES')
    allowed={'runner.py','axiom-gate.py','result.json','NeumannActualCoordinateGreenIntegrandDraft.lean','NeumannActualCoordinateGreenIntegrandDraft.olean','lean-sha256.txt','lake-sha256.txt'}
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
    op='NeumannActualCoordinateGreenIntegrandDraft.olean';require(d['outputs']=={op:sha(files[op])} and bool(files[op]),'OUTPUT')
    gate=types.ModuleType('gate');exec(compile(files['axiom-gate.py'],'gate','exec'),gate.__dict__)
    audits=gate.exact_axioms(files['physical.log'].decode(),set(NAMES));require(audits==d['audits'],'AUDITS')
    require(json.loads(files['parents.json'])==PARENTS,'PARENTS')
    allowed.add('parents.json')
    for n,h in PARENTS.items():
        key='parent-'+n+'.bin'; require(sha(files[key])==h,'PARENT='+n); allowed.add(key)
    require(set(files)==allowed,'FILES')
    return dict(status='VERIFIED_HOT_PASS',cold_seal=False,source=SOURCE,records=d['records'],audits=audits,outputs=d['outputs'],scope='literal full point-source Green integrand reflection under domain gates; not integrated Green, B0 or window15')

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
