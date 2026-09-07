"""Independent pinned PASS reader for literal full Green integrand HOT."""
import argparse
import json
import math
from pathlib import Path
import types
from verify_neumann_counting_reflection_diagnostic_v2 import unpack, require
from verify_neumann_coordinate_precision_diagnostic import sha, GATE_HASH
REV='neumann-physical-half-cell-hot-v2'
SOURCE='91dee187ebd5f32250c3966ed6a9141b25990ad7'
BASE='95c757465455c7e8cffcfcd6d9d18aa56f6d5083'
ROOT='/content/hrpoly-neumann-coordinate-precision-diagnostic-v1'
PIN='e9e61b864d93af288c96f50e58968471c10adbe0da76e3f092b2be15ff02029b'
RUNNER='3b66229b91d81967e062bcff980457d9b9a397298d42ce37fade6ead75f6a381'
ARCHIVE='8debebc3f16a117320c73c576451b5337994cf14ad0adca7d0db2dc4104e3883'
NAMES=['YangMills.RG.neumannBlockBoundaryReflection_eq_center_shift','YangMills.RG.neumannPhysicalGreen_blockBoundaryReflection_massUniform','YangMills.RG.neumannPhysicalGreen_lowerHalfCellReflection_massUniform']

PARENTS={
    "NeumannCoordinateProductRepro.olean": "4741a866c6b292fe9455853c1e0ce2eb6a65dc93b2e535d9d2ba73ba585ae72d",
    "NeumannHalfCellPhaseRepro.olean": "dc7a88c613978aa2120ca07bf330cadb51ed7d11738c91f200ec11b1ab842482",
    "NeumannEntireAverageHalfCellPhaseDraft.olean": "be24be4bc25693d70280afce4b31ff4f8ae6bb9411cf09fdca7e47ac6a324744",
    "NeumannCoordinateAliasReflectionDraft.olean": "ef02028360f190459616eb8ecbef56a70e53c11e0cdd14f9ce55bc193ea41be2",
    "NeumannCoordinateMomentumCarryDraft.olean": "8e9d176f4a642aeeae7e286dd693d394aa4165be349f840eecab115edd86f383",
    "NeumannCoordinateAveragePhaseDraft.olean": "f3439e2babe80464003ddfc014dad9b09c085e81efcebf3db0094b2b14c6ca45",
    "NeumannDiagonalTransportRepro.olean": "82718ecc7622064cb47e9f683fa4014c65361ea8d53c2495199216195cca32fc",
    "NeumannActualCoordinateSolutionDraft.olean":"8e4eb8490780cd16ccd70f690253b019922a32611232b089e34e0c836556c1df",
    "NeumannCoordinateEndpointPhaseDraft.olean":"4471ab587680400d9b76d0af102964dbf4dcbea8fb826e6f81e2cbe50091e1fe",
    "NeumannActualCoordinateGreenIntegrandDraft.olean":"9453389cc222d26ecc09f3cf183e5c332f08e6ce46b12ce96fea55c1f2558943",
    "NeumannPhysicalCoordinateReflectionDomainDraft.olean":"5bd5ad40d17784a1ca026f13b8f1ad2603abbb6e69ed8613d0421011ac431a68",
    "NeumannCoordinateIntegralReflectionDraft.olean":"dc35365e956b13c2186e8898f0776353ba609f1635e07c945e85a71b58c1dc27",
    "NeumannPhysicalCoordinateGreenIntegralDraft.olean":"399c7d7448888587940cb468f29f58566d5ff7837c06c9762c206e35303ecf8d",
    "NeumannActualCommonBlockTranslationDraft.olean":"61693a2806612bb7390a8b163467bf206ee75841776242c064fd71dddeb7198c",
    "NeumannActualFullSolutionScalarDraft.olean":"d4925a06a399d27ca2892a75bbcd577da756b42d0f520608c1eef2f77cc77a63",
    "NeumannCommonBlockEndpointPhaseDraft.olean":"36ffc5c08adf7a5e610f26b2e6b0886ae1d8f2d634bde7ad7046fede04920f0e"
}

def verify(files):
    for n,h in [('runner.py',RUNNER),('axiom-gate.py',GATE_HASH),('NeumannPhysicalHalfCellReflectionDraft.lean',PIN)]:require(sha(files[n])==h,'INPUT='+n)
    d=json.loads(files['result.json'])
    for k,v in dict(status='PASS',cold_seal=False,source=SOURCE,base=BASE,pin=PIN,gate=GATE_HASH,revision=REV,names=NAMES,error=None).items():require(d.get(k)==v,'RESULT='+k)
    cmds={'head':['git','rev-parse','HEAD'],'mathlib':['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],
        'lean_version':['lean','--version'],'lake_version':['lake','--version'],
        'prerequisites':['lake','build','YangMills.RG.BalabanCMP89Eq246MassUniformPhysicalContour','YangMills.RG.BalabanCMP89CenteredTorusGreenCoefficientPhase'],
        'physical':['lake','env','lean','-o','/content/'+REV+'/NeumannPhysicalHalfCellReflectionDraft.olean','tmp/'+REV+'/NeumannPhysicalHalfCellReflectionDraft.lean']}
    cmds['clean_after']=['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json']
    require([r['stage'] for r in d['records']]==list(cmds),'STAGES')
    allowed={'runner.py','axiom-gate.py','result.json','NeumannPhysicalHalfCellReflectionDraft.lean','NeumannPhysicalHalfCellReflectionDraft.olean','lean-sha256.txt','lake-sha256.txt'}
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
    op='NeumannPhysicalHalfCellReflectionDraft.olean';require(d['outputs']=={op:sha(files[op])} and bool(files[op]),'OUTPUT')
    gate=types.ModuleType('gate');exec(compile(files['axiom-gate.py'],'gate','exec'),gate.__dict__)
    audits=gate.exact_axioms(files['physical.log'].decode(),set(NAMES));require(audits==d['audits'],'AUDITS')
    require(json.loads(files['parents.json'])==PARENTS,'PARENTS')
    allowed.add('parents.json')
    for n,h in PARENTS.items():
        key='parent-'+n+'.bin'; require(sha(files[key])==h,'PARENT='+n); allowed.add(key)
    require(sha(files['translation-evidence.tar.gz'])=='adc3c4a22bbfc97277f56b113cb510ee10f19361b72e33f646234da18439d3d0','TRANSLATION_ARCHIVE')
    allowed.add('translation-evidence.tar.gz')
    require(set(files)==allowed,'FILES')
    return dict(status='VERIFIED_HOT_PASS',cold_seal=False,source=SOURCE,records=d['records'],audits=audits,outputs=d['outputs'],scope='literal normalized Green reflection at integer block boundaries and lower half-cell; no regional equation, B0 or window15')

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






