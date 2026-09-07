"""Independent reader of the fixed ten-declaration HOT retry, never a seal."""
import argparse
import json
import math
from pathlib import Path
import types
from verify_neumann_counting_reflection_diagnostic_v2 import unpack, require
from verify_neumann_coordinate_precision_diagnostic import sha, NAMES as OLD_NAMES, GATE_HASH

SOURCE='249ee54287989580df0f802796937caa1e4107a0'
BASE='95c757465455c7e8cffcfcd6d9d18aa56f6d5083'
REV='neumann-coordinate-precision-hot-retry-v1'
ROOT='/content/hrpoly-neumann-coordinate-precision-diagnostic-v1'
RUNNER_HASH='14b7bee8b260d9b0a5df266d216e7c3a3d4b2849e0575dcd4657140715386cb8'
ARCHIVE_HASH='ea16de33269c65964606bfe5997fea3fbf7478a27115d3bfbde5ef0ae401a915'
PARENT_HASH='5ce85f28076e99319b122dabef5949b23ed8858fc59f654091925f3254abfe04'
PINS={'NeumannCoordinateMomentumCarryDraft.lean':'4f75ddbacfd31824b63f4ebcd83be28a8e6ecb440c855fdaad7c976a17518fc4',
      'NeumannCoordinateAveragePhaseDraft.lean':'34572ae8bb05d3a2928abd172504ee201b58616e1817ca236283e4c73333d645'}
NAMES={s:OLD_NAMES[s+'_physical'] for s in ('carry','phase')}

def verify(files, parent):
    require(sha(files['runner.py'])==RUNNER_HASH,'RUNNER')
    require(sha(files['axiom-gate.py'])==GATE_HASH,'GATE')
    d=json.loads(files['result.json'])
    for k,value in dict(status='PASS',cold_seal=False,source=SOURCE,base=BASE,revision=REV,parent_hash=PARENT_HASH,pins=PINS,gate_hash=GATE_HASH,error=None).items():
        require(d.get(k)==value,'RESULT='+k)
    require(d['names']=={s:[n.removeprefix('YangMills.RG.') for n in names] for s,names in NAMES.items()},'NAMES')
    require(json.loads(files['parent-contract.json'])==parent,'PARENT_CONTRACT')
    cmds={'head':['git','rev-parse','HEAD'],'mathlib':['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],
        'lean_version':['lean','--version'],'lake_version':['lake','--version']}
    clean=['git','diff','--exit-code','HEAD','--','YangMills','tmp/NeumannCoordinateMomentumCarryDraft.lean','tmp/NeumannCoordinateAveragePhaseDraft.lean','lean-toolchain','lake-manifest.json']
    cmds['clean_before']=clean
    for s,n in zip(('carry','phase'),PINS):
        cmds[s]=['lake','env','lean','-o','.lake/build/lib/lean/'+n.replace('.lean','.olean'),'tmp/'+REV+'/'+n]
    cmds['clean_after']=clean
    require([r['stage'] for r in d['records']]==list(cmds),'STAGES')
    allowed={'runner.py','axiom-gate.py','parent-contract.json','result.json','records.json','lean-sha256.txt','lake-sha256.txt'}
    require(json.loads(files['records.json'])==d['records'],'RECORDS')
    for r in d['records']:
        s=r['stage']; require(r['command']==cmds[s] and r['cwd']==ROOT,'COMMAND='+s)
        require(r['exit']==0 and r['timed_out'] is False,'EXIT='+s)
        require(math.isfinite(r['seconds']) and 0<=r['seconds']<125,'TIME='+s)
        require(sha(files[s+'.log'])==r['log_sha256'],'LOG='+s); allowed.add(s+'.log')
    require(files['head.log'].decode().strip()==BASE,'HEAD')
    require(files['mathlib.log'].decode().strip()=='07642720480157414db592fa85b626dafb71355b','MATHLIB')
    for exe in ('lean','lake'):
        require('4.29.0-rc6' in files[exe+'_version.log'].decode(),'VERSION')
        require(len(files[exe+'-sha256.txt'].decode().strip())==64,'EXECUTABLE_DIGEST')
    for n,digest in PINS.items(): require(sha(files[n])==digest,'SOURCE='+n); allowed.add(n)
    require(set(d['outputs'])=={n.replace('.lean','.olean') for n in PINS},'OUTPUT_SET')
    for n,digest in d['outputs'].items(): require(bool(files[n]) and sha(files[n])==digest,'OUTPUT='+n); allowed.add(n)
    gate=types.ModuleType('pinned_gate'); exec(compile(files['axiom-gate.py'],'pinned_gate','exec'),gate.__dict__)
    audits={s:gate.exact_axioms(files[s+'.log'].decode(),names) for s,names in NAMES.items()}
    require(audits==d['audits'],'AUDITS'); require(set(files)==allowed,'FILE_SET')
    return dict(status='VERIFIED_HOT_PASS',cold_seal=False,source=SOURCE,base=BASE,records=d['records'],audits=audits,outputs=d['outputs'],parent_archive_sha256=PARENT_HASH)

def main():
    p=argparse.ArgumentParser();p.add_argument('--archive',type=Path,required=True);p.add_argument('--destination',type=Path,required=True);a=p.parse_args()
    require(a.archive.stat().st_size<32*2**20,'SIZE');blob=a.archive.read_bytes();require(sha(blob)==ARCHIVE_HASH,'ARCHIVE_HASH')
    raw=unpack(blob);prefix=REV+'-evidence/';require(all(n.startswith(prefix) and '/' not in n[len(prefix):] for n in raw),'PREFIX')
    files={n[len(prefix):]:b for n,b in raw.items()}
    parent_blob=Path('validation-evidence/neumann-coordinate-precision-diagnostic-v1-fail-20260907/hrpoly-neumann-coordinate-precision-diagnostic-v1-evidence.tar.gz').read_bytes()
    require(sha(parent_blob)==PARENT_HASH,'PARENT_ARCHIVE')
    parent_files={n.rsplit('/',1)[-1]:b for n,b in unpack(parent_blob).items()}
    report=verify(files,json.loads(parent_files['coordinate-contract.json'])); report['archive_sha256']=ARCHIVE_HASH
    payload=(json.dumps(report,sort_keys=True,indent=2)+'\n').encode()
    require(not a.destination.exists(),'NO_OVERWRITE');a.destination.mkdir()
    for n,b in files.items():(a.destination/n).write_bytes(b)
    (a.destination/a.archive.name).write_bytes(blob);(a.destination/'independent-verification.json').write_bytes(payload)
    print('STATUS='+report['status']);print('REPORT_SHA256='+sha(payload));print(json.dumps(report['outputs'],sort_keys=True))

if __name__=='__main__':main()
