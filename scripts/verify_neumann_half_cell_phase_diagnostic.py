"""Independent PASS reader for phase diagnostic; no network or compiler."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import types
from verify_neumann_counting_reflection_diagnostic_v2 import unpack, require

SOURCE = '7320d1bab92f0bcb18d8072dd0d2fa13b1aea204'
REV = 'neumann-half-cell-phase-diagnostic-v1'
ROOT = '/content/hrpoly-' + REV
RUNNER_HASH = 'ecd76d0c05609aa45a4dc1c69e33ae9fa0dfb8600283760464c8d547697a42b8'
BASE_HASH = '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
MATHLIB = '07642720480157414db592fa85b626dafb71355b'
ASSET = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'
PINS = {
    'tmp/NeumannHalfCellPhaseRepro.lean': 'ce9ecdf21529aab7bc4e479a6ff147be1f9d713dccee635589b92e0d594ee7dd',
    'tmp/NeumannEntireAverageHalfCellPhaseDraft.lean': 'b7f5c7a3173455ff5681f24fc1657b37657d3c341ea89c9fb7c7f628133c92be',
}
NAMES = {'phase_repro': ['NeumannHalfCellPhaseRepro.finite_exp_reverse'],
    'phase_physical': ['YangMills.RG.neumannEntireAverageFactor_halfCellPhase']}
LIB = '.lake/build/lib/lean/'
COMMANDS = {
    'scratch_import_path': ['python3', '-c', "from pathlib import Path; Path('.lake/build/lib/lean').mkdir(parents=True, exist_ok=True)"],
    'phase_repro': ['lake', 'env', 'lean', '-o', LIB+'NeumannHalfCellPhaseRepro.olean', 'tmp/NeumannHalfCellPhaseRepro.lean'],
    'phase_prerequisites': ['lake','build','YangMills.RG.BalabanCMP89Eq251EntireAverageAmplitude'],
    'phase_physical': ['lake', 'env', 'lean', '-o', LIB+'NeumannEntireAverageHalfCellPhaseDraft.olean', 'tmp/NeumannEntireAverageHalfCellPhaseDraft.lean'],
    'clean_after': ['git','diff','--exit-code','HEAD','--','YangMills',*PINS,'lean-toolchain','lake-manifest.json'],
}
REQUIRED = ['download_toolchain','extract_toolchain','lean_version','lake_version','clone','checkout','head','overlay_text_guard','import_prefix_guard','lake_update','mathlib_pin','cache_get',*COMMANDS]
SCOPE = 'finite reverse-sum and actual entire-average phase only; not Green covariance, regional inverse, B0 or window15'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def verify(files):
    for name,digest in [('runner.py',RUNNER_HASH),('durable-base.py',BASE_HASH),('axiom-gate.py',GATE_HASH)]:
        require(sha(files[name]) == digest, 'TRANSPORT='+name)
    gate = types.ModuleType('verified_axiom_gate')
    exec(compile(files['axiom-gate.py'],'verified_axiom_gate','exec'),gate.__dict__)
    data = json.loads(files['evidence.json'])
    for k,v in dict(status='PASS', source_sha=SOURCE, runner_rev=REV,
        mathlib_sha=MATHLIB, toolchain_asset_sha256=ASSET, source_blobs=PINS,
        minimum_ram_gib=40.0, gpu_runtime_authorized=False).items():
        require(data.get(k)==v, 'EVIDENCE='+k)
    c=json.loads(files['phase-contract.json'])
    expected=dict(source=SOURCE, revision=REV,scope=SCOPE,cold_seal=False,pins=PINS,names=NAMES,
        queue=[[s,cmd,NAMES.get(s)] for s,cmd in COMMANDS.items()],
        base='ddf6fdc1882edddbf063389aab4d455a8ed30801',base_hash=BASE_HASH,gate_hash=GATE_HASH)
    require(set(c)==set(expected)|{'outputs'},'CONTRACT_FIELDS')
    for k,v in expected.items():
        require(c[k]==v,'CONTRACT='+k)
    g=json.loads(files['gate-contract.json'])
    require(g['source_sha']==SOURCE and g['project_build_cache_restored'] is False
        and g['expected_axiom_names']==sorted(n for ns in NAMES.values() for n in ns)
        and g['base_runner_sha256']=='2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e','BASE_CONTRACT')
    pre=json.loads(files['preflight.json'])
    require(len(pre)==2,'PREFLIGHT_COUNT')
    for r,e in zip(pre,(0,7)):
        require(r['actual_exit']==r['expected_exit']==e and math.isfinite(r['seconds']) and r['seconds']>=0,'PREFLIGHT')
    records=data['records']; stages=[r['stage'] for r in records]
    require(len(stages)==len(set(stages)),'DUPLICATE_STAGE')
    require([s for s in stages if s in REQUIRED]==REQUIRED,'STAGE_ORDER')
    require(set(stages)<=set(REQUIRED)|{'apt_update','install_zstd'},'EXTRA_STAGE')
    expected_files={'runner.py','durable-base.py','axiom-gate.py','evidence.json','phase-contract.json','gate-contract.json','preflight.json'}
    idx={}
    for r in records:
        s=r['stage'];idx[s]=r
        require(r['exit']==0 and r['timed_out'] is False,'EXIT='+s)
        require(r['timeout_seconds']==(120 if s in NAMES else 3600),'TIMEOUT='+s)
        require(math.isfinite(r['seconds']) and r['seconds']>=0,'TIMER='+s)
        require(r['log_file']==s+'.log' and sha(files[s+'.log'])==r['output_sha256'],'LOG='+s)
        require(json.loads(files[s+'.json'])==r,'RECORD='+s)
        expected_files|={s+'.log',s+'.json'}
    for s,cmd in COMMANDS.items():
        require(idx[s]['command']==cmd and idx[s]['cwd']==ROOT,'COMMAND='+s)
    require(idx['checkout']['command']==['git','checkout','--detach',SOURCE],'CHECKOUT')
    require(files['head.log'].decode().strip()==SOURCE,'HEAD')
    require(files['mathlib_pin.log'].decode().strip()==MATHLIB,'MATHLIB')
    for s in ('lean_version','lake_version'):
        require('4.29.0-rc6' in files[s+'.log'].decode(),'VERSION='+s)
    for path,digest in PINS.items():
        n=Path(path).name;require(sha(files[n])==digest,'INPUT='+n);expected_files.add(n)
    outputs=c['outputs']
    require(set(outputs)=={'NeumannHalfCellPhaseRepro.olean','NeumannEntireAverageHalfCellPhaseDraft.olean'},'OUTPUT_SET')
    for n,digest in outputs.items():
        require(bool(files[n]) and sha(files[n])==digest,'OUTPUT='+n);expected_files.add(n)
    require(set(files)==expected_files,'FILE_SET')
    audits={s:gate.exact_axioms(files[s+'.log'].decode(),names) for s,names in NAMES.items()}
    return dict(status='VERIFIED_DIAGNOSTIC_PASS',cold_seal=False,source=SOURCE,scope=SCOPE,
        records=records,audits=audits,outputs=outputs)

def main():
    p=argparse.ArgumentParser();p.add_argument('--archive',type=Path,required=True)
    p.add_argument('--sha256',required=True);p.add_argument('--destination',type=Path)
    a=p.parse_args();require(a.archive.stat().st_size<32*2**20,'SIZE')
    blob=a.archive.read_bytes();require(sha(blob)==a.sha256.lower(),'ARCHIVE_HASH')
    raw=unpack(blob);prefix='hrpoly-'+REV+'-evidence/'
    require(all(n.startswith(prefix) and '/' not in n[len(prefix):] for n in raw),'PREFIX')
    files={n[len(prefix):]:b for n,b in raw.items()};report=verify(files)
    report['archive_sha256']=sha(blob);payload=(json.dumps(report,sort_keys=True,indent=2)+'\n').encode()
    if a.destination:
        require(not a.destination.exists(),'NO_OVERWRITE');a.destination.mkdir()
        (a.destination/a.archive.name).write_bytes(blob)
        for n,b in files.items():(a.destination/n).write_bytes(b)
        (a.destination/'independent-verification.json').write_bytes(payload)
    print(payload.decode());print('REPORT_SHA256='+sha(payload))

if __name__=='__main__':main()
