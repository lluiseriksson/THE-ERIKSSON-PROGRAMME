"""F4 uniform-amplitude diagnostic with cheap import-path and scalar repros.

Fresh source, diagnostic only. Temporary .oleans use Lake's compiled output
tree, never a source-root LEAN_PATH override. Stop at the first real error;
retain runtime only for evidence preservation and bounded follow-up debug.
"""
from __future__ import annotations
import copy
import hashlib
import json
import types
import urllib.request

ENGINE_COMMIT = '950ff77bcf022d6da2a0809543f1ecc652e6cc44'
ENGINE_PATH = 'scripts/colab_cmp85_full_green_hybrid_repro_v2.py'
ENGINE_HASH = '525c1e58f5961b81daa96075ab11fffc1e20269db525808c6b786463a6b8e81a'
SOURCE = 'be4e73409ac444d23e95c2eae2584fece5882f98'
REV = 'cmp85-uniform-full-green-diagnostic-v3'
ROOT = '/content/hrpoly-' + REV
BLOBS = {
    'tmp/FullGreenUniformPowerRepro.lean':
        '691e47eb11ebbf83b2a59f8bcb95152b4863ebb44a219879609efa6e7fd793cc',
    'tmp/FullGreenNormalizedBudgetRepro.lean':
        'b709e6376b505d55846acd6d255a56db06d2a817b40f671dac296a0c568a1f4f',
    'tmp/SourceFullGreenHybridAmplitudeDraft.lean':
        '3df28cff61bfd539dacac6e8e3ee18f175f3535f9d93bf12f59f06a6532b3882',
    'tmp/SourceFullGreenUniformAmplitudeDraft.lean':
        'c2819af6de7b6803f8ad375c92946441a491aa162a4177ff8ec9de32e69fed97',
}

PATH_REPRO = r'''import hashlib,json,os,subprocess,time
from pathlib import Path
root=Path('tmp/import-path-repro').resolve()
assert not root.exists(), 'REPRO_ALREADY_EXISTS'
source=root/'source'; built=root/'built'
(source/'Probe').mkdir(parents=True); (built/'Probe').mkdir(parents=True)
(source/'Probe/Leaf.lean').write_text('theorem importPathProbe : (1 : Nat) = 1 := rfl\n')
(source/'Main.lean').write_text('import Probe.Leaf\nexample : (1 : Nat) = 1 := importPathProbe\n')
records=[]
def child(name,command,env,expected):
 start=time.perf_counter()
 p=subprocess.run(command,cwd=source,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 record=dict(stage=name,exit=p.returncode,expected=expected,seconds=time.perf_counter()-start,
             command=command,output=p.stdout.decode(),sha256=hashlib.sha256(p.stdout).hexdigest())
 records.append(record); print(json.dumps(record,sort_keys=True),flush=True)
 assert p.returncode==expected, 'PATH_REPRO_EXIT='+name
 return p.stdout.decode()
env=os.environ.copy()
child('compile_leaf',['lean','-o',str(built/'Probe/Leaf.olean'),'Probe/Leaf.lean'],env,0)
assert (built/'Probe/Leaf.olean').is_file()
bad=child('source_first_expected_failure',['lean','Main.lean'],dict(env,LEAN_PATH=str(source)+os.pathsep+str(built)),1)
assert 'object file' in bad and 'does not exist' in bad
child('compiled_first_expected_pass',['lean','Main.lean'],dict(env,LEAN_PATH=str(built)+os.pathsep+str(source)),0)
print('IMPORT_PATH_REPRO=PASS synthetic_only=1 cases=3',flush=True)
'''

def compile_tmp(name):
    return ['lake', 'env', 'lean', '-o', '.lake/build/lib/lean/tmp/' + name + '.olean',
            'tmp/' + name + '.lean']

COMMANDS = {
    'import_path_repro': ['python3', '-c', PATH_REPRO],
    'mathlib_only_repro': ['lake', 'env', 'lean', 'tmp/FullGreenUniformPowerRepro.lean'],
    'prepare_tmp_outputs': ['python3', '-c',
        "from pathlib import Path; Path('.lake/build/lib/lean/tmp').mkdir(parents=True,exist_ok=True)"],
    'normalization_import': compile_tmp('FullGreenNormalizedBudgetRepro'),
    'materialize_sealed_imports': ['lake', 'build',
        'YangMills.RG.BalabanCMP85SourceFullGreenScalarFoundations',
        'YangMills.RG.BalabanCMP99PhysicalFullGreenOwnerResidueBound',
        'YangMills.RG.BalabanCMP99GeneratedFullPointSourceOwnerBound'],
    'hybrid_draft': compile_tmp('SourceFullGreenHybridAmplitudeDraft'),
    'uniform_draft': compile_tmp('SourceFullGreenUniformAmplitudeDraft'),
    'compiled_outputs': ['python3', '-c',
        "import hashlib,json; from pathlib import Path; "
        "names=['FullGreenNormalizedBudgetRepro','SourceFullGreenHybridAmplitudeDraft',"
        "'SourceFullGreenUniformAmplitudeDraft']; "
        "print(json.dumps({n:hashlib.sha256(Path('.lake/build/lib/lean/tmp/'+n+'.olean').read_bytes()).hexdigest() "
        "for n in names},sort_keys=True))"],
}
NAMES = {
    'mathlib_only_repro': {'fullGreenUniformPowerRepro'},
    'normalization_import': {'FullGreenNormalizedBudgetRepro.split',
        'FullGreenNormalizedBudgetRepro.retain_inverse_square'},
    'hybrid_draft': {'YangMills.RG.cmp85SourceFullGreen_fullBudget_le_hybrid_draft'},
    'uniform_draft': {'YangMills.RG.' + name for name in (
        'cmp85SourceFullGreenContourFactorDraft_pos',
        'cmp85SourceFullGreenHybridAmplitudeConstantDraft_nonneg',
        'cmp85SourceFullGreen_ownerAmplitude_split_draft',
        'cmp85SourceFullGreen_ownerAmplitude_inverse_square_draft',
        'exists_cmp85SourceFullGreen_uniformOwnerAmplitude_draft')},
}


def load_engine():
    url = ('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
           + ENGINE_COMMIT + '/' + ENGINE_PATH)
    with urllib.request.urlopen(url, timeout=60) as r:
        blob = r.read()
    if hashlib.sha256(blob).hexdigest() != ENGINE_HASH:
        raise RuntimeError('ENGINE_HASH_MISMATCH')
    h = types.ModuleType('uniform_durable_engine')
    exec(compile(blob, url, 'exec'), h.__dict__)
    h.SOURCE, h.REV, h.ROOT = SOURCE, REV, ROOT
    h.BLOBS, h.COMMANDS, h.NAMES = BLOBS, COMMANDS, NAMES
    h.REQUIRED = h.REQUIRED[:-3] + list(COMMANDS)
    h.CONTRACT.update(source_sha=SOURCE, runner_rev=REV, queue=COMMANDS,
        audit_expected={s: sorted(n) for s, n in NAMES.items()},
        import_path_policy='default Lake search path; tmp .oleans in .lake/build/lib/lean/tmp',
        engine_commit=ENGINE_COMMIT, engine_sha256=ENGINE_HASH)
    h.self_test = lambda gate: self_test(h, gate)
    return h


def self_test(h, gate):
    """Exercise exact durable gate with wrapping, bad hashes/exits and axioms."""
    gate.self_test()
    files = {'hybrid-contract.json': json.dumps(h.CONTRACT).encode(),
        'gate-contract.json': json.dumps(dict(source_sha=SOURCE,
            project_build_cache_restored=False, expected_axiom_names=sorted(set.union(*NAMES.values())),
            base_runner_sha256='2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e')).encode(),
        'preflight.json': json.dumps([dict(expected_exit=c, actual_exit=c, seconds=.01) for c in (0,7)]).encode()}
    records = []
    for s in h.REQUIRED:
        text='synthetic only'; command=COMMANDS.get(s,['synthetic'])
        if s=='head': text=SOURCE
        if s=='mathlib_pin': text=h.MATHLIB
        if s in ('lean_version','lake_version'): text='4.29.0-rc6'
        if s=='checkout': command=['git','checkout','--detach',SOURCE]
        if s in NAMES:
            text='\n'.join("'"+n+"' depends on axioms: [propext,\n Classical.choice, Quot.sound]" for n in sorted(NAMES[s]))
        files[s+'.log']=text.encode()
        record=dict(stage=s,exit=0,seconds=.01,log_file=s+'.log',output_sha256=h.sha(text.encode()),command=command,cwd=ROOT)
        records.append(record); files[s+'.json']=json.dumps(record).encode()
    data=dict(source_sha=SOURCE,runner_rev=REV,status='PASS',source_blobs=BLOBS,
        mathlib_sha=h.MATHLIB,toolchain_asset_sha256=h.ASSET,minimum_ram_gib=40.0,
        gpu_runtime_authorized=False,records=records)
    files['evidence.json']=json.dumps(data).encode()
    h.verify(files,gate)
    bads=[]
    for key,value in [('status','FAIL'),('source_sha','wrong')]:
        bad=dict(files); d=copy.deepcopy(data); d[key]=value
        bad['evidence.json']=json.dumps(d).encode(); bads.append(bad)
    bad=dict(files); bad['head.log']+=b'corrupt'; bads.append(bad)
    bad=dict(files); del bad['mathlib_only_repro.log']; bads.append(bad)
    for word in ('sorryAx','ofReduceBool','Other.axiom'):
        bad=dict(files); d=copy.deepcopy(data); s='uniform_draft'
        bad[s+'.log']=bad[s+'.log'].replace(b'Quot.sound',word.encode())
        r=next(r for r in d['records'] if r['stage']==s)
        r['output_sha256']=h.sha(bad[s+'.log'])
        bad[s+'.json']=json.dumps(r).encode()
        bad['evidence.json']=json.dumps(d).encode(); bads.append(bad)
    for bad in bads:
        try: h.verify(bad,gate)
        except (ValueError,KeyError,RuntimeError): continue
        raise RuntimeError('NEGATIVE_FIXTURE_ACCEPTED')
    print('UNIFORM_VERIFIER_SELF_TEST=PASS synthetic=1 rejected='+str(len(bads)),flush=True)


if __name__ == '__main__':
    raise SystemExit(load_engine().main())
