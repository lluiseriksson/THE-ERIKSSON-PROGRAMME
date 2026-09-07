"""R4 integer endpoint phase HOT diagnostic; no Green identity or cold claim."""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import tarfile
import time
import types
import urllib.request

SOURCE='1421eb6a8d619f41b598f79f01957b2dfd11a277'
BASE='95c757465455c7e8cffcfcd6d9d18aa56f6d5083'
PIN='b434a91d6e9b8a7a037ab61d1974f4bb1b400ef1ecb4a923ed127dec4b7fd6f9'
GATE='016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
REV='neumann-coordinate-endpoint-phase-hot-v1'
ROOT=Path('/content/hrpoly-neumann-coordinate-precision-diagnostic-v1')
OUT=Path('/content/'+REV)
RAW='https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
NAMES=['YangMills.RG.neumannFineEndpointCoordinateReflection_involutive','YangMills.RG.neumannCoordinateEndpointPhase_identity','YangMills.RG.neumannAliasTargetPhase_coordinateReflection','YangMills.RG.neumannAliasSourcePhase_coordinateReflection']
def sha(b):return hashlib.sha256(b).hexdigest()

def main():
    assert not OUT.exists(),'NO_REEXECUTION'; OUT.mkdir()
    scratch=ROOT/'tmp'/REV; scratch.mkdir(exist_ok=False)
    records=[]; status='FAIL'; error=None; audits={}
    env=os.environ.copy(); bins=list(Path('/content/lean-4.29.0-rc6-linux').glob('**/bin/lake'))
    assert len(bins)==1,'TOOLCHAIN'; env['PATH']=str(bins[0].parent)+':'+env['PATH']
    def run(stage,cmd):
        start=time.perf_counter(); timed=False; limit=600 if stage=='prerequisites' else 120
        with (OUT/(stage+'.log')).open('xb') as f:
            p=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            print('STAGE='+stage+' PID='+str(p.pid),flush=True)
            try:code=p.wait(timeout=limit)
            except subprocess.TimeoutExpired:timed=True;os.killpg(p.pid,signal.SIGKILL);code=p.wait()
        b=(OUT/(stage+'.log')).read_bytes(); r=dict(stage=stage,command=cmd,cwd=str(ROOT),exit=code,seconds=time.perf_counter()-start,timed_out=timed,timeout_seconds=limit,log_sha256=sha(b));records.append(r)
        (OUT/(stage+'.json')).write_text(json.dumps(r,sort_keys=True)+'\n')
        print(b.decode(errors='replace'),flush=True)
        assert code==0 and not timed,'FIRST_ERROR='+stage
        return b.decode()
    try:
        parents={
            'NeumannCoordinateProductRepro.olean':'4741a866c6b292fe9455853c1e0ce2eb6a65dc93b2e535d9d2ba73ba585ae72d',
            'NeumannHalfCellPhaseRepro.olean':'dc7a88c613978aa2120ca07bf330cadb51ed7d11738c91f200ec11b1ab842482',
            'NeumannEntireAverageHalfCellPhaseDraft.olean':'be24be4bc25693d70280afce4b31ff4f8ae6bb9411cf09fdca7e47ac6a324744',
            'NeumannCoordinateAliasReflectionDraft.olean':'ef02028360f190459616eb8ecbef56a70e53c11e0cdd14f9ce55bc193ea41be2',
            'NeumannCoordinateMomentumCarryDraft.olean':'8e9d176f4a642aeeae7e286dd693d394aa4165be349f840eecab115edd86f383',
            'NeumannCoordinateAveragePhaseDraft.olean':'f3439e2babe80464003ddfc014dad9b09c085e81efcebf3db0094b2b14c6ca45',
            'NeumannDiagonalTransportRepro.olean':'82718ecc7622064cb47e9f683fa4014c65361ea8d53c2495199216195cca32fc'}
        lib=ROOT/'.lake/build/lib/lean'
        for n,h in parents.items():
            p=Path('/content/neumann-diagonal-transport-repro-v2')/n if n=='NeumannDiagonalTransportRepro.olean' else lib/n
            b=p.read_bytes(); assert sha(b)==h,'PARENT_OUTPUT='+n
            (OUT/('parent-'+n+'.bin')).write_bytes(b)
            if n=='NeumannDiagonalTransportRepro.olean':
                assert not (lib/n).exists() or sha((lib/n).read_bytes())==h
                (lib/n).write_bytes(b)
        (OUT/'parents.json').write_text(json.dumps(parents,sort_keys=True)+'\n')
        assert run('head',['git','rev-parse','HEAD']).strip()==BASE
        assert run('mathlib',['git','-C','.lake/packages/mathlib','rev-parse','HEAD']).strip()=='07642720480157414db592fa85b626dafb71355b'
        for exe in ('lean','lake'):
            assert '4.29.0-rc6' in run(exe+'_version',[exe,'--version'])
            (OUT/(exe+'-sha256.txt')).write_text(sha((bins[0].parent/exe).read_bytes())+'\n')
        for name,path,digest in [('NeumannCoordinateEndpointPhaseDraft.lean','tmp/NeumannCoordinateEndpointPhaseDraft.lean',PIN),('axiom-gate.py','scripts/full_green_owner_exact_axiom_gate.py',GATE)]:
            b=urllib.request.urlopen(RAW+SOURCE+'/'+path,timeout=60).read();assert sha(b)==digest,'SOURCE='+path;(OUT/name).write_bytes(b)
        gate=types.ModuleType('gate');exec(compile((OUT/'axiom-gate.py').read_bytes(),'gate','exec'),gate.__dict__);gate.self_test()
        source=scratch/'NeumannCoordinateEndpointPhaseDraft.lean'
        source.write_bytes((OUT/source.name).read_bytes())
        run('prerequisites',['lake','build','YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointAliasPhase'])
        text=run('physical',['lake','env','lean','-o',str(OUT/'NeumannCoordinateEndpointPhaseDraft.olean'),str(source.relative_to(ROOT))])
        audits=gate.exact_axioms(text,set(NAMES))
        run('clean_after',['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json'])
        status='PASS'
    except Exception as e:error=repr(e);print('ERROR='+error,flush=True)
    finally:
        (OUT/'runner.py').write_bytes(Path(__file__).read_bytes())
        outputs={p.name:sha(p.read_bytes()) for p in OUT.glob('*.olean')}
        (OUT/'result.json').write_text(json.dumps(dict(status=status,cold_seal=False,source=SOURCE,base=BASE,pin=PIN,gate=GATE,revision=REV,records=records,names=NAMES,audits=audits,outputs=outputs,error=error),sort_keys=True)+'\n')
        archive=Path(str(OUT)+'.tar.gz')
        with tarfile.open(archive,'w:gz') as t:t.add(OUT,arcname=OUT.name)
        print('FINAL_STATUS='+status+' COLD_SEAL=0\nARCHIVE_SHA256='+sha(archive.read_bytes()),flush=True)
    return 0 if status=='PASS' else 1

if __name__=='__main__':raise SystemExit(main())
