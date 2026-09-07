"""R5 physical domain HOT retry; explicit scale arguments, no cold claim."""
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

SOURCE='6b1cc23e10dcdefacdbcf8d8f59493a1dd16bda3'
BASE='95c757465455c7e8cffcfcd6d9d18aa56f6d5083'
PIN='8bd17718342e66ecdb819361c591785c61dd6414363593d494ccd0a31f28db1d'
GATE='016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
REV='neumann-physical-green-integral-hot-v1'
ROOT=Path('/content/hrpoly-neumann-coordinate-precision-diagnostic-v1')
OUT=Path('/content/'+REV)
RAW='https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
NAMES=['YangMills.RG.neumannBrillouinMomentum_coordinateReflection','YangMills.RG.neumannPhysicalGreen_coordinateReflection_massUniform']
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
            'NeumannDiagonalTransportRepro.olean':'82718ecc7622064cb47e9f683fa4014c65361ea8d53c2495199216195cca32fc',
            'NeumannActualCoordinateSolutionDraft.olean':'8e4eb8490780cd16ccd70f690253b019922a32611232b089e34e0c836556c1df',
            'NeumannCoordinateEndpointPhaseDraft.olean':'4471ab587680400d9b76d0af102964dbf4dcbea8fb826e6f81e2cbe50091e1fe',
            'NeumannActualCoordinateGreenIntegrandDraft.olean':'9453389cc222d26ecc09f3cf183e5c332f08e6ce46b12ce96fea55c1f2558943',
            'NeumannPhysicalCoordinateReflectionDomainDraft.olean':'5bd5ad40d17784a1ca026f13b8f1ad2603abbb6e69ed8613d0421011ac431a68',
            'NeumannCoordinateIntegralReflectionDraft.olean':'dc35365e956b13c2186e8898f0776353ba609f1635e07c945e85a71b58c1dc27'}
        lib=ROOT/'.lake/build/lib/lean'
        for n,h in parents.items():
            origins={'NeumannDiagonalTransportRepro.olean':'neumann-diagonal-transport-repro-v2','NeumannActualCoordinateSolutionDraft.olean':'neumann-actual-coordinate-solution-hot-v1','NeumannCoordinateEndpointPhaseDraft.olean':'neumann-coordinate-endpoint-phase-hot-v1','NeumannActualCoordinateGreenIntegrandDraft.olean':'neumann-actual-coordinate-integrand-hot-v1','NeumannPhysicalCoordinateReflectionDomainDraft.olean':'neumann-physical-coordinate-domain-hot-v2','NeumannCoordinateIntegralReflectionDraft.olean':'neumann-coordinate-integral-reflection-hot-v1'}
            p=Path('/content')/origins[n]/n if n in origins else lib/n
            b=p.read_bytes(); assert sha(b)==h,'PARENT_OUTPUT='+n
            (OUT/('parent-'+n+'.bin')).write_bytes(b)
            if n in origins:
                assert not (lib/n).exists() or sha((lib/n).read_bytes())==h
                (lib/n).write_bytes(b)
        (OUT/'parents.json').write_text(json.dumps(parents,sort_keys=True)+'\n')
        assert run('head',['git','rev-parse','HEAD']).strip()==BASE
        assert run('mathlib',['git','-C','.lake/packages/mathlib','rev-parse','HEAD']).strip()=='07642720480157414db592fa85b626dafb71355b'
        for exe in ('lean','lake'):
            assert '4.29.0-rc6' in run(exe+'_version',[exe,'--version'])
            (OUT/(exe+'-sha256.txt')).write_text(sha((bins[0].parent/exe).read_bytes())+'\n')
        for name,path,digest in [('NeumannPhysicalCoordinateGreenIntegralDraft.lean','tmp/NeumannPhysicalCoordinateGreenIntegralDraft.lean',PIN),('axiom-gate.py','scripts/full_green_owner_exact_axiom_gate.py',GATE)]:
            b=urllib.request.urlopen(RAW+SOURCE+'/'+path,timeout=60).read();assert sha(b)==digest,'SOURCE='+path;(OUT/name).write_bytes(b)
        gate=types.ModuleType('gate');exec(compile((OUT/'axiom-gate.py').read_bytes(),'gate','exec'),gate.__dict__);gate.self_test()
        source=scratch/'NeumannPhysicalCoordinateGreenIntegralDraft.lean'
        source.write_bytes((OUT/source.name).read_bytes())
        run('prerequisites',['lake','build','YangMills.RG.BalabanCMP89Eq246MassUniformPhysicalContour'])
        text=run('physical',['lake','env','lean','-o',str(OUT/'NeumannPhysicalCoordinateGreenIntegralDraft.olean'),str(source.relative_to(ROOT))])
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


