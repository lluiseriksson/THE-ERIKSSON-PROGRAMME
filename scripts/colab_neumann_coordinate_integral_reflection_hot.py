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

SOURCE='76e777daccc7282628c0187810cde8477cf0a3b0'
BASE='95c757465455c7e8cffcfcd6d9d18aa56f6d5083'
PIN='e3c0fa979a32033284f496acc925c2005851cc2b6cece7c136421fc6717d16e1'
GATE='016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
REV='neumann-coordinate-integral-reflection-hot-v1'
ROOT=Path('/content/hrpoly-neumann-coordinate-precision-diagnostic-v1')
OUT=Path('/content/'+REV)
RAW='https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
NAMES=['YangMills.RG.neumannIntervalCoordinateReflection_insertNth','YangMills.RG.neumannIntegral_coordinateReflection']
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
        (OUT/'parents.json').write_text('{}\n')
        assert run('head',['git','rev-parse','HEAD']).strip()==BASE
        assert run('mathlib',['git','-C','.lake/packages/mathlib','rev-parse','HEAD']).strip()=='07642720480157414db592fa85b626dafb71355b'
        for exe in ('lean','lake'):
            assert '4.29.0-rc6' in run(exe+'_version',[exe,'--version'])
            (OUT/(exe+'-sha256.txt')).write_text(sha((bins[0].parent/exe).read_bytes())+'\n')
        for name,path,digest in [('NeumannCoordinateIntegralReflectionDraft.lean','tmp/NeumannCoordinateIntegralReflectionDraft.lean',PIN),('axiom-gate.py','scripts/full_green_owner_exact_axiom_gate.py',GATE)]:
            b=urllib.request.urlopen(RAW+SOURCE+'/'+path,timeout=60).read();assert sha(b)==digest,'SOURCE='+path;(OUT/name).write_bytes(b)
        gate=types.ModuleType('gate');exec(compile((OUT/'axiom-gate.py').read_bytes(),'gate','exec'),gate.__dict__);gate.self_test()
        source=scratch/'NeumannCoordinateIntegralReflectionDraft.lean'
        source.write_bytes((OUT/source.name).read_bytes())
        run('prerequisites',['lake','build','YangMills.RG.IntervalIntegralPiCoordinateTransport'])
        text=run('physical',['lake','env','lean','-o',str(OUT/'NeumannCoordinateIntegralReflectionDraft.olean'),str(source.relative_to(ROOT))])
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
