"""Single Mathlib-only R3 repro on a retained pinned checkout. No cold claim."""
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

SOURCE='5ed3699ca40d9ecd178bb6a24ad929375ee6d1c0'
BASE='95c757465455c7e8cffcfcd6d9d18aa56f6d5083'
PIN='65ee59400a92d3914555c2bc09de80af8e5ddd14b111ce9428a5732e62f39745'
GATE='016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
REV='neumann-diagonal-transport-repro-v2'
ROOT=Path('/content/hrpoly-neumann-coordinate-precision-diagnostic-v1')
OUT=Path('/content/'+REV)
RAW='https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
NAMES=['NeumannDiagonalTransportRepro.action','NeumannDiagonalTransportRepro.action_function','NeumannDiagonalTransportRepro.solution_unique']
def sha(b):return hashlib.sha256(b).hexdigest()

def main():
    assert not OUT.exists(),'NO_REEXECUTION'; OUT.mkdir()
    scratch=ROOT/'tmp'/REV; scratch.mkdir(exist_ok=False)
    records=[]; status='FAIL'; error=None; audits={}
    env=os.environ.copy(); bins=list(Path('/content/lean-4.29.0-rc6-linux').glob('**/bin/lake'))
    assert len(bins)==1,'TOOLCHAIN'; env['PATH']=str(bins[0].parent)+':'+env['PATH']
    def run(stage,cmd):
        start=time.perf_counter(); timed=False
        with (OUT/(stage+'.log')).open('xb') as f:
            p=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            print('STAGE='+stage+' PID='+str(p.pid),flush=True)
            try:code=p.wait(timeout=120)
            except subprocess.TimeoutExpired:timed=True;os.killpg(p.pid,signal.SIGKILL);code=p.wait()
        b=(OUT/(stage+'.log')).read_bytes(); r=dict(stage=stage,command=cmd,cwd=str(ROOT),exit=code,seconds=time.perf_counter()-start,timed_out=timed,log_sha256=sha(b));records.append(r)
        (OUT/(stage+'.json')).write_text(json.dumps(r,sort_keys=True)+'\n')
        print(b.decode(errors='replace'),flush=True)
        assert code==0 and not timed,'FIRST_ERROR='+stage
        return b.decode()
    try:
        assert run('head',['git','rev-parse','HEAD']).strip()==BASE
        assert run('mathlib',['git','-C','.lake/packages/mathlib','rev-parse','HEAD']).strip()=='07642720480157414db592fa85b626dafb71355b'
        for exe in ('lean','lake'):
            assert '4.29.0-rc6' in run(exe+'_version',[exe,'--version'])
            (OUT/(exe+'-sha256.txt')).write_text(sha((bins[0].parent/exe).read_bytes())+'\n')
        for name,path,digest in [('NeumannDiagonalTransportRepro.lean','tmp/NeumannDiagonalTransportRepro.lean',PIN),('axiom-gate.py','scripts/full_green_owner_exact_axiom_gate.py',GATE)]:
            b=urllib.request.urlopen(RAW+SOURCE+'/'+path,timeout=60).read();assert sha(b)==digest,'SOURCE='+path;(OUT/name).write_bytes(b)
        gate=types.ModuleType('gate');exec(compile((OUT/'axiom-gate.py').read_bytes(),'gate','exec'),gate.__dict__);gate.self_test()
        source=scratch/'NeumannDiagonalTransportRepro.lean'
        source.write_bytes((OUT/source.name).read_bytes())
        text=run('repro',['lake','env','lean','-o',str(OUT/'NeumannDiagonalTransportRepro.olean'),str(source.relative_to(ROOT))])
        audits=gate.exact_axioms(text,set(NAMES));status='PASS'
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
