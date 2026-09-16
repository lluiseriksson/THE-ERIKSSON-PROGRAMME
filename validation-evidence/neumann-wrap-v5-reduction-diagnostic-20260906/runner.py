"""Instrumentation only: replay the preserved failed source with Lean diagnostics.
Not a gate, cold seal, proof repair or successful oracle. Retain first child exit.
"""
import hashlib,json,os,signal,subprocess,tarfile,time
from pathlib import Path
ROOT=Path('/content/hrpoly-neumann-internal-bond-stencil-promoted-cold-v1')
OUT=Path('/content/neumann-wrap-v5-reduction-diagnostic')
SOURCE='b5baabdeba5951c7b25fc6b942676f5d2c0fc6b8'
DRAFT='tmp/neumann-rectangle-wrap-probe-hot-v5/NeumannRectangleWrapProbeDraft.lean'
SHA='7a9fcb8095e15c3adb3eb50d85cd76ebe65809e5740f14c327aac41d93dbfe76'
def sha(b): return hashlib.sha256(b).hexdigest()
def main():
    assert not OUT.exists(),'NO_REEXECUTION'
    b=(ROOT/DRAFT).read_bytes()
    assert sha(b)==SHA,'SOURCE_HASH'
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()=='81f35765ad50f8217bca20bc4530d99b3bf05103'
    prior=json.loads(Path('/content/neumann-rectangle-wrap-probe-hot-v5-evidence/result.json').read_text())
    assert prior['source']==SOURCE and prior['status']=='FAIL'
    assert prior['records'][-1]['stage']=='physical_draft' and prior['records'][-1]['exit']==1
    OUT.mkdir()
    (OUT/'source.lean').write_bytes(b)
    (OUT/'runner.py').write_bytes(Path(__file__).read_bytes())
    bins=list(Path('/content/lean-4.29.0-rc6-linux').glob('**/bin/lake'))
    assert len(bins)==1
    env=os.environ.copy()
    env['PATH']=str(bins[0].parent)+':'+env['PATH']
    cmd=['lake','env','lean','-Ddiagnostics=true',DRAFT]
    start=time.monotonic()
    timed_out=False
    with (OUT/'diagnostics.log').open('xb') as log:
        p=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        print('DIAGNOSTIC_PID='+str(p.pid),flush=True)
        try: p.wait(timeout=30)
        except subprocess.TimeoutExpired:
            timed_out=True
            os.killpg(p.pid,signal.SIGKILL)
            p.wait()
    record=dict(source=SOURCE,source_sha256=SHA,command=cmd,cwd=str(ROOT),exit=p.returncode,
        seconds=time.monotonic()-start,timed_out=timed_out,timeout_seconds=30,
        log_sha256=sha((OUT/'diagnostics.log').read_bytes()),scope='instrumentation only; no proof verdict')
    (OUT/'result.json').write_text(json.dumps(record,sort_keys=True)+'\n')
    archive=Path(str(OUT)+'.tar.gz')
    with tarfile.open(archive,'w:gz') as t: t.add(OUT,arcname=OUT.name)
    print(json.dumps(record,sort_keys=True),flush=True)
    print('ARCHIVE_SHA256='+sha(archive.read_bytes()),flush=True)
    print('DIAGNOSTIC_FINISHED=1 NO_SEAL=1',flush=True)
    return p.returncode
if __name__=='__main__': raise SystemExit(main())
