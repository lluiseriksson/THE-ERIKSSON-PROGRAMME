"""One bounded HOT repro/draft; not a cold seal. Preserve first real error."""
from pathlib import Path
import hashlib
import json
import os
import signal
import subprocess
import tarfile
import time
import types
import urllib.request

SOURCE = '47e975611f59ee8d95ec39317d4731918fe3b1bd'
BASE = '10437a1a824bdd920282778cabe2f3da6c40ce4e'
ROOT = Path('/content/hrpoly-cmp99-physical-value-action-promoted-cold-v1')
WORK = Path('/content/neumann-block-reflection-hot-v1')
PRIOR = Path(str(ROOT) + '-evidence.tar.gz')
PRIOR_HASH = '0c4000e3bf98def88f6f96aeaea5d15970d72a43e86458976a68ce2ea7e1f901'
BLOBS = {
    'NeumannBlockReflectionRepro.lean': '86f454067865f3b7eac480a6c59d127cc0dc7c21a9010ccbaa387d9b79417926',
    'NeumannBlockReflectionDraft.lean': 'facb070b5e6ad9b78e96850d3b86394de6c582928d8b1f9cd5b4405b8788b216',
}
NAMES = {
    'NeumannBlockReflectionRepro.lean': {'neumannBlockReflection_div_repro'},
    'NeumannBlockReflectionDraft.lean': {
        'YangMills.RG.neumannBlockReflectionDraft_involutive',
        'YangMills.RG.blockSite_neumannBlockReflectionDraft',
        'YangMills.RG.neumannBlockReflectionDraft_sameOwner_iff'},
}
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    assert not WORK.exists(), 'ALREADY_STARTED_NO_REEXECUTION'
    assert sha(PRIOR) == PRIOR_HASH, 'PRIOR_HASH'
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip() == BASE, 'BASE_SHA'
    assert subprocess.run(['git','diff','--exit-code','HEAD','--','YangMills','lean-toolchain','lake-manifest.json'],cwd=ROOT).returncode == 0, 'DIRTY_SOURCE'
    WORK.mkdir()
    (WORK/'runner.py').write_bytes(Path(__file__).read_bytes())
    os.environ['PATH'] = '/content/lean-4.29.0-rc6-linux/lean-4.29.0-rc6-linux/bin:' + os.environ['PATH']
    gate_path = Path('/content/physical-value-action-promoted-cold-v1-launch/full_green_owner_exact_axiom_gate.py')
    assert sha(gate_path) == '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2', 'AXIOM_HELPER_HASH'
    (WORK/gate_path.name).write_bytes(gate_path.read_bytes())
    gate = types.ModuleType('pinned_gate')
    exec(compile(gate_path.read_bytes(),str(gate_path),'exec'),gate.__dict__)
    records = []
    status, error = 'FAIL', None
    try:
        for name,digest in BLOBS.items():
            url = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/tmp/'+name
            with urllib.request.urlopen(url,timeout=60) as response:
                payload = response.read()
            assert hashlib.sha256(payload).hexdigest() == digest, 'SOURCE_HASH='+name
            (WORK/name).write_bytes(payload)
        for name in BLOBS:
            log = WORK/(name+'.log')
            command = ['lake','env','lean','-o',str(WORK/(name+'.olean')),str(WORK/name)]
            started = time.perf_counter()
            timed_out = False
            with log.open('xb') as out:
                child = subprocess.Popen(command,cwd=ROOT,stdout=out,
                    stderr=subprocess.STDOUT,start_new_session=True)
                try:
                    child.wait(timeout=180)
                except subprocess.TimeoutExpired:
                    timed_out = True
                    os.killpg(child.pid,signal.SIGKILL)
                    child.wait()
            record = dict(stage=name,command=command,exit=child.returncode,
                timed_out=timed_out,seconds=time.perf_counter()-started,log_sha256=sha(log))
            records.append(record)
            (WORK/'records.tmp').write_text(json.dumps(records,sort_keys=True)+'\n')
            (WORK/'records.tmp').replace(WORK/'records.json')
            print(json.dumps(record,sort_keys=True),flush=True)
            assert child.returncode == 0, 'FIRST_ERROR='+name
            record['axioms'] = gate.exact_axioms(log.read_text(),NAMES[name])
            (WORK/'records.tmp').write_text(json.dumps(records,sort_keys=True)+'\n')
            (WORK/'records.tmp').replace(WORK/'records.json')
        assert sha(PRIOR) == PRIOR_HASH, 'PRIOR_CHANGED'
        status = 'PASS'
    except Exception as exc:
        error = repr(exc)
        print('FIRST_ERROR='+error,flush=True)
    report = dict(status=status,cold_seal=False,source=SOURCE,base=BASE,
        prior_sha256=PRIOR_HASH,source_blobs=BLOBS,records=records,error=error,
        files={p.name:sha(p) for p in WORK.iterdir() if p.is_file()})
    (WORK/'evidence.json').write_text(json.dumps(report,sort_keys=True)+'\n')
    archive = Path(str(WORK)+'.tar.gz')
    with tarfile.open(archive,'w:gz') as tar:
        tar.add(WORK,arcname=WORK.name)
    print('ARCHIVE='+str(archive)+' SHA256='+sha(archive),flush=True)
    print('FINAL_STATUS='+status+' COLD_SEAL=0',flush=True)
    return 0 if status == 'PASS' else 1

if __name__ == '__main__':
    raise SystemExit(main())
