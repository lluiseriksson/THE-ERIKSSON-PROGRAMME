"""One exact membership repair in the retained Colab graph; diagnostic only.

NOT EXECUTED: the retained host disappeared before this prepared retry could
run (2026-09-06). Keep this recipe as provenance; its prior/base gates reject
an empty replacement runtime. Use the pinned fresh diagnostic v2 instead.
"""
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

SOURCE = '06a928178b22c42c4ecc5387461b808ee3a19dea'
BASE = 'dc00d3fe4a583da601820605a98644e1fbc0245d'
ROOT = Path('/content/hrpoly-neumann-generated-counting-reflection-diagnostic-v1')
WORK = Path('/content/neumann-counting-reflection-hot-v2')
INPUT = ROOT/'tmp'/'neumann_counting_reflection_v2'
PRIOR = Path('/content/neumann-generated-counting-reflection-diagnostic-v1-preservation-20260905.tar.gz')
PRIOR_HASH = '97b8b08e71002036bdbe45b6f6e23547468e296a2bf566a61180514bc056f30a'
NAME = 'NeumannGeneratedCountingMassReflectionDraft.lean'
BLOB = '5f6edb3c6c7613d59d57cd943b7f9a20af23e3f2f6fe10a5643f696b0cb86fa9'
EXPECTED = {'YangMills.RG.neumannGeneratedFullSiteReflectionDraft_involutive',
    'YangMills.RG.neumannGeneratedTerminalOwner_reflection_draft',
    'YangMills.RG.neumannGeneratedFullCountingMass_reflection_draft'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert not WORK.exists() and not INPUT.exists(), 'ALREADY_STARTED_NO_REEXECUTION'
    assert sha(PRIOR) == PRIOR_HASH, 'PRIOR_HASH'
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip() == BASE, 'BASE_SHA'
    assert subprocess.run(['git','diff','--exit-code','HEAD','--',
        'YangMills','lean-toolchain','lake-manifest.json'],cwd=ROOT).returncode == 0, 'DIRTY_SOURCE'
    WORK.mkdir()
    (WORK/'runner.py').write_bytes(Path(__file__).read_bytes())
    os.environ['PATH'] = '/content/lean-4.29.0-rc6-linux/lean-4.29.0-rc6-linux/bin:' + os.environ['PATH']
    records = []
    status, error, axioms = 'FAIL', None, None
    try:
        helper = ROOT/'scripts'/'full_green_owner_exact_axiom_gate.py'
        assert sha(helper) == '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2', 'AXIOM_HELPER'
        (WORK/helper.name).write_bytes(helper.read_bytes())
        gate = types.ModuleType('pinned_gate')
        exec(compile(helper.read_bytes(),str(helper),'exec'),gate.__dict__)
        gate.self_test()
        INPUT.mkdir(parents=True,exist_ok=False)
        url = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/tmp/'+NAME
        with urllib.request.urlopen(url,timeout=60) as response:
            payload = response.read()
        assert hashlib.sha256(payload).hexdigest() == BLOB, 'SOURCE_HASH'
        (WORK/NAME).write_bytes(payload)
        (INPUT/NAME).write_bytes(payload)
        log = WORK/'draft.log'
        command = ['lake','env','lean','-o',str(WORK/'draft.olean'),str((INPUT/NAME).relative_to(ROOT))]
        started = time.perf_counter()
        timed_out = False
        with log.open('xb') as out:
            child = subprocess.Popen(command,cwd=ROOT,stdout=out,
                stderr=subprocess.STDOUT,start_new_session=True)
            print('CHILD_PID='+str(child.pid),flush=True)
            try:
                child.wait(timeout=180)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(child.pid,signal.SIGKILL)
                child.wait()
        record = dict(stage='counting_reflection_retry',command=command,cwd=str(ROOT),
            exit=child.returncode,timed_out=timed_out,seconds=time.perf_counter()-started,
            log_sha256=sha(log))
        records.append(record)
        (WORK/'records.tmp').write_text(json.dumps(records,sort_keys=True)+'\n')
        (WORK/'records.tmp').replace(WORK/'records.json')
        print(json.dumps(record,sort_keys=True),flush=True)
        print(log.read_text(),flush=True)
        assert child.returncode == 0 and not timed_out, 'FIRST_ERROR=counting_reflection_retry'
        axioms = gate.exact_axioms(log.read_text(),EXPECTED)
        assert (WORK/'draft.olean').is_file(), 'MISSING_OUTPUT'
        assert sha(PRIOR) == PRIOR_HASH, 'PRIOR_CHANGED'
        status = 'PASS'
    except Exception as exc:
        error = repr(exc)
        print('FIRST_ERROR='+error,flush=True)
    report = dict(status=status,cold_seal=False,source=SOURCE,base=BASE,
        prior_sha256=PRIOR_HASH,source_blob=BLOB,records=records,axioms=axioms,error=error,
        files={p.name:sha(p) for p in WORK.iterdir() if p.is_file()})
    tmp = WORK/'evidence.tmp'
    tmp.write_text(json.dumps(report,sort_keys=True)+'\n')
    tmp.replace(WORK/'evidence.json')
    archive = Path(str(WORK)+'.tar.gz')
    with tarfile.open(archive,'w:gz') as tar:
        tar.add(WORK,arcname=WORK.name)
    print('ARCHIVE='+str(archive)+' SHA256='+sha(archive),flush=True)
    print('FINAL_STATUS='+status+' COLD_SEAL=0',flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
