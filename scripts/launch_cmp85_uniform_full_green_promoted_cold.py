"""Pinned launcher for the intermediate F4 cold graph gate, never exploratory CI."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import urllib.request

REV = 'cmp85-uniform-full-green-promoted-cold-v1'
SOURCE = '5138e9bd4bc88797c91c21df5bb5c630c71600ca'
TOOLS = '96fa32b3dcb6b4bbf6a9eedc40f12c8f5c178450'
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
WORK = Path('/content/f4-promoted-cold-launch')
FILES = {
    'colab_cmp85_uniform_full_green_promoted_cold.py':
        (TOOLS, 'f5bbc99cbc897c17dded603c87ceebe5ba9bd747f19273c377a401c4a8499622'),
    'verify_cmp85_uniform_full_green_promoted_cold.py':
        (TOOLS, 'f408dc8cb99fa1131f4b444f519c35a741dafc643f34e3881f4c49737e153da9'),
    'verify_cmp99_full_green_residue_cold.py':
        (SOURCE, '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c'),
    'full_green_owner_exact_axiom_gate.py':
        (SOURCE, '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'),
}

def main():
    if WORK.exists():
        raise RuntimeError('LAUNCH_ALREADY_STARTED_NO_REEXECUTION')
    WORK.mkdir()
    records = []
    def child(stage, command):
        log = WORK / (stage + '.log')
        start = time.perf_counter()
        with log.open('wb') as stream:
            result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
        record = dict(stage=stage, command=command, exit=result.returncode,
            seconds=time.perf_counter()-start,
            log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
        records.append(record)
        tmp = WORK / 'launch-records.json.tmp'
        tmp.write_text(json.dumps(records, sort_keys=True, indent=2)+'\n')
        tmp.replace(WORK / 'launch-records.json')
        print(json.dumps(record, sort_keys=True), flush=True)
        if result.returncode:
            print(log.read_text(errors='replace')[-8000:], flush=True)
            raise RuntimeError('FIRST_ERROR='+stage)
    print('SOURCE_SHA='+SOURCE+' RUNNER_REV='+REV, flush=True)
    for name, (commit, digest) in FILES.items():
        url = RAW+commit+'/scripts/'+name
        with urllib.request.urlopen(url, timeout=60) as response:
            blob = response.read()
        if hashlib.sha256(blob).hexdigest() != digest:
            raise RuntimeError('TRANSPORT_HASH_MISMATCH='+name)
        (WORK/name).write_bytes(blob)
        print('TRANSPORT_OK='+name+' SHA256='+digest, flush=True)
    (WORK/'transport.json').write_text(json.dumps(FILES, sort_keys=True, indent=2)+'\n')
    verifier = str(WORK/'verify_cmp85_uniform_full_green_promoted_cold.py')
    child('verifier_self_test', [sys.executable, verifier, '--helpers', str(WORK), '--self-test'])
    child('cold_graph', [sys.executable, str(WORK/'colab_cmp85_uniform_full_green_promoted_cold.py')])
    archive = Path('/content/hrpoly-'+REV+'-evidence.tar.gz')
    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    child('archive_verifier', [sys.executable, verifier, '--helpers', str(WORK),
        '--archive', str(archive), '--sha256', digest])
    print('VERIFIED_ARCHIVE='+str(archive)+' SHA256='+digest, flush=True)
    print('LAUNCH_FINAL_STATUS=PASS INTERMEDIATE_COLD_GRAPH=1', flush=True)

if __name__ == '__main__':
    try:
        main()
    except Exception:
        import traceback
        traceback.print_exc()
        print('LAUNCH_FINAL_STATUS=FAIL RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
        raise
