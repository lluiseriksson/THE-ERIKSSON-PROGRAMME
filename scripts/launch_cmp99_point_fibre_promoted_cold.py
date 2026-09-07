"""Pinned launcher for the intermediate F5 cold graph gate, never exploratory CI."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import urllib.request

REV = 'cmp99-point-fibre-promoted-cold-v1'
SOURCE = '6c49a8daeb6d6c6f60ac4a2cd2bafda67a495ff4'
TOOLS = '4a08173f79d4fab73b524605339c41085a9ae26b'
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
WORK = Path('/content/f5-promoted-cold-launch')
FILES = {
    'colab_cmp99_point_fibre_promoted_cold.py':
        (TOOLS, '9713719644c3ac294d8575da53d33afc17400b1d905fe34aa62ba303a4c756c2'),
    'verify_cmp99_point_fibre_promoted_cold.py':
        (TOOLS, 'f9a1c8b85731e8203d9046860005a1a0f867298ca2b33be3abf17396612f0a51'),
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
    verifier = str(WORK/'verify_cmp99_point_fibre_promoted_cold.py')
    child('verifier_self_test', [sys.executable, verifier, '--helpers', str(WORK), '--self-test'])
    child('cold_graph', [sys.executable, str(WORK/'colab_cmp99_point_fibre_promoted_cold.py')])
    archive = Path('/content/hrpoly-'+REV+'-evidence.tar.gz')
    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    child('archive_verifier', [sys.executable, verifier, '--helpers', str(WORK),
        '--archive', str(archive), '--sha256', digest])
    print('VERIFIED_ARCHIVE='+str(archive)+' SHA256='+digest, flush=True)
    print('LAUNCH_FINAL_STATUS=PASS INTERMEDIATE_COLD_GRAPH=1', flush=True)


def preserve(status):
    """Package launch logs and any cold archive before releasing control."""
    import tarfile
    result = WORK / 'launch-final-status.json'
    result.write_text(json.dumps(dict(status=status, source=SOURCE, revision=REV),
                                 sort_keys=True) + '\n')
    destination = Path('/content/f5-promoted-cold-preservation-20260905.tar.gz')
    if destination.exists():
        raise RuntimeError('PRESERVATION_ALREADY_EXISTS')
    archive = Path('/content/hrpoly-' + REV + '-evidence.tar.gz')
    with tarfile.open(destination, 'w:gz') as tar:
        tar.add(WORK, arcname=WORK.name)
        if archive.is_file():
            tar.add(archive, arcname=archive.name)
        tar.add(Path(__file__), arcname='launch_f5_promoted_cold.py')
    print('PRESERVATION_ARCHIVE=' + str(destination), flush=True)
    print('PRESERVATION_SHA256=' + hashlib.sha256(destination.read_bytes()).hexdigest(),
          flush=True)

if __name__ == '__main__':
    status = 'FAIL'
    try:
        main()
        status = 'PASS'
    except Exception:
        import traceback
        traceback.print_exc()
        print('LAUNCH_FINAL_STATUS=FAIL RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
        raise
    finally:
        if WORK.is_dir() and not (WORK / 'launch-final-status.json').exists():
            preserve(status)
