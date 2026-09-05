"""One-shot transport and preservation for the bounded owner/point HOT queue."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import time
import traceback
import urllib.request

WORK = Path('/content/owner-point-dictionary-hot-v1-launch')
INNER = Path('/content/cmp99-owner-point-dictionary-hot-v1-logs.tar.gz')
OUTER = Path('/content/owner-point-dictionary-hot-v1-preservation-20260905.tar.gz')
FILES = {
    'colab_cmp99_owner_point_dictionary_hot.py': (
        'c1536a7871d7671de15f79d8ebdf74a600cb2476',
        'af90f74a1c11f1a467bfaddfcd03a99ebd377602cdb161c323d2ea44e51b71c8'),
    'verify_cmp99_owner_point_dictionary_hot.py': (
        'baa65237eea398d7929a86ad89c218fe2a6958be',
        '19abb9e0e2992237216c163bae46b2b82cbcb08433c6270ad24c2c3eedae1e2b'),
    'full_green_owner_exact_axiom_gate.py': (
        '59f9f522f3f731ac8a6270ac5c3ae719b1b201f6',
        '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--prior-archive-sha256', required=True)
    args = p.parse_args()
    if WORK.exists() or INNER.exists() or OUTER.exists():
        raise RuntimeError('ALREADY_STARTED_NO_REEXECUTION')
    WORK.mkdir()
    records, status = [], 'FAIL'
    def child(stage,command):
        log = WORK / (stage+'.log')
        start = time.perf_counter()
        with log.open('xb') as out:
            proc = subprocess.run(command,stdout=out,stderr=subprocess.STDOUT)
        records.append(dict(stage=stage,command=command,exit=proc.returncode,
            seconds=time.perf_counter()-start,log_sha256=sha(log)))
        temp = WORK / 'launch-records.json.tmp'
        temp.write_text(json.dumps(records,sort_keys=True)+'\n')
        temp.replace(WORK / 'launch-records.json')
        print(json.dumps(records[-1],sort_keys=True),flush=True)
        if proc.returncode:
            print(log.read_text(errors='replace')[-8000:],flush=True)
            raise RuntimeError('FIRST_ERROR='+stage)
    try:
        for name,(commit,digest) in FILES.items():
            url = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+commit+'/scripts/'+name
            with urllib.request.urlopen(url,timeout=60) as response:
                blob = response.read()
            if hashlib.sha256(blob).hexdigest() != digest:
                raise RuntimeError('TRANSPORT_HASH='+name)
            (WORK/name).write_bytes(blob)
        (WORK/'transport.json').write_text(json.dumps(FILES,sort_keys=True)+'\n')
        runner = str(WORK/'colab_cmp99_owner_point_dictionary_hot.py')
        verify = [sys.executable,str(WORK/'verify_cmp99_owner_point_dictionary_hot.py'),
            '--runner',runner,'--axiom-gate',str(WORK/'full_green_owner_exact_axiom_gate.py')]
        child('verifier_self_test',verify+['--self-test'])
        child('owner_point_diagnostic',[sys.executable,runner,
            '--prior-archive-sha256',args.prior_archive_sha256])
        child('archive_verifier',verify+['--archive',str(INNER),'--sha256',sha(INNER),
            '--prior-sha256',args.prior_archive_sha256])
        status = 'PASS'
    except Exception:
        traceback.print_exc()
    finally:
        (WORK/'launch-final-status.json').write_text(json.dumps(dict(status=status,
            source='6f20ead457a528c2e5df6cc5fa2318fe43dbeeda',cold_seal=False,
            prior_archive_sha256=args.prior_archive_sha256),sort_keys=True)+'\n')
        with tarfile.open(OUTER,'w:gz') as tar:
            tar.add(WORK,arcname=WORK.name)
            if INNER.exists(): tar.add(INNER,arcname=INNER.name)
            tar.add(Path(__file__),arcname='launch_cmp99_owner_point_dictionary_hot.py')
        print('LAUNCH_FINAL_STATUS='+status+' COLD_SEAL=0',flush=True)
        print('PRESERVATION_ARCHIVE='+str(OUTER),flush=True)
        print('PRESERVATION_SHA256='+sha(OUTER),flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1',flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
