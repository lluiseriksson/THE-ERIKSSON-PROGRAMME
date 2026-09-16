"""One execution, four pinned instruments, actual exits and durable evidence."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import time
import traceback
import urllib.request

SOURCE = '9bba6c7b8c6f447a8e1914acca66e5c904beb154'
INSTRUMENT = 'f429e5b8007e666f1d19dad73715f9176e031ac1'
REV = 'neumann-integer-image-counting-diagnostic-v1'
WORK = Path('/content/' + REV + '-launch')
INNER = Path('/content/hrpoly-' + REV + '-evidence.tar.gz')
OUTER = Path('/content/' + REV + '-preservation-20260906.tar.gz')
PINS = {
    'neumann_integer_image_contract.py': 'fd53437cdfd46e31b9838055d04e4b21d1ae4a064bd1a6283406b318bc9784d5',
    'colab_neumann_integer_image_diagnostic.py': 'a9de3c61b120edd17f450b316526c2ee7d2aad64d4615966a5e215e4efbad2b5',
    'verify_neumann_integer_image_diagnostic.py': '6f2bedc5903420b1bbb9878e32cbb986e8a9a9466013f3c716d76a68a627271f',
    'verify_neumann_counting_reflection_diagnostic_v2.py': 'a596e50eb708d39819da3f15557fa5705ab564874b70d9913f8a8b9794bec851',
}
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if any(p.exists() for p in (WORK, INNER, OUTER)):
        raise RuntimeError('ALREADY_STARTED_NO_REEXECUTION')
    WORK.mkdir()
    status, records = 'FAIL', []

    def run(stage, command):
        log = WORK / (stage + '.log')
        start = time.perf_counter()
        with log.open('xb') as stream:
            child = subprocess.Popen(command, stdout=stream, stderr=subprocess.STDOUT)
            print('STAGE=' + stage + ' CHILD_PID=' + str(child.pid), flush=True)
            child.wait()
        r = dict(stage=stage, command=command, exit=child.returncode,
                 seconds=time.perf_counter()-start, log_sha256=sha(log))
        records.append(r)
        temp = WORK / 'records.tmp'
        temp.write_text(json.dumps(records, sort_keys=True) + '\n')
        temp.replace(WORK / 'records.json')
        print(json.dumps(r, sort_keys=True), flush=True)
        print(log.read_text(errors='replace')[-8000:], flush=True)
        if child.returncode:
            raise RuntimeError('FIRST_ERROR=' + stage)

    try:
        for name, digest in PINS.items():
            with urllib.request.urlopen(RAW + INSTRUMENT + '/scripts/' + name, timeout=60) as response:
                blob = response.read()
            if hashlib.sha256(blob).hexdigest() != digest:
                raise RuntimeError('TRANSPORT_HASH=' + name)
            (WORK / name).write_bytes(blob)
        (WORK / 'transport.json').write_text(json.dumps(dict(source=SOURCE,
            instrument=INSTRUMENT, pins=PINS), sort_keys=True) + '\n')
        run('image_diagnostic', [sys.executable, str(WORK / 'colab_neumann_integer_image_diagnostic.py')])
        run('independent_archive_verifier', [sys.executable,
            str(WORK / 'verify_neumann_integer_image_diagnostic.py'), '--archive', str(INNER),
            '--sha256', sha(INNER), '--runner-sha256', PINS['colab_neumann_integer_image_diagnostic.py'],
            '--contract-sha256', PINS['neumann_integer_image_contract.py']])
        status = 'PASS'
    except Exception:
        traceback.print_exc()
    finally:
        (WORK / 'final-status.json').write_text(json.dumps(dict(status=status,
            source=SOURCE, revision=REV, cold_seal=False), sort_keys=True) + '\n')
        with tarfile.open(OUTER, 'w:gz') as archive:
            archive.add(WORK, arcname=WORK.name)
            if INNER.is_file():
                archive.add(INNER, arcname=INNER.name)
            archive.add(Path(__file__), arcname='launch_neumann_integer_image_diagnostic.py')
        print('LAUNCH_FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('PRESERVATION_ARCHIVE=' + str(OUTER), flush=True)
        print('PRESERVATION_SHA256=' + sha(OUTER), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
