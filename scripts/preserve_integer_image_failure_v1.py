"""Bounded exact FAIL preservation, never a mathematical PASS or cold seal."""
import json
import math
from pathlib import Path
import time
import neumann_integer_image_contract as C
from launch_neumann_integer_image_diagnostic import PINS
from verify_neumann_counting_reflection_diagnostic_v2 import unpack
from verify_neumann_integer_image_diagnostic import REQUIRED

START = time.perf_counter()
ARCHIVE = Path.home() / 'Downloads/neumann-integer-image-counting-diagnostic-v1-preservation-20260906.tar.gz'
EXPECTED = '2b5824b15159b5bf5e61e6fe25f5036bb152c68d212c85f7323a0b5eb3d61b5a'
INNER_SHA = '3c985e01f64b709b5e6332f84fa7cb8cbeb5fd6de88ea814b98b7711be81f80e'


def main():
    assert ARCHIVE.stat().st_size < 2**20
    blob = ARCHIVE.read_bytes()
    assert C.sha(blob) == EXPECTED
    outer = unpack(blob)
    prefix = C.REV + '-launch/'
    for name, digest in PINS.items():
        assert C.sha(outer[prefix + name]) == digest
    assert C.sha(outer['launch_neumann_integer_image_diagnostic.py']) == '8a5d7a91798be790f4b70cf0a7d114787609799a455b08154647f5747cac5568'
    final = json.loads(outer[prefix + 'final-status.json'])
    assert final == dict(status='FAIL', source=C.SOURCE, revision=C.REV, cold_seal=False)
    launch = json.loads(outer[prefix + 'records.json'])
    assert len(launch) == 1 and launch[0]['stage'] == 'image_diagnostic' and launch[0]['exit'] == 1
    assert C.sha(outer[prefix + 'image_diagnostic.log']) == launch[0]['log_sha256']
    inner_blob = outer[Path(C.EVIDENCE).name + '.tar.gz']
    assert C.sha(inner_blob) == INNER_SHA
    raw = unpack(inner_blob)
    ip = Path(C.EVIDENCE).name + '/'
    assert all(n.startswith(ip) and '/' not in n[len(ip):] for n in raw)
    files = {n[len(ip):]: b for n, b in raw.items()}
    data = json.loads(files['evidence.json'])
    assert data['status'] == 'FAIL' and data['source_sha'] == C.SOURCE and data['runner_rev'] == C.REV
    assert data['source_blobs'] == C.BLOBS
    assert files['head.log'].decode().strip() == C.SOURCE
    assert files['mathlib_pin.log'].decode().strip() == '07642720480157414db592fa85b626dafb71355b'
    inputs = {p: files[Path(p).name] for p in C.BLOBS}
    assert files['mathlib-repro.lean'] == C.minimal_text(inputs)
    records = data['records']
    stages = [r['stage'] for r in records]
    assert len(stages) == len(set(stages))
    assert [s for s in stages if s in REQUIRED] == REQUIRED[:REQUIRED.index('image_mathlib_repro') + 1]
    assert set(stages) <= set(REQUIRED) | {'apt_update', 'install_zstd'}
    for i, r in enumerate(records):
        s = r['stage']
        assert r['exit'] == (1 if i == len(records)-1 else 0)
        assert math.isfinite(r['seconds']) and r['seconds'] >= 0
        assert r['log_file'] == s + '.log'
        assert C.sha(files[s + '.log']) == r['output_sha256']
        assert json.loads(files[s + '.json']) == r
    last = records[-1]
    assert last['stage'] == 'image_mathlib_repro' and last['timed_out'] is False
    assert last['command'] == C.COMMANDS['image_mathlib_repro']
    log = files['image_mathlib_repro.log'].decode()
    assert C.sha(files['image_mathlib_repro.log']) == '3c9388556b331e504fca8cab325acb624b90c86c338e6ea10e3af46294cdfcb1'
    first = log.splitlines()[0]
    assert first == "tmp/NeumannIntegerImageCountingMathlibRepro.lean:76:6: error: 'change' tactic failed, pattern"
    assert 'sorryAx' in log and not any(n.endswith('.olean') for n in files)
    report = dict(classification='VERIFIED_FAILURE', mathematical_status='FAIL', cold_seal=False,
        source=C.SOURCE, archive_sha256=EXPECTED, inner_sha256=INNER_SHA,
        first_error=first, failed_stage=last, records_verified=len(records),
        not_run=['image_prerequisites', 'image_draft', 'final_clean_source', 'independent_archive_verifier'],
        counters=dict(producers='20/41', term_source=0, window15='not attained'))
    dest = Path('validation-evidence/neumann-integer-image-diagnostic-v1-fail-20260906')
    assert not dest.exists(), 'NO_OVERWRITE'
    dest.mkdir()
    (dest / ARCHIVE.name).write_bytes(blob)
    # Preserve all inner source/log records. Outer remains durable byte-for-byte.
    for name, b in files.items():
        (dest / name).write_bytes(b)
    payload = (json.dumps(report, indent=2, sort_keys=True) + '\n').encode()
    (dest / 'verified-failure.json').write_bytes(payload)
    print(json.dumps(report, sort_keys=True))
    print('VERIFIED_FAILURE_REPORT_SHA256=' + C.sha(payload))
    print('SECONDS=' + str(time.perf_counter()-START))


if __name__ == '__main__':
    main()
