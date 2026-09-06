"""Bounded independent reader for actual v2 HOT evidence, not a cold seal."""
import argparse
import json
import math
from pathlib import Path
import types
import neumann_integer_image_contract as C
from verify_neumann_counting_reflection_diagnostic_v2 import unpack

SOURCE = '8a0714a034be31c6f4f25243e1f1c2c2fc88431f'
REV = 'neumann-integer-image-hot-retry-v2'
DRAFT_HASH = '1077b61b5113678fa9cda799fafac904f2b302bdc7b67e342a342ebff96b8082'
RUNNER_HASH = 'e2360d489ee6eb9bedf5edb3ea049e72f660d69996ca0dc057771b4bc85b87cf'


def check(files):
    assert C.sha(files['runner.py']) == RUNNER_HASH
    cb = files['original-contract.py']
    assert C.sha(cb) == 'fd53437cdfd46e31b9838055d04e4b21d1ae4a064bd1a6283406b318bc9784d5'
    local = types.ModuleType('pinned_contract')
    exec(compile(cb, 'pinned_contract', 'exec'), local.__dict__)
    local.BLOBS[local.DRAFT] = DRAFT_HASH
    gb = files['axiom-gate.py']
    assert C.sha(gb) == C.GATE_HASH
    gate = types.ModuleType('pinned_gate')
    exec(compile(gb, 'pinned_gate', 'exec'), gate.__dict__)
    d = json.loads(files['result.json'])
    assert d['status'] == 'PASS' and d['source'] == SOURCE and d['cold_seal'] is False
    assert d['records'] == json.loads(files['records.json'])
    stages = ['base_head', 'mathlib_pin', 'clean_before', 'lean_version',
        'lake_version', 'mathlib_repro', 'image_prerequisites', 'source_draft', 'clean_after']
    assert [r['stage'] for r in d['records']] == stages
    assert files['base_head.log'].decode().strip() == C.SOURCE
    assert files['mathlib_pin.log'].decode().strip() == '07642720480157414db592fa85b626dafb71355b'
    assert files['clean_before.log'] == files['clean_after.log'] == b''
    for exe in ('lean', 'lake'):
        assert '4.29.0-rc6' in files[exe + '_version.log'].decode()
        assert len(files[exe + '-sha256.txt'].decode().strip()) == 64
    inputs = {p: files[Path(p).name] for p in local.BLOBS}
    assert files['mathlib-repro.lean'] == local.minimal_text(inputs)
    t = json.loads(files['transport.json'])
    assert t == dict(source=SOURCE, base=C.SOURCE, draft_sha256=DRAFT_HASH,
        input_pins=local.BLOBS, minimal_sha256=C.sha(files['mathlib-repro.lean']), cold_seal=False)
    expected = {'runner.py', 'original-contract.py', 'axiom-gate.py',
        'result.json', 'records.json', 'transport.json', 'mathlib-repro.lean',
        'lean-sha256.txt', 'lake-sha256.txt', *(Path(p).name for p in local.BLOBS)}
    for r in d['records']:
        s = r['stage']
        expected.add(s + '.log')
        assert r['exit'] == 0 and r['timed_out'] is False
        assert math.isfinite(r['seconds']) and r['seconds'] >= 0
        assert C.sha(files[s + '.log']) == r['log_sha256']
        assert r['timeout_seconds'] == (1800 if s == 'image_prerequisites' else 120)
        if s in ('mathlib_repro', 'source_draft'):
            kind = 'repro' if s == 'mathlib_repro' else 'draft'
            assert r['command'] == ['lake', 'env', 'lean', '-o',
                '/content/' + REV + '-evidence/' + s + '.olean',
                C.ROOT + '/tmp/' + REV + '-' + kind + '.lean']
            assert gate.exact_axioms(files[s + '.log'].decode(), C.NAMES) == d['axioms'][s]
        if s == 'image_prerequisites':
            assert r['command'] == ['lake', 'build', 'YangMills.RG.BalabanCMP89NeumannReflectionOrbitAlgebra']
    assert set(d['outputs']) == {'mathlib_repro.olean', 'source_draft.olean'}
    for n, h in d['outputs'].items():
        assert files[n] and C.sha(files[n]) == h
        expected.add(n)
    assert set(files) == expected
    return dict(status='VERIFIED_HOT_PASS', cold_seal=False, source=SOURCE,
        base_source=C.SOURCE, records=d['records'], outputs=d['outputs'], axioms=d['axioms'],
        scope='Integer image/owner/indicator only; physical operator and inverse open')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--archive', type=Path, required=True)
    ap.add_argument('--sha256', required=True)
    ap.add_argument('--destination', type=Path)
    a = ap.parse_args()
    assert a.archive.stat().st_size < 8 * 2**20
    blob = a.archive.read_bytes()
    assert C.sha(blob) == a.sha256.lower()
    raw = unpack(blob)
    prefix = REV + '-evidence/'
    assert all(n.startswith(prefix) and '/' not in n[len(prefix):] for n in raw)
    files = {n[len(prefix):]: b for n, b in raw.items()}
    report = check(files)
    report['archive_sha256'] = C.sha(blob)
    payload = (json.dumps(report, indent=2, sort_keys=True) + '\n').encode()
    if a.destination:
        assert not a.destination.exists(), 'NO_OVERWRITE'
        a.destination.mkdir()
        (a.destination / a.archive.name).write_bytes(blob)
        for n, b in files.items():
            (a.destination / n).write_bytes(b)
        (a.destination / 'independent-verification.json').write_bytes(payload)
    print(payload.decode())
    print('VERIFIED_HOT_REPORT_SHA256=' + C.sha(payload))


if __name__ == '__main__':
    main()
