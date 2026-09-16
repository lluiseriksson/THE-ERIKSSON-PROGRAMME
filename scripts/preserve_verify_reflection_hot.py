"""Bounded archive verification only; no Lean, network, subprocess or pools."""
from pathlib import Path, PurePosixPath
import hashlib
import io
import json
import shutil
import sys
import tarfile
from full_green_owner_exact_axiom_gate import exact_axioms

OUTER = '5c2dac811cb81f6df02236ed092ca2948cf2f61bad84c3ffcdeb32030b0cca58'
INNER = [
    '44dffcda0ce7c6295b743d5261c30eb8f483bb3a9158ac114c3a19d06cab3544',
    '4ccd1e23eee9e6aee3034944c367c3eb14c52266bc3cf1e1392822e6f34c4a47',
    'fe422e85b137ff571d1779939b5c20275174395728d7db233c5300aeb741ca44',
    '92ceef59e36c9bb49b9e8595a77ba44f52bc89170a04b935d58f0a73c4a54bc0',
]
PRIOR = '0c4000e3bf98def88f6f96aeaea5d15970d72a43e86458976a68ce2ea7e1f901'
BASE = '10437a1a824bdd920282778cabe2f3da6c40ce4e'
SOURCES = ['47e975611f59ee8d95ec39317d4731918fe3b1bd'] * 2 + [
    '3918b24e4e78c2dafccc0062f0b62becbdd9fd66',
    'e46c93e3aa337bcf0c0feea19d61e97522f22861']

def sha(b):
    return hashlib.sha256(b).hexdigest()

def members(b):
    assert len(b) < 8_000_000
    result = {}
    with tarfile.open(fileobj=io.BytesIO(b), mode='r:gz') as tar:
        total = 0
        for m in tar:
            p = PurePosixPath(m.name)
            assert not p.is_absolute() and '..' not in p.parts
            assert m.isdir() or m.isfile()
            if m.isdir():
                continue
            total += m.size
            assert total < 32_000_000 and m.name not in result
            result[m.name] = tar.extractfile(m).read()
    return result

def main():
    archive, dest = map(Path, sys.argv[1:])
    assert archive.stat().st_size == 163259
    b = archive.read_bytes()
    assert sha(b) == OUTER and not dest.exists()
    outer = members(b)
    assert set(outer) == {f'neumann-block-reflection-hot-v{i}.tar.gz' for i in range(1, 5)}
    reports = []
    for i, digest in enumerate(INNER, 1):
        name = f'neumann-block-reflection-hot-v{i}'
        payload = outer[name + '.tar.gz']
        assert sha(payload) == digest
        raw = members(payload)
        assert all(p.startswith(name + '/') for p in raw)
        files = {p[len(name)+1:]: v for p, v in raw.items()}
        e = json.loads(files['evidence.json'])
        assert e['base'] == BASE and e['source'] == SOURCES[i-1]
        assert e['prior_sha256'] == PRIOR and e['cold_seal'] is False
        assert e['status'] == ('PASS' if i == 4 else 'FAIL')
        assert all(sha(files[p]) == h for p, h in e['files'].items())
        assert all(sha(files[p]) == h for p, h in e['source_blobs'].items())
        assert len(e['records']) == (1 if i < 3 else 2)
        assert e['records'] == json.loads(files['records.json'])
        for k, r in enumerate(e['records']):
            log = files[r['stage'] + '.log']
            assert sha(log) == r['log_sha256'] and not r['timed_out']
            assert r['exit'] == (1 if i < 4 and k == len(e['records'])-1 else 0)
            if r['exit'] == 0:
                expected = ({'neumannBlockReflection_div_repro'} |
                    ({'neumannBlockReflection_finrev_repro'} if i == 4 else set())) if k == 0 else {
                    'YangMills.RG.neumannBlockReflectionDraft_involutive',
                    'YangMills.RG.blockSite_neumannBlockReflectionDraft',
                    'YangMills.RG.neumannBlockReflectionDraft_sameOwner_iff'}
                assert exact_axioms(log.decode(), expected) == r['axioms']
                assert len(files[r['stage'] + '.olean']) > 0
                assert 'warning:' not in log.decode()
        reports.append(dict(version=i, archive_sha256=digest, **e))
    dest.mkdir(parents=True)
    shutil.copyfile(archive, dest / archive.name)
    report = dict(verification='PASS', cold_seal=False, outer_sha256=OUTER,
                  attempts=reports, scope='half-cell block geometry only; 20/41 unchanged')
    out = dest / 'independent-verification.json'
    out.write_text(json.dumps(report, sort_keys=True, indent=2)+'\n', encoding='utf-8')
    print('REFLECTION_HOT_PRESERVATION=PASS')
    print('REPORT_SHA256=' + sha(out.read_bytes()))

if __name__ == '__main__':
    main()
