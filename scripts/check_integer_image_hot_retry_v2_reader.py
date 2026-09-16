"""Mutation tests against the actual downloaded HOT archive; no compiler."""
import copy
import json
from pathlib import Path
from verify_neumann_counting_reflection_diagnostic_v2 import unpack
from verify_integer_image_hot_retry_v2 import check, REV

blob = (Path.home() / 'Downloads/neumann-integer-image-hot-retry-v2-evidence.tar.gz').read_bytes()
raw = unpack(blob)
prefix = REV + '-evidence/'
files = {n[len(prefix):]: b for n, b in raw.items()}
assert check(files)['status'] == 'VERIFIED_HOT_PASS'
bad = []
for name in ('runner.py', 'original-contract.py', 'axiom-gate.py',
             'mathlib-repro.lean', 'source_draft.olean', 'source_draft.log',
             'NeumannIntegerImageCountingKernelDraft.lean'):
    f = dict(files)
    f[name] += b'corrupt'
    bad.append(f)
for key, value in (('status', 'FAIL'), ('cold_seal', True), ('source', '0'*40)):
    f = dict(files)
    d = json.loads(f['result.json'])
    d[key] = value
    f['result.json'] = json.dumps(d).encode()
    bad.append(f)
f = dict(files)
d = json.loads(f['result.json'])
d['records'][5]['exit'] = 1
f['records.json'] = json.dumps(d['records']).encode()
f['result.json'] = json.dumps(d).encode()
bad.append(f)
for f in bad:
    try:
        check(f)
    except (AssertionError, ValueError, KeyError):
        continue
    raise AssertionError('MUTATION_ACCEPTED')
print('READER_TEST_PASS actual=1 rejected=' + str(len(bad)))
