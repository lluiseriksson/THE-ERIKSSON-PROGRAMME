"""Bounded mutations of a preserved archive; instrument test, not a new run."""
import copy
import json
from pathlib import Path
from verify_neumann_image_interval_hot_v3 import verify
from verify_neumann_counting_reflection_diagnostic_v2 import unpack, sha

p = Path('validation-evidence/neumann-image-interval-hot-v3-20260906/neumann-image-interval-hot-v3-evidence.tar.gz')
b = p.read_bytes()
assert sha(b) == '34387a931f104302b88107f641ddac6741965b1ce18dad7f50486c28af55c1fc'
good = {n.split('/', 1)[1]: v for n, v in unpack(b).items()}
assert verify(good)['status'] == 'VERIFIED_HOT_PASS'
data = json.loads(good['result.json'])
bad = []

def fixture(d):
    f = dict(good)
    f['result.json'] = json.dumps(d).encode()
    f['records.json'] = json.dumps(d['records']).encode()
    return f

for n in ('runner.py', 'NeumannImageIntervalCoverageDraft.lean', 'mathlib-repro.lean',
          'physical_draft.log', 'physical_draft.olean'):
    f = dict(good)
    f[n] += b'corruption'
    bad.append(f)
for key, value in [('source', '0'*40), ('cold_seal', True), ('status', 'FAIL')]:
    d = copy.deepcopy(data)
    d[key] = value
    bad.append(fixture(d))
for key, value in [('exit', 1), ('timed_out', True), ('cwd', '/wrong'),
                   ('seconds', float('nan')), ('command', ['echo', 'PASS']),
                   ('timeout_seconds', 9999)]:
    d = copy.deepcopy(data)
    d['records'][6][key] = value
    bad.append(fixture(d))
for mutate in ('missing', 'duplicate'):
    d = copy.deepcopy(data)
    if mutate == 'missing':
        d['records'].pop()
    else:
        d['records'].append(d['records'][-1])
    bad.append(fixture(d))
f = dict(good)
f['unexpected.txt'] = b'unexpected'
bad.append(f)
for v in (1, 2):
    old = Path(f'validation-evidence/neumann-image-interval-hot-v{v}-fail-20260906/neumann-image-interval-hot-v{v}-evidence.tar.gz')
    bad.append({n.split('/', 1)[1]: b for n, b in unpack(old.read_bytes()).items()})
for f in bad:
    try:
        verify(f)
    except (AssertionError, ValueError, KeyError):
        continue
    raise AssertionError('MUTATION_OR_OLD_FAILURE_ACCEPTED')
print('INSTRUMENT_TEST_ONLY actual_pass=1 rejected=' + str(len(bad)))
