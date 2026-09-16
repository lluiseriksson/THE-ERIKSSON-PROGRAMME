"""Bounded mutations of a preserved archive; instrument test, not a new run."""
import copy
import json
from pathlib import Path
from verify_neumann_actual_full_green_images_hot_v1 import verify
from verify_neumann_counting_reflection_diagnostic_v2 import unpack, sha

p = Path('validation-evidence/neumann-actual-full-green-images-hot-v1-20260906/neumann-actual-full-green-images-hot-v1-evidence.tar.gz')
b = p.read_bytes()
assert sha(b) == 'b00bfb901dc0559f5ca13942cc1f5ec2a64749af0bfd37bd26f3310c9c1f4e03'
good = {n.split('/', 1)[1]: v for n, v in unpack(b).items()}
assert verify(good)['status'] == 'VERIFIED_HOT_PASS'
data = json.loads(good['result.json'])
bad = []

def fixture(d):
    f = dict(good)
    f['result.json'] = json.dumps(d).encode()
    f['records.json'] = json.dumps(d['records']).encode()
    return f

for n in ('runner.py', 'NeumannActualFullGreenReflectionSummabilityDraft.lean',
          'physical_draft.log', 'physical_draft.olean'):
    f = dict(good)
    f[n] += b'corruption'
    bad.append(f)
for key, value in [('parent_outer_sha256', '0'*64), ('source', '0'*40), ('cold_seal', True), ('status', 'FAIL')]:
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
