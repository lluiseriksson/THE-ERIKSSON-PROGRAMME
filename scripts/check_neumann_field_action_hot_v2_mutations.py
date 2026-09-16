"""Bounded rejection tests over the preserved actual HOT result; no compiler."""
import copy
import json
from pathlib import Path
from verify_neumann_generated_average_field_action_hot_v2 import verify, REV
from verify_neumann_counting_reflection_diagnostic_v2 import unpack, sha

archive = Path('validation-evidence/neumann-generated-average-field-action-hot-v2-20260906/'
               'neumann-generated-average-field-action-hot-v2-evidence.tar.gz').read_bytes()
assert sha(archive) == '6b3d1f7889c80bb1ba27802700ec5760b9422ba3a7efc4470e338d23c0a95a62'
original = {n.split('/', 1)[1]: b for n, b in unpack(archive).items()}
assert verify(original)['status'] == 'VERIFIED_HOT_PASS'
rejected = []

def reject(label, mutate):
    files = dict(original)
    data = json.loads(files['result.json'])
    mutate(files, data)
    files['result.json'] = (json.dumps(data, sort_keys=True) + '\n').encode()
    if 'records' in data:
        files['records.json'] = (json.dumps(data['records'], sort_keys=True) + '\n').encode()
    try:
        verify(files)
    except (ValueError, KeyError, AssertionError):
        rejected.append(label)
    else:
        raise AssertionError('INVALID_ACCEPTED=' + label)

for key, value in [('source', '0'*40), ('base_source', '0'*40),
                   ('cold_seal', True), ('status', 'UNKNOWN'),
                   ('parent_outer_sha256', '0'*64)]:
    reject(key, lambda f, d, k=key, v=value: d.__setitem__(k, v))
reject('missing_stage', lambda f, d: d['records'].pop())
reject('duplicate_stage', lambda f, d: d['records'].append(copy.deepcopy(d['records'][-1])))
reject('child_nonzero', lambda f, d: d['records'][-1].__setitem__('exit', 1))
reject('timeout', lambda f, d: d['records'][-1].__setitem__('timed_out', True))
reject('wrong_command', lambda f, d: d['records'][-1].__setitem__('command', ['true']))
reject('missing_name', lambda f, d: d['axioms']['physical_draft'].pop(next(iter(d['axioms']['physical_draft']))))
reject('output_changed', lambda f, d: f.__setitem__('physical_draft.olean', b'changed'))
reject('source_changed', lambda f, d: f.__setitem__('NeumannGeneratedAverageFieldActionDraft.lean', b'changed'))
reject('log_changed', lambda f, d: f.__setitem__('physical_draft.log', b'changed'))
reject('extra_file', lambda f, d: f.__setitem__('unexpected.txt', b'extra'))
reject('truncated_repro', lambda f, d: f.__setitem__('NeumannGeneratedAverageFieldActionIteRepro.lean', b'import Mathlib\n'))

def forbidden_axiom(files, data):
    name = next(iter(data['axioms']['physical_draft']))
    files['physical_draft.log'] += ("\n'" + name + "' depends on axioms: [sorryAx]\n").encode()
    for r in data['records']:
        if r['stage'] == 'physical_draft':
            r['log_sha256'] = sha(files['physical_draft.log'])
reject('forbidden_axiom_with_updated_log_hash', forbidden_axiom)
print('ACTUAL_HOT_ACCEPTED=1 MUTATIONS_REJECTED=' + str(len(rejected)))
print('NO_COMPILER_EVIDENCE=1')
