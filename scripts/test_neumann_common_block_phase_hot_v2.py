"""Synthetic instrument tests only; no compiler, network or real proof output."""
import copy
import json
from pathlib import Path
import subprocess
import types
import verify_neumann_common_block_phase_hot_v2 as v

def blob(ref, path):
    return subprocess.check_output(['git', 'cat-file', 'blob', ref + ':' + path], timeout=5)

rb = blob('6b7856c62c67caba2ad101d67e912ca8e6e5603d', 'scripts/colab_neumann_common_block_phase_hot_v2.py')
r = types.ModuleType('runner')
exec(compile(rb, 'runner', 'exec'), r.__dict__)
f = {'runner.py': rb, 'parent-reviewed-diagnostic-evidence.json': blob(r.REVIEW_REF, r.REVIEW_PATH)}
for p in r.PINS:
    f[Path(p).name] = blob(r.SOURCE_REFS[p], p)
commands = {
    'base_head': ['git', 'rev-parse', 'HEAD'],
    'mathlib_pin': ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
    'lean_version': ['lean', '--version'],
    'lake_version': ['lake', '--version'],
    'clean_before': ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'],
    'physical_prerequisites': ['lake', 'build', 'YangMills.RG.BalabanCMP89CenteredTorusGreenCoefficientPhase'],
    'physical_draft': ['lake', 'env', 'lean', '-o', '/content/' + r.REV + '-evidence/physical_draft.olean', 'tmp/' + r.REV + '/NeumannCommonBlockEndpointPhaseDraft.lean'],
    'clean_after': ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'],
}
records = []
for s, cmd in commands.items():
    text = ''
    if s == 'base_head': text = r.BASE
    if s == 'mathlib_pin': text = '07642720480157414db592fa85b626dafb71355b'
    if s in ('lean_version', 'lake_version'): text = '4.29.0-rc6'
    if s == 'physical_draft': text = '\n'.join("'YangMills.RG." + n + "' depends on axioms: [propext,\n Classical.choice, Quot.sound]" for n in r.NAMES[s])
    f[s + '.log'] = text.encode()
    records.append(dict(stage=s, command=cmd, cwd=v.ROOT, exit=0, timed_out=False,
        seconds=.01, timeout_seconds=600 if s == 'physical_prerequisites' else 120,
        log_sha256=v.sha(f[s + '.log'])))
for exe in ('lean', 'lake'): f[exe + '-sha256.txt'] = b'0' * 64 + b'\n'
f['physical_draft.olean'] = b'SYNTHETIC NOT A LEAN OUTPUT'
gate = types.ModuleType('gate')
exec(compile(f['full_green_owner_exact_axiom_gate.py'], 'gate', 'exec'), gate.__dict__)
d = dict(status='PASS', source=r.SOURCE, base_source=r.BASE, cold_seal=False,
    parent_outer_sha256=r.PARENT_OUTER_SHA, parent_review_sha256=r.REVIEW_HASH,
    parent_diagnostic_olean_sha256=r.PARENT_OLEAN_HASH,
    scope='common integer-block endpoint phases only; not full Green covariance, regional inverse, B0 or window15',
    source_refs=r.SOURCE_REFS, pins=r.PINS, names=r.NAMES, records=records,
    axioms={'physical_draft':gate.exact_axioms(f['physical_draft.log'].decode(), {'YangMills.RG.' + n for n in r.NAMES['physical_draft']})},
    outputs={'physical_draft.olean':v.sha(f['physical_draft.olean'])})
f['records.json'] = json.dumps(records).encode()
f['result.json'] = json.dumps(d).encode()
assert v.verify(f)['status'] == 'VERIFIED_HOT_PASS'
rejected = 0
for key, value in [('cold_seal', True), ('source', '0'*40), ('parent_diagnostic_olean_sha256', '0'*64), ('scope', 'inverse')]:
    g = copy.deepcopy(f)
    dd = copy.deepcopy(d)
    dd[key] = value
    g['result.json'] = json.dumps(dd).encode()
    try: v.verify(g)
    except (ValueError, KeyError): rejected += 1
    else: raise AssertionError('INVALID_ACCEPTED')
for key in ('runner.py', 'physical_draft.olean', 'parent-reviewed-diagnostic-evidence.json'):
    g = copy.deepcopy(f)
    g[key] += b'changed'
    try: v.verify(g)
    except (ValueError, KeyError): rejected += 1
    else: raise AssertionError('ALTERED_BYTES_ACCEPTED')
print('SYNTHETIC_VALID=1 REJECTED=' + str(rejected) + ' NOT_COMPILER_EVIDENCE')
