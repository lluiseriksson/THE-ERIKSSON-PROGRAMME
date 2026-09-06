"""Bounded instrument self-test. Synthetic fixtures are NOT Lean evidence."""
import ast
import copy
import json
from pathlib import Path
import subprocess
import neumann_integer_image_contract as C
import verify_neumann_integer_image_diagnostic as V


def main():
    inputs = {p: subprocess.run(['git', 'cat-file', 'blob', C.SOURCE + ':' + p],
              check=True, capture_output=True).stdout for p in C.BLOBS}
    repro = C.minimal_text(inputs)
    assert repro.count(b'#print axioms') == 7
    assert b'import YangMills' not in repro
    assert repro.endswith(inputs[C.DRAFT][inputs[C.DRAFT].index(b'namespace YangMills.RG'):])
    scripts = ('neumann_integer_image_contract.py', 'colab_neumann_integer_image_diagnostic.py',
               'verify_neumann_integer_image_diagnostic.py')
    for name in scripts:
        ast.parse((Path('scripts') / name).read_text(encoding='utf-8'))
    runner = Path('scripts/colab_neumann_integer_image_diagnostic.py').read_bytes()
    contract = Path('scripts/neumann_integer_image_contract.py').read_bytes()
    gate = subprocess.run(['git', 'cat-file', 'blob', C.SOURCE +
                           ':scripts/full_green_owner_exact_axiom_gate.py'],
                          check=True, capture_output=True).stdout
    rh, ch = C.sha(runner), C.sha(contract)
    files = {'runner.py': runner, 'contract.py': contract,
             'full_green_owner_exact_axiom_gate.py': gate, 'mathlib-repro.lean': repro,
             **{Path(p).name: b for p, b in inputs.items()},
             'mathlib-repro.olean': b'SYNTHETIC ONLY', 'image-draft.olean': b'SYNTHETIC ONLY'}
    outputs = {n: C.sha(files[n]) for n in ('mathlib-repro.olean', 'image-draft.olean')}
    files['image-contract.json'] = json.dumps(dict(source=C.SOURCE, cold_seal=False,
        restored_project_outputs=False, names=sorted(C.NAMES), queue=list(C.COMMANDS),
        leaf_timeout_seconds=120, outputs=outputs,
        inputs={p: dict(file=Path(p).name, sha256=h) for p, h in C.BLOBS.items()})).encode()
    files['gate-contract.json'] = json.dumps(dict(source_sha=C.SOURCE,
        base_runner_sha256=C.BASE_RUNNER_HASH, project_build_cache_restored=False,
        expected_axiom_names=sorted(C.NAMES))).encode()
    files['preflight.json'] = json.dumps([dict(actual_exit=n, expected_exit=n, seconds=.01)
                                         for n in (0, 7)]).encode()
    records = []
    for s in V.REQUIRED:
        content = {'head': C.SOURCE, 'mathlib_pin': V.MATHLIB,
                   'lean_version': '4.29.0-rc6', 'lake_version': '4.29.0-rc6',
                   'final_clean_source': ''}.get(s, 'SYNTHETIC ONLY')
        if s in ('image_mathlib_repro', 'image_draft'):
            content = '\n'.join("'" + n + "' depends on axioms: [propext,\nClassical.choice, Quot.sound]"
                                for n in sorted(C.NAMES))
        cmd = C.COMMANDS.get(s, ['synthetic'])
        if s == 'checkout':
            cmd = ['git', 'checkout', '--detach', C.SOURCE]
        files[s + '.log'] = content.encode()
        r = dict(stage=s, command=cmd, cwd=C.ROOT, exit=0, seconds=.01,
                 log_file=s + '.log', output_sha256=C.sha(files[s + '.log']))
        if s in ('image_mathlib_repro', 'image_draft'):
            r['timed_out'] = False
        files[s + '.json'] = json.dumps(r).encode()
        records.append(r)
    data = dict(status='PASS', source_sha=C.SOURCE, runner_rev=C.REV, source_blobs=C.BLOBS,
                minimum_ram_gib=40.0, gpu_runtime_authorized=False, mathlib_sha=V.MATHLIB,
                toolchain_asset_sha256=V.ASSET, records=records)
    files['evidence.json'] = json.dumps(data).encode()
    V.check(files, rh, ch)
    bads = []
    for name in ('image-draft.olean', 'mathlib-repro.lean', 'runner.py', 'contract.py',
                 Path(C.DRAFT).name):
        bad = dict(files); bad[name] += b'WRONG'; bads.append(bad)
    for key, value in [('status', 'FAIL'), ('source_sha', 'wrong'), ('minimum_ram_gib', 12)]:
        bad = dict(files); d = copy.deepcopy(data); d[key] = value
        bad['evidence.json'] = json.dumps(d).encode(); bads.append(bad)
    for forbidden in ('sorryAx', 'ofReduceBool', 'Other.axiom'):
        bad = dict(files); d = copy.deepcopy(data); s = 'image_draft'
        bad[s + '.log'] = bad[s + '.log'].replace(b'Quot.sound', forbidden.encode())
        r = next(r for r in d['records'] if r['stage'] == s)
        r['output_sha256'] = C.sha(bad[s + '.log'])
        bad[s + '.json'] = json.dumps(r).encode()
        bad['evidence.json'] = json.dumps(d).encode(); bads.append(bad)
    for bad in bads:
        try:
            V.check(bad, rh, ch)
        except (ValueError, RuntimeError, KeyError):
            continue
        raise AssertionError('BAD_FIXTURE_ACCEPTED')
    print('IMAGE_INSTRUMENT_SELF_TEST=PASS synthetic=1 rejected=' + str(len(bads)))
    print('EXTRACTED_REPRO_SHA256=' + C.sha(repro))


if __name__ == '__main__':
    main()
