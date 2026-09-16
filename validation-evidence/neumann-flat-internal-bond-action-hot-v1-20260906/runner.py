"""Bounded flat internal-bond action HOT template, not executable until parent-cold pins are filled.

Parent-cold pins must come from independently preserved internal-bond stencil cold evidence.
No source, equation, coefficient or inverse hypothesis may change to fill them.
"""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import tarfile
import time
import types
import urllib.request

SOURCE = '9838cd3c3c280971ef69fcf2e0bf19f4f193923c'
BASE = '81f35765ad50f8217bca20bc4530d99b3bf05103'
REV = 'neumann-flat-internal-bond-action-hot-v1'
ROOT = Path('/content/hrpoly-neumann-internal-bond-stencil-promoted-cold-v1')
OUT = Path('/content/' + REV + '-evidence')
ARCHIVE = Path(str(OUT) + '.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
PINS = {
    "YangMills/RG/NeumannInternalBondStencil.lean": "392a7a242b91a467496e520b7565b65ba2bed27831006fca00a4e54dc36ded1c",
    "YangMills/RG/BalabanCMP99SourceFlatPhysicalTransport.lean": "632b6cd59e19eb0da1efb6edc9e75a3e7cba9ff7e6c50237c57c4b734b855448",
    "scripts/full_green_owner_exact_axiom_gate.py": "016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2",
    "tmp/NeumannFlatInternalBondActionDraft.lean": "2478c299b924fb9976c6976d442fe3c2725b6ca5ea6f08178d196e4050c90c99"
}
SOURCE_REFS = {p: (BASE if p.startswith('YangMills/') else SOURCE) for p in PINS}
NAMES = {"physical_draft": ["neumannFlatInternalBond_extendedDerivative_apply", "neumannFlatInternalBond_laplacian_apply"]}
# Deliberately unset: only actual independently preserved parent-cold evidence may fill these.
PARENT_OUTER_SHA = '6c3977a59ccad04a4458bd615c3ddecdb3f36d5f9151e681eebcd376d26a917b'
REVIEW_REF = '39b0782587098e1698f75b8663b32cb5a6946773'
REVIEW_PATH = 'validation-evidence/neumann-internal-bond-stencil-cold-20260906/independent-local-verification.json'
REVIEW_HASH = '813813795f437c413166e3ece6c1755dde1c82ded8331dd0c0ca384fb58d9607'
PARENT_OLEAN_HASH = '17a9f0d27a509de604d384bfa00666fa6768e97c4a6d41b3a23fcd2acc49355f'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    assert all(isinstance(v, str) and len(v) == n for v, n in ((PARENT_OUTER_SHA, 64), (REVIEW_REF, 40), (REVIEW_HASH, 64), (PARENT_OLEAN_HASH, 64))), 'PARENT_COLD_EVIDENCE_NOT_PINNED'
    assert ROOT.is_dir() and not OUT.exists() and not ARCHIVE.exists(), 'NO_REEXECUTION'
    parent = Path('/content/neumann-internal-bond-stencil-promoted-cold-v1-preservation-20260906.tar.gz')
    assert sha(parent.read_bytes()) == PARENT_OUTER_SHA, 'PARENT_ARCHIVE'
    parent_status = json.loads(Path('/content/neumann-internal-bond-stencil-promoted-cold-v1-launch/launch-final-status.json').read_text())
    assert parent_status == dict(status='PASS', source=BASE, revision='neumann-internal-bond-stencil-promoted-cold-v1', cold_seal=True), 'PARENT_STATUS'
    OUT.mkdir()
    scratch = ROOT / 'tmp' / REV
    scratch.mkdir(exist_ok=False)
    env = os.environ.copy()
    bins = list(Path('/content/lean-4.29.0-rc6-linux').glob('**/bin/lake'))
    assert len(bins) == 1, 'EXACT_TOOLCHAIN_BIN'
    env['PATH'] = str(bins[0].parent) + ':' + env['PATH']
    records, axioms, outputs, status = [], {}, {}, 'FAIL'

    def run(stage, command, timeout=120):
        log = OUT / (stage + '.log')
        start, timed_out = time.perf_counter(), False
        with log.open('xb') as f:
            p = subprocess.Popen(command, cwd=ROOT, env=env, stdout=f,
                stderr=subprocess.STDOUT, start_new_session=True)
            print('STAGE=' + stage + ' PID=' + str(p.pid), flush=True)
            try:
                p.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
        b = log.read_bytes()
        r = dict(stage=stage, command=command, cwd=str(ROOT), exit=p.returncode,
            seconds=time.perf_counter()-start, timed_out=timed_out,
            timeout_seconds=timeout, log_sha256=sha(b))
        records.append(r)
        temp = OUT / 'records.tmp'
        temp.write_text(json.dumps(records, sort_keys=True) + '\n')
        temp.replace(OUT / 'records.json')
        print(json.dumps(r, sort_keys=True), flush=True)
        print(b.decode(errors='replace')[-6000:], flush=True)
        if p.returncode or timed_out:
            raise RuntimeError('FIRST_ERROR=' + stage)
        return b.decode()

    try:
        with urllib.request.urlopen(RAW + REVIEW_REF + '/' + REVIEW_PATH, timeout=60) as response:
            review_blob = response.read()
        assert sha(review_blob) == REVIEW_HASH, 'REVIEW_HASH'
        review = json.loads(review_blob)
        assert review['status'] == 'VERIFIED_COLD_PASS' and review['source'] == BASE and review['cold_seal'] is True, 'REVIEW_STATUS_SOURCE'
        assert review['outer_sha256'] == PARENT_OUTER_SHA, 'REVIEW_PARENT'
        assert review['cold']['status'] == 'PASS' and review['cold']['source_sha'] == BASE, 'REVIEW_COLD'
        assert review['cold']['production_outputs'] == {'NeumannInternalBondStencil.olean': PARENT_OLEAN_HASH}, 'REVIEW_OUTPUT'
        assert sha((ROOT / '.lake/build/lib/lean/YangMills/RG/NeumannInternalBondStencil.olean').read_bytes()) == PARENT_OLEAN_HASH, 'PARENT_OUTPUT_CHANGED'
        (OUT / 'parent-reviewed-cold-evidence.json').write_bytes(review_blob)
        assert run('base_head', ['git', 'rev-parse', 'HEAD']).strip() == BASE
        assert run('mathlib_pin', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']).strip() == '07642720480157414db592fa85b626dafb71355b'
        for exe in ('lean', 'lake'):
            assert '4.29.0-rc6' in run(exe + '_version', [exe, '--version'])
            (OUT / (exe + '-sha256.txt')).write_text(sha((bins[0].parent / exe).read_bytes()) + '\n')
        run('clean_before', ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        for path, digest in PINS.items():
            with urllib.request.urlopen(RAW + SOURCE_REFS[path] + '/' + path, timeout=60) as response:
                b = response.read()
            assert sha(b) == digest, 'SOURCE_HASH=' + path
            (OUT / Path(path).name).write_bytes(b)
            if path.endswith('.lean'):
                with (scratch / Path(path).name).open('xb') as f:
                    f.write(b)
        for path in PINS:
            if path.startswith('YangMills/'):
                assert sha((ROOT / path).read_bytes()) == PINS[path], 'BASE_SOURCE_CHANGED=' + path
        gate = types.ModuleType('pinned_gate')
        gb = (OUT / 'full_green_owner_exact_axiom_gate.py').read_bytes()
        exec(compile(gb, 'pinned_gate', 'exec'), gate.__dict__)
        gate.self_test()
        run('physical_prerequisites', ["lake","build","YangMills.RG.NeumannInternalBondStencil","YangMills.RG.BalabanCMP99SourceFlatPhysicalTransport"], timeout=600)
        for stage, path in [('physical_draft', 'NeumannFlatInternalBondActionDraft.lean')]:
            op = OUT / (stage + '.olean')
            text = run(stage, ['lake', 'env', 'lean', '-o', str(op), str((scratch / Path(path).name).relative_to(ROOT))])
            axioms[stage] = gate.exact_axioms(text, {'YangMills.RG.' + n for n in NAMES[stage]})
            assert op.stat().st_size > 0
            outputs[op.name] = sha(op.read_bytes())
            print('AXIOM_GATE=PASS ' + stage, flush=True)
        run('clean_after', ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        status = 'PASS'
    except Exception as e:
        print('ERROR=' + repr(e), flush=True)
    finally:
        (OUT / 'runner.py').write_bytes(Path(__file__).read_bytes())
        (OUT / 'result.json').write_text(json.dumps(dict(status=status, source=SOURCE,
            base_source=BASE, cold_seal=False, pins=PINS, source_refs=SOURCE_REFS, names=NAMES, records=records,
            axioms=axioms, outputs=outputs, parent_outer_sha256=PARENT_OUTER_SHA,
            parent_review_sha256=REVIEW_HASH, parent_production_olean_sha256=PARENT_OLEAN_HASH,
            scope='actual flat masked Neumann derivative and Laplacian only; not nonperiodic rectangle boundary law, regional inverse, uniform B0 or window15'), sort_keys=True) + '\n')
        with tarfile.open(ARCHIVE, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(ARCHIVE), flush=True)
        print('ARCHIVE_SHA256=' + sha(ARCHIVE.read_bytes()), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
