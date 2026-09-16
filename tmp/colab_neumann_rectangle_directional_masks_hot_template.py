"""Bounded directional rectangle masks HOT template, not executable until parent-cold pins are filled.

Parent-cold pins must come from independently preserved wrap/flat cold evidence.
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

SOURCE = 'adfef2b5b883a839e24b03ceedd118b32428dace'
BASE = '15e776db59c051571f79e47974acc2fbf597f715'
REV = 'neumann-rectangle-directional-masks-hot-v1'
ROOT = Path('/content/hrpoly-neumann-wrap-flat-promoted-cold-v1')
OUT = Path('/content/' + REV + '-evidence')
ARCHIVE = Path(str(OUT) + '.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
PINS = {
    "YangMills/RG/BalabanCMP89NeumannRectangleActiveRegion.lean": "d4d2fe4c099a297231ae71621de1cffa46e66e90ae60f51999a8200561c267eb",
    "scripts/full_green_owner_exact_axiom_gate.py": "016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2",
    "tmp/NeumannRectangleDirectionalMasksDraft.lean": "307267a89d4630b0e6de38ba2e81838e878851c58230e1b3e671a6939214c81a",
    "tmp/NeumannRectangleDirectionalMasksRepro.lean": "d9d3d2a1676d0b36106dd1ea76e9b806682cbc46327b55d9afdc50592b515062"
}
SOURCE_REFS = {p: (BASE if p.startswith('YangMills/') else SOURCE) for p in PINS}
NAMES = {
    "mathlib_repro": [
        "rectangleForwardMask_nat",
        "rectangleBackwardMask_nat"
    ],
    "physical_draft": [
        "rectangleForwardMask_nat",
        "rectangleBackwardMask_nat",
        "neumannRectangle_outgoingBond_iff",
        "neumannRectangle_incomingBond_iff"
    ]
}
# Deliberately unset until actual independently preserved parent cold evidence.
PARENT_OUTER_SHA = None
REVIEW_REF = None
REVIEW_PATH = 'validation-evidence/neumann-wrap-flat-cold-20260907/independent-local-verification.json'
REVIEW_HASH = None
PARENT_OLEAN_HASH = None


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    assert all(isinstance(v, str) and len(v) == n for v, n in ((PARENT_OUTER_SHA, 64), (REVIEW_REF, 40), (REVIEW_HASH, 64), (PARENT_OLEAN_HASH, 64))), 'PARENT_COLD_EVIDENCE_NOT_PINNED'
    assert ROOT.is_dir() and not OUT.exists() and not ARCHIVE.exists(), 'NO_REEXECUTION'
    parent = Path('/content/neumann-wrap-flat-promoted-cold-v1-preservation-20260907.tar.gz')
    assert sha(parent.read_bytes()) == PARENT_OUTER_SHA, 'PARENT_ARCHIVE'
    parent_status = json.loads(Path('/content/neumann-wrap-flat-promoted-cold-v1-launch/launch-final-status.json').read_text())
    assert parent_status == dict(status='PASS', source=BASE, revision='neumann-wrap-flat-promoted-cold-v1', cold_seal=True), 'PARENT_STATUS'
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
        assert review['cold']['production_outputs']['NeumannRectangleWrapProbe.olean'] == PARENT_OLEAN_HASH, 'REVIEW_OUTPUT'
        assert sha((ROOT / '.lake/build/lib/lean/YangMills/RG/NeumannRectangleWrapProbe.olean').read_bytes()) == PARENT_OLEAN_HASH, 'PARENT_OUTPUT_CHANGED'
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
        repro_op = OUT / 'mathlib_repro.olean'
        repro_text = run('mathlib_repro', ['lake', 'env', 'lean', '-o', str(repro_op),
            str((scratch / 'NeumannRectangleDirectionalMasksRepro.lean').relative_to(ROOT))])
        axioms['mathlib_repro'] = gate.exact_axioms(repro_text, {'YangMills.RG.' + n for n in NAMES['mathlib_repro']})
        assert repro_op.stat().st_size > 0
        outputs[repro_op.name] = sha(repro_op.read_bytes())
        run('physical_prerequisites', ["lake","build","YangMills.RG.BalabanCMP89NeumannRectangleActiveRegion"], timeout=600)
        for stage, path in [('physical_draft', 'NeumannRectangleDirectionalMasksDraft.lean')]:
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
            scope='actual directional torus rectangle bond masks including full-period sides; not physical carrier choice, reflection covariance, regional inverse, uniform B0 or window15'), sort_keys=True) + '\n')
        with tarfile.open(ARCHIVE, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(ARCHIVE), flush=True)
        print('ARCHIVE_SHA256=' + sha(ARCHIVE.read_bytes()), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
