"""Bounded canonical-Neumann spacing normalization HOT diagnostic after cold1162.

Parent-cold pins come from independently preserved cold1162 evidence.
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

SOURCE = '852d3b82ed5d0ffd2e5c38eb4eeb96c433858bbc'
BASE = '4746880218c694a9d4e9d32c0af61f86d460b7b4'
REV = 'neumann-canonical-spacing-hot-v1'
ROOT = Path('/content/hrpoly-neumann-canonical-precision-promoted-cold-v1')
OUT = Path('/content/' + REV + '-evidence')
ARCHIVE = Path(str(OUT) + '.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
PINS = {
    "YangMills/RG/NeumannCanonicalPrecisionOffsetAction.lean": "af4a26de1ffcac0a9ad6dc802f31cfe655b0b3bdef84f0c5dcf123fa1747e702",
    "YangMills/RG/BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse.lean": "8b5519b4861f78c2d7a5a98b8b8f3db03e22db6e54f8abc8fb05ebc494c5ecca",
    "scripts/full_green_owner_exact_axiom_gate.py": "016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2",
    "tmp/NeumannCanonicalSpacingNormalizationDraft.lean": "c59ee6910c6333b2ba99311f3064f5bca1f57a32e94d64a737fc3e6205a5dfcb",
    "tmp/NeumannCanonicalSpacingNormalizationRepro.lean": "53eb6ca13bdece88590563396d2b02d8f418f266e439649fea2908cce278484f"
}
SOURCE_REFS = {p: (BASE if p.startswith('YangMills/') else SOURCE) for p in PINS}
NAMES = {"physical_draft": [
    "neumannCanonicalFourierSpacing_terminal_eq_one",
    "neumannCanonicalFourierSpacing_countingCoefficient",
    "neumannCanonicalFourierSpacing_countingMassCoefficient"
]}
# Actual preserved cold1162 pins; no unreviewed parent is accepted.
PARENT_OUTER_SHA = 'd2f2434bd3a6a2719a33b3683ec630749f747d339b15911d95cca375bc98e81a'
REVIEW_REF = '806e7f32d60edb5b3dd64053d019658e60b22a85'
REVIEW_PATH = 'validation-evidence/neumann-canonical-precision-cold-20260906/independent-local-verification.json'
REVIEW_HASH = 'c556fe2293f438991d99b1a3e5d6581812944995ce6a69411cb54a02942e8644'
PARENT_OLEAN_HASH = '59ba1504c640479910b28d2cb68cdad817407b2665c3a0ca4e0dbc1c942ad336'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    assert all(isinstance(v, str) and len(v) == n for v, n in ((PARENT_OUTER_SHA, 64), (REVIEW_REF, 40), (REVIEW_HASH, 64), (PARENT_OLEAN_HASH, 64))), 'PARENT_COLD_EVIDENCE_NOT_PINNED'
    assert ROOT.is_dir() and not OUT.exists() and not ARCHIVE.exists(), 'NO_REEXECUTION'
    parent = Path('/content/neumann-canonical-precision-promoted-cold-v1-preservation-20260906.tar.gz')
    assert sha(parent.read_bytes()) == PARENT_OUTER_SHA, 'PARENT_ARCHIVE'
    parent_status = json.loads(Path('/content/neumann-canonical-precision-promoted-cold-v1-launch/launch-final-status.json').read_text())
    assert parent_status == dict(status='PASS', source=BASE, revision='neumann-canonical-precision-promoted-cold-v1', cold_seal=True), 'PARENT_STATUS'
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
        assert review['cold']['production_outputs'] == {'NeumannCanonicalPrecisionOffsetAction.olean': PARENT_OLEAN_HASH}, 'REVIEW_OUTPUT'
        assert sha((ROOT / '.lake/build/lib/lean/YangMills/RG/NeumannCanonicalPrecisionOffsetAction.olean').read_bytes()) == PARENT_OLEAN_HASH, 'PARENT_OUTPUT_CHANGED'
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
        run('mathlib_repro', ['lake', 'env', 'lean', '-o', str(repro_op),
            str((scratch / 'NeumannCanonicalSpacingNormalizationRepro.lean').relative_to(ROOT))])
        assert repro_op.stat().st_size > 0
        outputs[repro_op.name] = sha(repro_op.read_bytes())
        run('physical_prerequisites', ["lake","build","YangMills.RG.NeumannCanonicalPrecisionOffsetAction","YangMills.RG.BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse"], timeout=600)
        for stage, path in [('physical_draft', 'NeumannCanonicalSpacingNormalizationDraft.lean')]:
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
            scope='canonical fine-to-terminal spacing and counting coefficient normalization only; not boundary inverse, uniform B0 or window15'), sort_keys=True) + '\n')
        with tarfile.open(ARCHIVE, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(ARCHIVE), flush=True)
        print('ARCHIVE_SHA256=' + sha(ARCHIVE.read_bytes()), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
