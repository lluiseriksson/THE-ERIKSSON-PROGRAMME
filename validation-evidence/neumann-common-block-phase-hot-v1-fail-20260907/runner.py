"""Bounded common-block phase HOT; blocked until parent evidence is pinned.

Run only after the actual-scalar diagnostic archive is independently preserved.
No cold seal, carrier choice, inverse or scalar-window attainment is inferred.
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

SOURCE = '93264d4b654022f51cd1d1f0ce7963de26408d4b'
BASE = 'eb5a9ec0609b015a3d367c0d729c2c2074a45b51'
REV = 'neumann-common-block-phase-hot-v1'
ROOT = Path('/content/hrpoly-neumann-actual-scalar-diagnostic-v1')
OUT = Path('/content/' + REV + '-evidence')
ARCHIVE = Path(str(OUT) + '.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
PINS = {
    "scripts/full_green_owner_exact_axiom_gate.py": "016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2",
    "tmp/NeumannCommonBlockEndpointPhaseDraft.lean": "51ca413f0cb903e721da9d701d594cb770cb252fb4e12a51b7ef509863fa3119"
}
SOURCE_REFS = {p: (BASE if p.startswith('YangMills/') else SOURCE) for p in PINS}
NAMES = {"physical_draft": ["neumannAliasTargetPhase_blockShift", "neumannAliasSourcePhase_blockShift", "neumannCommonBlockPhase_cancel"]}
# Deliberately unset until actual independently preserved parent diagnostic evidence.
PARENT_OUTER_SHA = 'd8bf0b29becbfc23b11ae923d667310d9d1a1a5c4182703b3240736117c18c72'
REVIEW_REF = 'f1e17f75aef75fbc589136722a33a5fc7edde93d'
REVIEW_PATH = 'validation-evidence/neumann-actual-scalar-diagnostic-v1-20260907/independent-verification.json'
REVIEW_HASH = '4ebca1702f13bac303fa371a5e6dfaf63b295fc71dda8ca3fa303388292af131'
PARENT_OLEAN_HASH = 'd4925a06a399d27ca2892a75bbcd577da756b42d0f520608c1eef2f77cc77a63'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    assert all(isinstance(v, str) and len(v) == n for v, n in ((PARENT_OUTER_SHA, 64), (REVIEW_REF, 40), (REVIEW_HASH, 64), (PARENT_OLEAN_HASH, 64))), 'PARENT_DIAGNOSTIC_EVIDENCE_NOT_PINNED'
    assert ROOT.is_dir() and not OUT.exists() and not ARCHIVE.exists(), 'NO_REEXECUTION'
    parent = Path('/content/hrpoly-neumann-actual-scalar-diagnostic-v1-evidence.tar.gz')
    assert sha(parent.read_bytes()) == PARENT_OUTER_SHA, 'PARENT_ARCHIVE'
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
        assert review['status'] == 'VERIFIED_DIAGNOSTIC_PASS' and review['source'] == BASE and review['cold_seal'] is False, 'REVIEW_STATUS_SOURCE'
        assert review['archive_sha256'] == PARENT_OUTER_SHA, 'REVIEW_PARENT'
        assert review['outputs']['NeumannActualFullSolutionScalarDraft.olean'] == PARENT_OLEAN_HASH, 'REVIEW_OUTPUT'
        assert sha((ROOT / '.lake/build/lib/lean/NeumannActualFullSolutionScalarDraft.olean').read_bytes()) == PARENT_OLEAN_HASH, 'PARENT_OUTPUT_CHANGED'
        (OUT / 'parent-reviewed-diagnostic-evidence.json').write_bytes(review_blob)
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
        run('physical_prerequisites', ["lake","build","YangMills.RG.BalabanCMP89CenteredTorusGreenCoefficientPhase"], timeout=600)
        for stage, path in [('physical_draft', 'NeumannCommonBlockEndpointPhaseDraft.lean')]:
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
            parent_review_sha256=REVIEW_HASH, parent_diagnostic_olean_sha256=PARENT_OLEAN_HASH,
            scope='common integer-block endpoint phases only; not full Green covariance, regional inverse, B0 or window15'), sort_keys=True) + '\n')
        with tarfile.open(ARCHIVE, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(ARCHIVE), flush=True)
        print('ARCHIVE_SHA256=' + sha(ARCHIVE.read_bytes()), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
