"""Bounded coordinate alias reflection HOT; blocked until parent evidence is pinned.

Run only after the common-translation diagnostic archive is independently preserved.
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

SOURCE = '6804b00aadf10ea9181044d150128c8942b9e7c7'
BASE = '327a79d3e88e9580a2c37238f25d1f1f6b9f8429'
REV = 'neumann-coordinate-alias-reflection-hot-v1'
ROOT = Path('/content/hrpoly-neumann-actual-common-translation-diagnostic-v1')
OUT = Path('/content/' + REV + '-evidence')
ARCHIVE = Path(str(OUT) + '.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
PINS = {
    "scripts/full_green_owner_exact_axiom_gate.py": "016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2",
    "tmp/NeumannCoordinateAliasReflectionDraft.lean": "ffb4bbab01f8f49b593d2f2657f12a499232501a54bb64638c0320c8d28aea3e"
}
SOURCE_REFS = {p: (BASE if p.startswith('YangMills/') else SOURCE) for p in PINS}
NAMES = {"physical_draft":["neumannAliasPiCoordinateReflection_self","neumannAliasPiCoordinateReflection_other","neumannAliasCoordinateReflection_other","neumannAliasCoordinateReflection_residue","neumannAliasCoordinateReflection_involutive","neumannAliasCoordinateReflection_sum","neumannPhysicalAliasCoordinateReflection_central"]}
# Deliberately unset until actual independently preserved parent diagnostic evidence.
PARENT_OUTER_SHA = None
REVIEW_REF = None
REVIEW_PATH = 'validation-evidence/neumann-actual-common-translation-diagnostic-v1-20260907/independent-verification.json'
REVIEW_HASH = None
PARENT_OLEAN_HASH = None


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    assert all(isinstance(v, str) and len(v) == n for v, n in ((PARENT_OUTER_SHA, 64), (REVIEW_REF, 40), (REVIEW_HASH, 64), (PARENT_OLEAN_HASH, 64))), 'PARENT_DIAGNOSTIC_EVIDENCE_NOT_PINNED'
    assert ROOT.is_dir() and not OUT.exists() and not ARCHIVE.exists(), 'NO_REEXECUTION'
    parent = Path('/content/hrpoly-neumann-actual-common-translation-diagnostic-v1-evidence.tar.gz')
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
        assert review['outputs']['NeumannActualCommonBlockTranslationDraft.olean'] == PARENT_OLEAN_HASH, 'REVIEW_OUTPUT'
        assert sha((ROOT / '.lake/build/lib/lean/NeumannActualCommonBlockTranslationDraft.olean').read_bytes()) == PARENT_OLEAN_HASH, 'PARENT_OUTPUT_CHANGED'
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
        run('physical_prerequisites', ["lake","build","YangMills.RG.BalabanCMP99SourceAliasReflectionInvolutive","YangMills.RG.BalabanCMP99SourceAliasReflectionStabilizedSolution"], timeout=600)
        for stage, path in [('physical_draft', 'NeumannCoordinateAliasReflectionDraft.lean')]:
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
            scope='one-coordinate actual alias permutation and central preservation only; not precision or Green covariance, inverse, B0 or window15'), sort_keys=True) + '\n')
        with tarfile.open(ARCHIVE, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(ARCHIVE), flush=True)
        print('ARCHIVE_SHA256=' + sha(ARCHIVE.read_bytes()), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
