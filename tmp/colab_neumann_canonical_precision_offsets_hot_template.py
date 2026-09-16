"""Prepared canonical-Neumann finite-action HOT template; NOT READY TO RUN.

Four parent-cold pins must be populated only after independent preservation.
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

SOURCE = '5fa96640891aa7fc980b4e27a77c08e85bf6909f'
BASE = '9bb957757b6454871eaea6e26aed8c95dc576b3c'
REV = 'neumann-canonical-precision-offsets-hot-v1'
ROOT = Path('/content/hrpoly-neumann-mass-offsets-promoted-cold-v1')
OUT = Path('/content/' + REV + '-evidence')
ARCHIVE = Path(str(OUT) + '.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
PINS = {
    "YangMills/RG/BalabanCMP89NeumannPrecisionThreeSpecies.lean": "5b4869974f4adb2f8a4aa582eed14b0e07b7607addf1f3c13cd7b668a12207a1",
    "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision.lean": "401bf8c0c10291be569e30e2abb42ce2644ffa35895024b40944c4d4353d2585",
    "YangMills/RG/NeumannGeneratedMassCompleteOffsets.lean": "3a490345c5e0d8a7a6d3c87f5624075f294476fd1f261796893636ab666b2892",
    "YangMills/RG/NeumannRetainedCountingMassDictionary.lean": "4807e1d24361a4b9ac11ff423bed0820b933d9fc69a509f13c6ef1fb57dbf13c",
    "scripts/full_green_owner_exact_axiom_gate.py": "016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2",
    "tmp/NeumannCanonicalPrecisionOffsetActionDraft.lean": "c8fb07148897a3c6941a39075b9a29b5e79250b2d911d02349a4254e733ea405",
    "tmp/NeumannCanonicalPrecisionOffsetActionRepro.lean": "e9e0ee784e158c4efd8aef1b9bc0e30126d2b50ad74dfdfd044c15d1c3946cd8"
}
SOURCE_REFS = {p: (BASE if p.startswith('YangMills/') else SOURCE) for p in PINS}
NAMES = {"physical_draft": [
    "neumannCanonicalPrecision_eq_explicitCountingMass",
    "neumannCanonicalPrecision_apply_eq_completeOffsets"
]}
# Deliberately unset: no HOT launch before the live cold gate is preserved.
PARENT_OUTER_SHA = None
REVIEW_REF = None
REVIEW_PATH = 'validation-evidence/neumann-mass-offsets-cold-20260906/independent-local-verification.json'
REVIEW_HASH = None
PARENT_OLEAN_HASH = None


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    assert all(isinstance(v, str) and len(v) == n for v, n in ((PARENT_OUTER_SHA, 64), (REVIEW_REF, 40), (REVIEW_HASH, 64), (PARENT_OLEAN_HASH, 64))), 'PARENT_COLD_EVIDENCE_NOT_PINNED'
    assert ROOT.is_dir() and not OUT.exists() and not ARCHIVE.exists(), 'NO_REEXECUTION'
    parent = Path('/content/neumann-mass-offsets-promoted-cold-v1-preservation-20260906.tar.gz')
    assert sha(parent.read_bytes()) == PARENT_OUTER_SHA, 'PARENT_ARCHIVE'
    parent_status = json.loads(Path('/content/neumann-mass-offsets-promoted-cold-v1-launch/launch-final-status.json').read_text())
    assert parent_status == dict(status='PASS', source=BASE, revision='neumann-mass-offsets-promoted-cold-v1', cold_seal=True), 'PARENT_STATUS'
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
        assert review['cold']['production_outputs'] == {'NeumannGeneratedMassCompleteOffsets.olean': PARENT_OLEAN_HASH}, 'REVIEW_OUTPUT'
        assert sha((ROOT / '.lake/build/lib/lean/YangMills/RG/NeumannGeneratedMassCompleteOffsets.olean').read_bytes()) == PARENT_OLEAN_HASH, 'PARENT_OUTPUT_CHANGED'
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
            str((scratch / 'NeumannCanonicalPrecisionOffsetActionRepro.lean').relative_to(ROOT))])
        assert repro_op.stat().st_size > 0
        outputs[repro_op.name] = sha(repro_op.read_bytes())
        run('physical_prerequisites', ["lake","build","YangMills.RG.BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision","YangMills.RG.BalabanCMP89NeumannPrecisionThreeSpecies","YangMills.RG.NeumannRetainedCountingMassDictionary","YangMills.RG.NeumannGeneratedMassCompleteOffsets"], timeout=600)
        for stage, path in [('physical_draft', 'NeumannCanonicalPrecisionOffsetActionDraft.lean')]:
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
            scope='literal canonical Neumann precision finite-offset action only; not Fourier normalization, regional inverse, uniform B0 or window15'), sort_keys=True) + '\n')
        with tarfile.open(ARCHIVE, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(ARCHIVE), flush=True)
        print('ARCHIVE_SHA256=' + sha(ARCHIVE.read_bytes()), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
