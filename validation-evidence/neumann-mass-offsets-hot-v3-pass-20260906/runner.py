"""Bounded actual mass/complete-offset diagnostic; not a cold seal."""
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

SOURCE = '6d02bcfd4091fb549dd9856f6fa95bb10e854643'
BASE = '7f7455b286da5809a0ee64a1511684f887cf8a88'
REV = 'neumann-generated-mass-complete-offsets-hot-v3'
ROOT = Path('/content/hrpoly-neumann-complete-fibre-promoted-cold-v1')
OUT = Path('/content/' + REV + '-evidence')
ARCHIVE = Path(str(OUT) + '.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
PINS = {
    "tmp/NeumannGeneratedMassCompleteOffsetsDraft.lean": "19c06eedbcc4c1f618f83ae5ed2df2a94b5d1edfccbcdb06dbd8c6b5b9242d58",
    "tmp/NeumannGeneratedMassCompleteOffsetsRepro.lean": "8359bbd989813c8daf10cc53ab5fa1d8a69e1ed8668c20f6069f98ec98f318ea",
    "YangMills/RG/NeumannGeneratedCompleteFibre.lean": "e551b8fe365aa5d20e1353f6b20e8789ab7ce750a3de99e3f9f635aa4c2917cf",
    "YangMills/RG/NeumannGeneratedAverageFieldAction.lean": "592e8967c9eb244dc3af6df69231979bbad36aae8554d76a1efe611538a552b1",
    "YangMills/RG/BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernel.lean": "034829a40a5ba4636b0fd252aa216f74d46312d130e86bde0fec36aba3c68aa7",
    "scripts/full_green_owner_exact_axiom_gate.py": "016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2"
}
SOURCE_REFS = {p: (BASE if p.startswith('YangMills/') else SOURCE) for p in PINS}
NAMES = {
    "physical_draft": [
        "neumannGeneratedActiveCoarseOwner",
        "sum_neumannGeneratedTerminalOwner_eq_completeOffsets",
        "neumannGeneratedWeightedMass_apply_eq_completeOffsets",
        "neumannGeneratedCountingMass_apply_eq_completeOffsets",
        "sum_neumannGeneratedTerminalOwner_integerField_eq_completeOffsets",
        "sum_neumannGeneratedTerminalOwner_commonImage_eq_completeOffsets"
    ]
}
PARENT_OUTER_SHA = 'e0516b0fbef4f87ce98700c96e9695a9c19557ac2484dce14b1cf4c84183d48c'
REVIEW_REF = '7a4eee0b08c8d535d869fad11b4c2db0048372c3'
REVIEW_PATH = 'validation-evidence/neumann-complete-fibre-cold-reviewed-20260906/reviewed-cold-evidence.json'
REVIEW_HASH = '59d55b07a9a1a79ef77f6a9b429f525f518830c7eab2a4206889ad646fba6ced'
PARENT_OLEAN_HASH = '3ae9c726f72c33ffc2afe176d801714f5eb2f4eaf117dbc26fba6f245d31c9e2'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    assert isinstance(PARENT_OUTER_SHA, str) and len(PARENT_OUTER_SHA) == 64, 'PARENT_COLD_EVIDENCE_NOT_PINNED'
    assert ROOT.is_dir() and not OUT.exists() and not ARCHIVE.exists(), 'NO_REEXECUTION'
    parent = Path('/content/neumann-complete-fibre-promoted-cold-v1-preservation-20260906.tar.gz')
    assert sha(parent.read_bytes()) == PARENT_OUTER_SHA, 'PARENT_ARCHIVE'
    parent_status = json.loads(Path('/content/neumann-complete-fibre-promoted-cold-v1-launch/launch-final-status.json').read_text())
    assert parent_status == dict(status='FAIL', source=BASE, revision='neumann-complete-fibre-promoted-cold-v1', cold_seal=True), 'ORIGINAL_PARENT_STATUS_CHANGED'
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
        assert review['status'] == 'PASS_AFTER_READER_CORRECTION' and review['source'] == BASE, 'REVIEW_STATUS_SOURCE'
        assert review['original_launch_status'] == 'FAIL' and review['original_outer_sha256'] == PARENT_OUTER_SHA, 'REVIEW_PARENT'
        assert review['cold']['status'] == 'PASS' and review['cold']['stages_verified'] == 16, 'REVIEW_COLD'
        assert sha((ROOT / '.lake/build/lib/lean/YangMills/RG/NeumannGeneratedCompleteFibre.olean').read_bytes()) == PARENT_OLEAN_HASH, 'PARENT_OUTPUT_CHANGED'
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
            str((scratch / 'NeumannGeneratedMassCompleteOffsetsRepro.lean').relative_to(ROOT))])
        assert repro_op.stat().st_size > 0
        outputs[repro_op.name] = sha(repro_op.read_bytes())
        run('physical_prerequisites', ["lake","build","YangMills.RG.NeumannGeneratedCompleteFibre","YangMills.RG.NeumannGeneratedAverageFieldAction","YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernel"], timeout=600)
        for stage, path in [('physical_draft', 'NeumannGeneratedMassCompleteOffsetsDraft.lean')]:
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
            scope='actual generated source-weighted/counting mass finite offsets and common integer image; not regional inverse, uniform B0 or window15'), sort_keys=True) + '\n')
        with tarfile.open(ARCHIVE, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(ARCHIVE), flush=True)
        print('ARCHIVE_SHA256=' + sha(ARCHIVE.read_bytes()), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
