"""Bounded literal Eq246 source-image insertion; retained cache, no cold claim."""
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

SOURCE = 'acc09ce87687c473f7fc8280e6d61c78e2d24f7e'
BASE = 'af35fbb8c75bf2347543034b3abf27f0217b1bbf'
REV = 'neumann-actual-full-green-images-hot-v1'
ROOT = Path('/content/hrpoly-neumann-integer-dictionary-cohort-cold-v1')
OUT = Path('/content/' + REV + '-evidence')
ARCHIVE = Path(str(OUT) + '.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
PINS = {
    "tmp/NeumannActualFullGreenReflectionSummabilityDraft.lean": "ac912343ac7f46cc2b8fb900943d53b7324e4b1ae04d2367ef680cd4be318041",
    "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalGreenInsertion.lean": "8d00ea71c6ae290aaefe4c6c5b107a69eb707ae5648695b1d35c0b1543ddca04",
    "YangMills/RG/BalabanCMP89Eq246MassUniformCenteredGreenFourierSummability.lean": "2320d5137734b7254e32b1a51cb5eb0406da60d6472a359dce8f4c3e3be24eef",
    "scripts/full_green_owner_exact_axiom_gate.py": "016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2"
}
NAMES = {
    "physical_draft": [
        "neumannActualFullGreenDecayCertificate",
        "summable_neumannActualFullGreenReflection_sum",
        "summable_neumannActualFullGreenReflection_real_sum"
    ]
}
PARENT_OUTER_SHA = '0c3a8858b2fab470e9a618ad084613f22c635ccc8b3942311d9ff623a7b04a34'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    assert ROOT.is_dir() and not OUT.exists() and not ARCHIVE.exists(), 'NO_REEXECUTION'
    parent = Path('/content/neumann-integer-dictionary-cohort-cold-v1-preservation-20260906.tar.gz')
    assert sha(parent.read_bytes()) == PARENT_OUTER_SHA, 'PARENT_ARCHIVE'
    assert Path('/content/neumann-integer-dictionary-cohort-cold-v1-exit.txt').read_text().strip() == '0', 'PARENT_NOT_PASS'
    assert sha(Path('/content/neumann-image-rectangle-hot-v2-evidence.tar.gz').read_bytes()) == 'aae64e9f3eb9966b7bfe1c90398e9460608082c2d3388fa4e2a67d2639f01f2e', 'PREVIOUS_PASS_PRESERVED'
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
        assert run('base_head', ['git', 'rev-parse', 'HEAD']).strip() == BASE
        assert run('mathlib_pin', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']).strip() == '07642720480157414db592fa85b626dafb71355b'
        for exe in ('lean', 'lake'):
            assert '4.29.0-rc6' in run(exe + '_version', [exe, '--version'])
            (OUT / (exe + '-sha256.txt')).write_text(sha((bins[0].parent / exe).read_bytes()) + '\n')
        run('clean_before', ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        for path, digest in PINS.items():
            with urllib.request.urlopen(RAW + SOURCE + '/' + path, timeout=60) as response:
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
        run('physical_prerequisites', ['lake', 'build',
            'YangMills.RG.BalabanCMP89NeumannRectangularPhysicalGreenInsertion',
            'YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenFourierSummability'], timeout=1800)
        for stage, path in [('physical_draft', 'NeumannActualFullGreenReflectionSummabilityDraft.lean')]:
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
            base_source=BASE, cold_seal=False, pins=PINS, names=NAMES, records=records,
            axioms=axioms, outputs=outputs, parent_outer_sha256=PARENT_OUTER_SHA,
            scope='literal Eq246 source-image summability, not regional inverse or uniform B0'), sort_keys=True) + '\n')
        with tarfile.open(ARCHIVE, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(ARCHIVE), flush=True)
        print('ARCHIVE_SHA256=' + sha(ARCHIVE.read_bytes()), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
