"""One Mathlib-first HOT finite integer/Q-kernel diagnostic in retained cold runtime."""
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

SOURCE = 'eb2fde64ff5597e6c3fa49d3beb114633e806d37'
BASE = '87edca6519df5b450b906e83db2ffa4fc1bd87bd'
REV = 'neumann-finite-integer-kernel-hot-v2'
ROOT = Path('/content/hrpoly-neumann-integer-image-promoted-cold-v1')
OUT = Path('/content/' + REV + '-evidence')
ARCHIVE = Path(str(OUT) + '.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
PINS = {
    'tmp/NeumannGeneratedIntegerCountingKernelDraft.lean': 'e4dee3b659ea6ceee7a114764a4f079f3c156a0ad83f6934c94362dbba320a74',
    'tmp/NeumannFiniteIntegerCoordinatesMathlibRepro.lean': '986dad72628054f5adf607c61c77b5e7c29c2871b3d785b6389f6fd3644c8b01',
    'scripts/full_green_owner_exact_axiom_gate.py': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
}
NAMES = {
    'mathlib_repro': ['neumannFiniteSiteIntegerCoordinates_injective', 'neumannOwnerCastRepro', 'neumannFiniteOwnerEqualityRepro'],
    'physical_draft': ['neumannFiniteSiteIntegerCoordinates_injective', 'neumannGeneratedTerminalOwner_integerCoordinates',
        'neumannGeneratedTerminalOwner_eq_iff_integerCoordinates', 'neumannGeneratedFlatCountingMass_integerOwner'],
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    assert ROOT.is_dir() and not OUT.exists() and not ARCHIVE.exists(), 'NO_REEXECUTION'
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
        gate = types.ModuleType('pinned_gate')
        gb = (OUT / 'full_green_owner_exact_axiom_gate.py').read_bytes()
        exec(compile(gb, 'pinned_gate', 'exec'), gate.__dict__)
        gate.self_test()
        for stage, path in [('mathlib_repro', 'tmp/NeumannFiniteIntegerCoordinatesMathlibRepro.lean'),
                            ('physical_draft', 'tmp/NeumannGeneratedIntegerCountingKernelDraft.lean')]:
            if stage == 'physical_draft':
                run('physical_prerequisites', ['lake', 'build', 'YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernel'], 3600)
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
            axioms=axioms, outputs=outputs, scope='finite integer owner and explicit counting mass, not image inverse'), sort_keys=True) + '\n')
        with tarfile.open(ARCHIVE, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(ARCHIVE), flush=True)
        print('ARCHIVE_SHA256=' + sha(ARCHIVE.read_bytes()), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
