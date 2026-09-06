"""Bounded independent interval-image HOT diagnostic; no new bootstrap."""
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

SOURCE = '977d05282815960921d9397e2ff2a100cc4021dd'
BASE = '87edca6519df5b450b906e83db2ffa4fc1bd87bd'
REV = 'neumann-image-interval-hot-v1'
ROOT = Path('/content/hrpoly-neumann-integer-image-promoted-cold-v1')
OUT = Path('/content/' + REV + '-evidence')
ARCHIVE = Path(str(OUT) + '.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
PINS = {
    "tmp/NeumannImageIntervalCoverageDraft.lean": "baa0e468d676632ec4e89feec5028c0202acc6acff309ad59b07a4040064f085",
    "YangMills/RG/BalabanCMP89NeumannReflectionOrbitAlgebra.lean": "25a68943ae80ca3dcb4dbd22f2db7e10501d7b10c021692c84870f8a1fbb843a",
    "scripts/neumann_image_interval_repro_contract.py": "ffd03345111bc147e73553076861ab4ef57d363f545a0f0524d3fcb62d4abd2d",
    "scripts/full_green_owner_exact_axiom_gate.py": "016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2"
}
NAMES = {
    "mathlib_repro": [
        "neumannOrbitFalse_periodQuotient",
        "neumannOrbitTrue_periodQuotient",
        "neumannOrbitFalse_periodRemainder",
        "neumannOrbitTrue_periodRemainder",
        "neumannImageIntervalFamily_injective",
        "neumannImageIntervalFamily_surjective",
        "neumannImageIntervalFamily_bijective"
    ],
    "physical_draft": [
        "neumannOrbitFalse_periodQuotient",
        "neumannOrbitTrue_periodQuotient",
        "neumannOrbitFalse_periodRemainder",
        "neumannOrbitTrue_periodRemainder",
        "neumannImageIntervalFamily_injective",
        "neumannImageIntervalFamily_surjective",
        "neumannImageIntervalFamily_bijective"
    ]
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    assert ROOT.is_dir() and not OUT.exists() and not ARCHIVE.exists(), 'NO_REEXECUTION'
    parent = Path('/content/neumann-finite-integer-kernel-hot-v2-evidence.tar.gz')
    assert sha(parent.read_bytes()) == '91096b90e7d1583ee7b3ce88f3f09c2b74e2c882e618641df88efde17d43dbf9', 'PARENT_ARCHIVE'
    assert Path('/content/finite-integer-hot-v2-exit.txt').read_text().strip() == '0', 'PARENT_NOT_PASS'
    assert (ROOT / '.lake/build/lib/lean/YangMills/RG/BalabanCMP89NeumannReflectionOrbitAlgebra.olean').is_file(), 'PREREQUISITE_MISSING'
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
        contract = types.ModuleType('pinned_contract')
        cb = (OUT / 'neumann_image_interval_repro_contract.py').read_bytes()
        exec(compile(cb, 'pinned_contract', 'exec'), contract.__dict__)
        repro = contract.make_repro(
            (OUT / 'NeumannImageIntervalCoverageDraft.lean').read_bytes(),
            (OUT / 'BalabanCMP89NeumannReflectionOrbitAlgebra.lean').read_bytes())
        assert sha(repro) == 'ccfc6aa7e6a850256de48d93113a8b237079d5bad43bfd8cfcbad48b5e948c8d', 'REPRO_HASH'
        (OUT / 'mathlib-repro.lean').write_bytes(repro)
        with (scratch / 'mathlib-repro.lean').open('xb') as f:
            f.write(repro)
        assert sha((ROOT / contract.ORBIT_PATH).read_bytes()) == PINS[contract.ORBIT_PATH], 'BASE_ORBIT_CHANGED'
        gate = types.ModuleType('pinned_gate')
        gb = (OUT / 'full_green_owner_exact_axiom_gate.py').read_bytes()
        exec(compile(gb, 'pinned_gate', 'exec'), gate.__dict__)
        gate.self_test()
        for stage, path in [('mathlib_repro', 'mathlib-repro.lean'),
                            ('physical_draft', 'NeumannImageIntervalCoverageDraft.lean')]:
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
            axioms=axioms, outputs=outputs, scope='one-dimensional full image-family bijection, not image inverse'), sort_keys=True) + '\n')
        with tarfile.open(ARCHIVE, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(ARCHIVE), flush=True)
        print('ARCHIVE_SHA256=' + sha(ARCHIVE.read_bytes()), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
