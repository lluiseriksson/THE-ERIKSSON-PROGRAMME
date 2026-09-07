"""Bounded finite-block image averaging HOT diagnostic; no new bootstrap."""
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

SOURCE = '4c8171bdc4f70606d89de05f53b6f90d39e689b8'
SUPPORT_SOURCE = '4c8171bdc4f70606d89de05f53b6f90d39e689b8'
BASE = 'af35fbb8c75bf2347543034b3abf27f0217b1bbf'
REV = 'neumann-integer-block-image-average-hot-v1'
ROOT = Path('/content/hrpoly-neumann-integer-dictionary-cohort-cold-v1')
OUT = Path('/content/' + REV + '-evidence')
ARCHIVE = Path(str(OUT) + '.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
PINS = {
    "tmp/NeumannIntegerBlockImageAverageDraft.lean": "a16ac31056401feee09e97df149fc3460852bd820349f3280eac06a245ae5f62",
    "YangMills/L0_Lattice/FiniteLattice.lean": "6713bde615562a3f1eae351e2157208826cacd9b1a3c557df42a1fccd7d7de9c",
    "YangMills/RG/NeumannHalfCellBlockReflection.lean": "d4f2ca991e1e3a4dcddf295539de73e3b2272c00bbc4a96ad2e670a7dd74faa4",
    "YangMills/RG/BalabanCMP89NeumannReflectionOrbitAlgebra.lean": "25a68943ae80ca3dcb4dbd22f2db7e10501d7b10c021692c84870f8a1fbb843a",
    "YangMills/RG/BalabanCMP89NeumannReflectionBranchSum.lean": "a2bc16c72a54e7baaf9389bc1f4124eb568bfbaae03150423963585a499852c0",
    "scripts/neumann_integer_block_image_average_repro_contract.py": "4b1f4b1f0096ca10f74eb37a0c32782573a549e4e9dd80eed5a75e60f9e2b59e",
    "scripts/full_green_owner_exact_axiom_gate.py": "016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2"
}
NAMES = {
    "mathlib_repro": [
        "neumannIntegerImage_fineBlockPoint",
        "sum_neumannIntegerImage_fineBlockPoint",
        "weightedSum_neumannIntegerImage_fineBlockPoint"
    ],
    "physical_draft": [
        "neumannIntegerImage_fineBlockPoint",
        "sum_neumannIntegerImage_fineBlockPoint",
        "weightedSum_neumannIntegerImage_fineBlockPoint"
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
    assert (ROOT / '.lake/build/lib/lean/YangMills/RG/NeumannIntegerImageCountingKernel.olean').is_file(), 'PREREQUISITE_MISSING'
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
            ref = SOURCE if path == 'tmp/NeumannIntegerBlockImageAverageDraft.lean' else SUPPORT_SOURCE
            with urllib.request.urlopen(RAW + ref + '/' + path, timeout=60) as response:
                b = response.read()
            assert sha(b) == digest, 'SOURCE_HASH=' + path
            (OUT / Path(path).name).write_bytes(b)
            if path.endswith('.lean'):
                with (scratch / Path(path).name).open('xb') as f:
                    f.write(b)
        contract = types.ModuleType('pinned_contract')
        cb = (OUT / 'neumann_integer_block_image_average_repro_contract.py').read_bytes()
        exec(compile(cb, 'pinned_contract', 'exec'), contract.__dict__)
        repro = contract.make_repro({p: (OUT / Path(p).name).read_bytes() for p in contract.INPUTS})
        assert sha(repro) == '84ff17cff6c72d0bd532e617adcbed7398580b59a8fa88ebf926b19038565f76', 'REPRO_HASH'
        (OUT / 'mathlib-repro.lean').write_bytes(repro)
        with (scratch / 'mathlib-repro.lean').open('xb') as f:
            f.write(repro)
        for path in contract.INPUTS[1:]:
            assert sha((ROOT / path).read_bytes()) == PINS[path], 'BASE_SOURCE_CHANGED=' + path
        gate = types.ModuleType('pinned_gate')
        gb = (OUT / 'full_green_owner_exact_axiom_gate.py').read_bytes()
        exec(compile(gb, 'pinned_gate', 'exec'), gate.__dict__)
        gate.self_test()
        for stage, path in [('mathlib_repro', 'mathlib-repro.lean'),
                            ('physical_draft', 'NeumannIntegerBlockImageAverageDraft.lean')]:
            if stage == 'physical_draft':
                run('physical_prerequisites', ['lake', 'build', 'YangMills.RG.NeumannHalfCellBlockReflection', 'YangMills.RG.NeumannIntegerImageCountingKernel'], timeout=600)
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
            base_source=BASE, support_source=SUPPORT_SOURCE, cold_seal=False, pins=PINS, names=NAMES, records=records,
            axioms=axioms, outputs=outputs, parent_outer_sha256=PARENT_OUTER_SHA,
            scope='literal multidimensional image-family bijection, not image inverse'), sort_keys=True) + '\n')
        with tarfile.open(ARCHIVE, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(ARCHIVE), flush=True)
        print('ARCHIVE_SHA256=' + sha(ARCHIVE.read_bytes()), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
