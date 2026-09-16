"""Bounded Mathlib repro after the exact promoted cold PASS; never a cold seal.

Reuses the retained checkout without changing tracked sources. One invocation,
one Lean child, no Lake build/bootstrap/retry. Archives real logs even on FAIL.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tarfile
import time
import types
import urllib.request

BASE = '9b73a5fe37d1e5e3c8589af211c46708a9d0a7bb'
SOURCE = 'd7e2199934a14c843d46cb08094c554bc9d0c5f1'
BLOB = '62c8ceb7502820740147bd678955e0ca529cceb6954bb350b4c0fbbcfc46a4d1'
NAME = 'NeumannIntegerImageBlockOwnerRepro.lean'
ROOT = Path('/content/hrpoly-neumann-counting-promoted-cold-v1')
WORK = Path('/content/neumann-integer-image-owner-hot-v1')
PRIOR = Path('/content/hrpoly-neumann-counting-promoted-cold-v1-evidence.tar.gz')
HELPERS = Path('/content/neumann-counting-promoted-cold-v1-launch')
PINS = {
    'verify_neumann_counting_promoted_cold.py': '9decd5ede386cf72c30c6a1909e545f852a68e8fad4801ba48674adbe0caf5c5',
    'verify_cmp99_full_green_residue_cold.py': '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c',
    'full_green_owner_exact_axiom_gate.py': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
}
NAMES = {'neumannIntegerHalfCellOwner_repro',
    'neumannIntegerTranslatedOwner_repro', 'neumannIntegerReflectedOwner_repro'}
MATHLIB = '07642720480157414db592fa85b626dafb71355b'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--prior-sha256', required=True)
    args = parser.parse_args()
    prior_hash = args.prior_sha256.lower()
    assert len(prior_hash) == 64 and all(c in '0123456789abcdef' for c in prior_hash)
    assert ROOT.is_dir() and PRIOR.is_file(), 'PRIOR_RUNTIME_ABSENT'
    assert not WORK.exists(), 'ALREADY_STARTED_NO_REEXECUTION'
    assert sha(PRIOR) == prior_hash, 'PRIOR_HASH'
    WORK.mkdir()
    (WORK / 'runner.py').write_bytes(Path(__file__).read_bytes())
    records, axioms, status, error = [], None, 'FAIL', None
    opened = datetime.datetime.now(datetime.timezone.utc).isoformat()

    def run(stage, command, timeout=60):
        log = WORK / (stage + '.log')
        started, timed_out = time.perf_counter(), False
        print('STAGE=' + stage + ' CMD=' + json.dumps(command), flush=True)
        with log.open('xb') as out:
            child = subprocess.Popen(command, cwd=ROOT, stdout=out,
                stderr=subprocess.STDOUT, start_new_session=True)
            print('CHILD_PID=' + str(child.pid), flush=True)
            try:
                child.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
        record = dict(stage=stage, command=command, cwd=str(ROOT),
            exit=child.returncode, timed_out=timed_out,
            seconds=time.perf_counter() - started, log_sha256=sha(log))
        records.append(record)
        temp = WORK / 'records.tmp'
        temp.write_text(json.dumps(records, sort_keys=True) + '\n')
        temp.replace(WORK / 'records.json')
        print(json.dumps(record, sort_keys=True), flush=True)
        output = log.read_text(errors='replace')
        print(output, flush=True)
        assert child.returncode == 0 and not timed_out, 'FIRST_ERROR=' + stage
        return output

    try:
        for name, digest in PINS.items():
            assert sha(HELPERS / name) == digest, 'HELPER_HASH=' + name
            (WORK / name).write_bytes((HELPERS / name).read_bytes())
        run('verify_cold_archive', [sys.executable,
            str(HELPERS / 'verify_neumann_counting_promoted_cold.py'),
            '--helpers', str(HELPERS), '--archive', str(PRIOR),
            '--sha256', prior_hash])
        import psutil
        assert psutil.virtual_memory().total / 2**30 >= 40, 'HIGH_RAM_REQUIRED'
        assert not Path('/dev/nvidia0').exists(), 'GPU_NOT_AUTHORIZED'
        assert not [p.pid for p in psutil.process_iter(['name'])
            if p.info['name'] in {'lean', 'lake'}], 'EXISTING_LEAN_LAKE'
        assert run('base_head', ['git', 'rev-parse', 'HEAD']).strip() == BASE, 'BASE_SHA'
        assert run('mathlib_pin', ['git', '-C', '.lake/packages/mathlib',
            'rev-parse', 'HEAD']).strip() == MATHLIB, 'MATHLIB_PIN'
        run('clean_source', ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        bindir = Path('/content/lean-4.29.0-rc6-linux/lean-4.29.0-rc6-linux/bin')
        assert (bindir / 'lake').is_file() and (bindir / 'lean').is_file(), 'PINNED_BIN_ABSENT'
        os.environ['PATH'] = str(bindir) + ':' + os.environ['PATH']
        for name in ('lean', 'lake'):
            assert '4.29.0-rc6' in run(name + '_version', [str(bindir / name), '--version'])
        (WORK / 'toolchain-binaries.json').write_text(json.dumps(
            {name: sha(bindir / name) for name in ('lean', 'lake')}, sort_keys=True) + '\n')
        url = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/' + SOURCE + '/tmp/' + NAME
        with urllib.request.urlopen(url, timeout=60) as response:
            blob = response.read()
        assert hashlib.sha256(blob).hexdigest() == BLOB, 'SOURCE_HASH'
        (WORK / NAME).write_bytes(blob)
        folder = ROOT / 'tmp' / 'neumann_integer_image_owner_hot_v1'
        folder.mkdir(parents=True, exist_ok=False)
        target = folder / NAME
        target.write_bytes(blob)
        relative = str(target.relative_to(ROOT))
        paths = WORK / 'paths.txt'
        paths.write_text(relative + '\n')
        run('text_guard', [sys.executable, 'scripts/check_lean_overlay_text.py',
            '--paths-from', str(paths), '--require-prevalidation'])
        run('import_guard', [sys.executable, 'scripts/check_lean_import_prefix.py', relative])
        output = run('integer_image_owner_repro', ['lake', 'env', 'lean',
            '-o', str(WORK / 'repro.olean'), relative], timeout=120)
        gate = types.ModuleType('pinned_gate')
        helper = WORK / 'full_green_owner_exact_axiom_gate.py'
        exec(compile(helper.read_bytes(), str(helper), 'exec'), gate.__dict__)
        axioms = gate.exact_axioms(output, NAMES)
        assert (WORK / 'repro.olean').is_file(), 'OUTPUT_ABSENT'
        assert sha(PRIOR) == prior_hash and sha(target) == BLOB, 'INPUT_CHANGED'
        run('final_clean_source', ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        status = 'PASS'
    except Exception as exc:
        error = repr(exc)
        print('FIRST_ERROR=' + error, flush=True)
    evidence = dict(status=status, cold_seal=False, source=SOURCE, source_blob=BLOB,
        base=BASE, prior_sha256=prior_hash, opened_utc=opened, records=records,
        axioms=axioms, error=error, scope='integer image block-owner arithmetic only; not Q kernel or inverse',
        files={p.name: sha(p) for p in WORK.iterdir() if p.is_file()})
    temp = WORK / 'evidence.tmp'
    temp.write_text(json.dumps(evidence, sort_keys=True) + '\n')
    temp.replace(WORK / 'evidence.json')
    archive = Path(str(WORK) + '.tar.gz')
    with tarfile.open(archive, 'w:gz') as tar:
        tar.add(WORK, arcname=WORK.name)
    print('ARCHIVE=' + str(archive) + ' SHA256=' + sha(archive), flush=True)
    print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
