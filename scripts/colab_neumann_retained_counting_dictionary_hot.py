"""One retained-runtime diagnostic, only after independently verified v2 PASS.

No checkout change, background pool, CI, cold-seal claim or silent retry.
The input file depends only on already published production modules.
Prepared before the prerequisite completes; not permission to run concurrently.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tarfile
import time
import types
import urllib.request

BASE = '06a928178b22c42c4ecc5387461b808ee3a19dea'
SOURCE = '214b6923f3523d44282d5772fa6ab09782864f10'
PRODUCTION_TREE = 'd60f95120f11de18d0d3e3a73e90c9b59db07f05'
ROOT = Path('/content/hrpoly-neumann-generated-counting-reflection-diagnostic-v2')
WORK = Path('/content/neumann-retained-counting-dictionary-hot-v1')
INPUT = ROOT / 'tmp' / 'neumann_retained_counting_dictionary_hot_v1'
PRIOR = Path('/content/neumann-generated-counting-reflection-diagnostic-v2-preservation-20260906.tar.gz')
NAME = 'NeumannRetainedCountingMassDictionaryDraft.lean'
BLOB = '6f8a5be71b33261c263291b9049337ed068f1aee282f7eb1482b264bcd91e7f6'
VERIFIER_SOURCE = '160ff087d55125a7a0f6f22f8b94c2e21a9336fa'
VERIFIER_HASH = 'a596e50eb708d39819da3f15557fa5705ab564874b70d9913f8a8b9794bec851'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
MATHLIB = '07642720480157414db592fa85b626dafb71355b'
EXPECTED = {
    'YangMills.RG.neumannFlatGeneratedCountingMass_eq_explicit_draft',
    'YangMills.RG.neumannFlatRetainedTerminalCountingMass_eq_explicit_draft',
}
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def download(commit, relative, expected, destination):
    url = RAW + commit + '/' + relative
    with urllib.request.urlopen(url, timeout=60) as response:
        data = response.read()
    assert hashlib.sha256(data).hexdigest() == expected, 'TRANSPORT_HASH=' + relative
    destination.write_bytes(data)
    return dict(url=url, sha256=expected, bytes=len(data))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--prior-sha256', required=True)
    args = parser.parse_args()
    assert re.fullmatch('[0-9a-fA-F]{64}', args.prior_sha256), 'PRIOR_DIGEST_FORMAT'
    prior_hash = args.prior_sha256.lower()
    assert ROOT.is_dir() and PRIOR.is_file(), 'PRIOR_RUNTIME_OR_ARCHIVE_ABSENT'
    assert not WORK.exists() and not INPUT.exists(), 'ALREADY_STARTED_NO_REEXECUTION'
    assert digest(PRIOR) == prior_hash, 'PRIOR_ARCHIVE_HASH'
    WORK.mkdir()
    (WORK / 'runner.py').write_bytes(Path(__file__).read_bytes())
    records, transports = [], []
    status, error, axioms = 'FAIL', None, None
    opened = datetime.datetime.now(datetime.timezone.utc).isoformat()

    def run(stage, command, timeout=60, cwd=ROOT):
        log = WORK / (stage + '.log')
        started = time.perf_counter()
        timed_out = False
        print('STAGE=' + stage + ' CMD=' + json.dumps(command), flush=True)
        with log.open('xb') as out:
            child = subprocess.Popen(command, cwd=cwd, stdout=out,
                stderr=subprocess.STDOUT, start_new_session=True)
            print('CHILD_PID=' + str(child.pid), flush=True)
            try:
                child.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
        record = dict(stage=stage, command=command, cwd=str(cwd),
            exit=child.returncode, timed_out=timed_out,
            seconds=time.perf_counter() - started, log_sha256=digest(log))
        records.append(record)
        temp = WORK / 'records.tmp'
        temp.write_text(json.dumps(records, sort_keys=True) + '\n')
        temp.replace(WORK / 'records.json')
        print(json.dumps(record, sort_keys=True), flush=True)
        print(log.read_text(errors='replace'), flush=True)
        assert child.returncode == 0 and not timed_out, 'FIRST_ERROR=' + stage
        return log.read_text()

    try:
        helper = ROOT / 'scripts' / 'full_green_owner_exact_axiom_gate.py'
        assert digest(helper) == GATE_HASH, 'AXIOM_HELPER'
        (WORK / helper.name).write_bytes(helper.read_bytes())
        verifier = WORK / 'verify_neumann_counting_reflection_diagnostic_v2.py'
        transports.append(download(VERIFIER_SOURCE,
            'scripts/verify_neumann_counting_reflection_diagnostic_v2.py',
            VERIFIER_HASH, verifier))
        run('verify_prior', [sys.executable, str(verifier), '--archive', str(PRIOR),
            '--sha256', prior_hash, '--axiom-helper', str(helper)])
        # Verify a terminal archive, not a lock file or a success prefix. A prior
        # output hash is still not permission to mutate its checkout or artifacts.
        import psutil
        assert psutil.virtual_memory().total / 2**30 >= 40, 'HIGH_RAM_REQUIRED'
        assert not Path('/dev/nvidia0').exists(), 'GPU_NOT_AUTHORIZED'
        active = [(p.pid, p.info['name']) for p in psutil.process_iter(['name'])
            if p.info['name'] in {'lean', 'lake'}]
        assert not active, 'EXISTING_LEAN_LAKE_NO_PARALLEL=' + repr(active)
        assert run('base_head', ['git', 'rev-parse', 'HEAD']).strip() == BASE, 'BASE_SHA'
        assert run('production_tree', ['git', 'rev-parse', 'HEAD:YangMills']).strip() == PRODUCTION_TREE, 'PRODUCTION_TREE'
        run('clean_source', ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        assert run('mathlib_pin', ['git', '-C', '.lake/packages/mathlib',
            'rev-parse', 'HEAD']).strip() == MATHLIB, 'MATHLIB_PIN'
        bindir = Path('/content/lean-4.29.0-rc6-linux/lean-4.29.0-rc6-linux/bin')
        assert (bindir / 'lean').is_file() and (bindir / 'lake').is_file(), 'PINNED_BIN_ABSENT'
        os.environ['PATH'] = str(bindir) + ':' + os.environ['PATH']
        for program in ('lean', 'lake'):
            assert '4.29.0-rc6' in run(program + '_version', [str(bindir / program), '--version']), 'VERSION'
        (WORK / 'toolchain-binaries.json').write_text(json.dumps(
            {p: digest(bindir / p) for p in ('lean', 'lake')}, sort_keys=True) + '\n')
        INPUT.mkdir(parents=True, exist_ok=False)
        transports.append(download(SOURCE, 'tmp/' + NAME, BLOB, WORK / NAME))
        (INPUT / NAME).write_bytes((WORK / NAME).read_bytes())
        manifest = WORK / 'paths.txt'
        relative = str((INPUT / NAME).relative_to(ROOT))
        manifest.write_text(relative + '\n')
        run('text_guard', [sys.executable, 'scripts/check_lean_overlay_text.py',
            '--paths-from', str(manifest), '--require-prevalidation'])
        run('import_guard', [sys.executable, 'scripts/check_lean_import_prefix.py', relative])
        run('prerequisites', ['lake', 'build',
            'YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalPrecisionKernel',
            'YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge'], timeout=1800)
        output = run('retained_counting_dictionary', ['lake', 'env', 'lean', '-o',
            str(WORK / 'draft.olean'), relative], timeout=180)
        gate = types.ModuleType('pinned_gate')
        exec(compile(helper.read_bytes(), str(helper), 'exec'), gate.__dict__)
        axioms = gate.exact_axioms(output, EXPECTED)
        assert (WORK / 'draft.olean').is_file(), 'OUTPUT_ABSENT'
        assert digest(PRIOR) == prior_hash, 'PRIOR_CHANGED'
        assert digest(INPUT / NAME) == BLOB, 'INPUT_CHANGED'
        run('final_clean_source', ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        status = 'PASS'
    except Exception as exc:
        error = repr(exc)
        print('FIRST_ERROR=' + error, flush=True)
    report = dict(status=status, cold_seal=False, base=BASE, source=SOURCE,
        source_blob=BLOB, production_tree=PRODUCTION_TREE, opened_utc=opened,
        prior_sha256=prior_hash, transports=transports, records=records,
        axioms=axioms, error=error,
        scope='retained terminal counting mass only; no Neumann inverse or window15',
        files={p.name: digest(p) for p in WORK.iterdir() if p.is_file()})
    temp = WORK / 'evidence.tmp'
    temp.write_text(json.dumps(report, sort_keys=True) + '\n')
    temp.replace(WORK / 'evidence.json')
    archive = Path(str(WORK) + '.tar.gz')
    with tarfile.open(archive, 'w:gz') as tar:
        tar.add(WORK, arcname=WORK.name)
    print('ARCHIVE=' + str(archive) + ' SHA256=' + digest(archive), flush=True)
    print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
