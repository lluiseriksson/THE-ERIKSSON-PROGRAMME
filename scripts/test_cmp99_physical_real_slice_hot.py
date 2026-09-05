"""Small synthetic tests of the physical real-slice runner; NEVER runs Lean.

Every subprocess and HTTPS response is replaced by an explicit fixture.
Fake output bytes are labelled SYNTHETIC_NOT_LEAN. These tests establish
only control flow, first-error preservation and evidence bookkeeping.
"""
from __future__ import annotations
import contextlib
import ctypes
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import time
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
QUEUE = ['verify_cold_evidence', 'retained_head', 'retained_clean', 'mathlib_pin',
         'text_guard', 'import_guard', 'mathlib_carrier_repro',
         'physical_prerequisites', 'physical_real_slice_draft', 'final_clean']


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def one_case(case):
    spec = importlib.util.spec_from_file_location('synthetic_runner_' + case,
        HERE / 'colab_cmp99_physical_real_slice_hot.py')
    runner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runner)
    with tempfile.TemporaryDirectory(prefix='f5-synthetic-') as temporary:
        base = Path(temporary)
        runner.ROOT, runner.LOGS = base / 'root', base / 'logs'
        runner.HELPERS, runner.COLD_ARCHIVE = base / 'helpers', base / 'cold.tar.gz'
        runner.ROOT.mkdir()
        runner.HELPERS.mkdir()
        cold = b'SYNTHETIC_COLD_ARCHIVE_NOT_COMPILATION_EVIDENCE'
        runner.COLD_ARCHIVE.write_bytes(cold)
        cold_hash = sha(cold)
        launch = dict(status='FAIL' if case == 'cold_fail' else 'PASS',
            source=runner.COLD_SOURCE, revision='cmp99-point-fibre-promoted-cold-v1')
        (runner.HELPERS / 'launch-final-status.json').write_text(json.dumps(launch))
        helpers = {
            'verify_cmp99_point_fibre_promoted_cold.py': b'# synthetic verifier fixture',
            'verify_cmp99_full_green_residue_cold.py': b'# synthetic helper fixture',
            'full_green_owner_exact_axiom_gate.py':
                (HERE / 'full_green_owner_exact_axiom_gate.py').read_bytes(),
        }
        runner.HELPER_HASHES = {name: sha(blob) for name, blob in helpers.items()}
        for name, blob in helpers.items():
            (runner.HELPERS / name).write_bytes(blob)
        fixtures = {path: ('-- SYNTHETIC SOURCE FIXTURE ' + path).encode()
                    for path in runner.BLOBS}
        runner.BLOBS = {path: sha(blob) for path, blob in fixtures.items()}
        calls = []

        def fake_urlopen(url, timeout):
            assert timeout == 60
            match = [blob for path, blob in fixtures.items() if url.endswith('/' + path)]
            assert len(match) == 1
            return io.BytesIO(match[0])

        def fake_run(command, *, cwd, stdout, stderr):
            assert Path(cwd) == runner.ROOT and stderr == subprocess.STDOUT
            stage = QUEUE[len(calls)]
            calls.append(stage)
            raw, code = b'', 0
            if stage == 'verify_cold_evidence':
                assert command[0] == sys.executable and '--sha256' in command
                assert command[command.index('--sha256') + 1] == cold_hash
                raw = b'SYNTHETIC_VERIFIER_ONLY\n'
                if case == 'verifier_fail':
                    raw, code = b'SYNTHETIC_FIRST_ERROR_VERIFIER\n', 9
            elif stage == 'retained_head':
                raw = (runner.COLD_SOURCE + '\n').encode()
            elif stage == 'mathlib_pin':
                raw = b'07642720480157414db592fa85b626dafb71355b\n'
            elif stage in ('mathlib_carrier_repro', 'physical_real_slice_draft'):
                assert command[:3] == ['lake', 'env', 'lean']
                if stage == 'mathlib_carrier_repro' and case == 'repro_fail':
                    raw, code = b'SYNTHETIC_FIRST_ERROR_REPRO\n', 7
                else:
                    if not (stage == 'physical_real_slice_draft' and case == 'missing_output'):
                        Path(command[command.index('-o') + 1]).write_bytes(b'SYNTHETIC_NOT_LEAN')
                    if stage == 'physical_real_slice_draft':
                        raw = '\n'.join("'" + name +
                            "' depends on axioms: [propext, Classical.choice, Quot.sound]"
                            for name in sorted(runner.EXPECTED)).encode()
                        if case == 'forbidden_axiom':
                            raw = raw.replace(b'Quot.sound', b'sorryAx', 1)
            elif stage == 'physical_prerequisites':
                assert command[:2] == ['lake', 'build']
                raw = b'SYNTHETIC_PREREQUISITES_ONLY\n'
            stdout.write(raw)
            return subprocess.CompletedProcess(command, code)

        if case == 'duplicate_start':
            runner.LOGS.mkdir()
        digest = '0' * 64 if case == 'cold_hash' else cold_hash
        capture = io.StringIO()
        with patch.object(sys, 'argv', ['synthetic-test', '--cold-archive-sha256', digest]), \
             patch.object(runner.subprocess, 'run', side_effect=fake_run), \
             patch.object(runner.urllib.request, 'urlopen', side_effect=fake_urlopen), \
             patch.dict(os.environ), contextlib.redirect_stdout(capture):
            if case == 'duplicate_start':
                try:
                    runner.main()
                except RuntimeError as error:
                    assert str(error) == 'ALREADY_STARTED_NO_REEXECUTION'
                    assert not calls
                    return
                raise AssertionError('DUPLICATE_START_ACCEPTED')
            result = runner.main()
        evidence = json.loads((runner.LOGS / 'debug-evidence.json').read_text())
        assert evidence['cold_seal'] is False
        assert evidence['status'] == ('PASS' if case == 'pass' else 'FAIL')
        assert result == (0 if case == 'pass' else 1)
        assert [record['stage'] for record in evidence['records']] == calls
        for record in evidence['records']:
            assert record['seconds'] >= 0
            assert sha((runner.LOGS / record['log']).read_bytes()) == record['sha256']
        for name, digest in evidence['files'].items():
            assert sha((runner.LOGS / name).read_bytes()) == digest
        with tarfile.open(str(runner.LOGS) + '.tar.gz') as archive:
            names = {m.name for m in archive.getmembers() if m.isfile()}
            assert names == {'logs/' + n for n in evidence['files']} | {'logs/debug-evidence.json'}
        if case == 'pass':
            assert calls == QUEUE and len(evidence['axioms']) == 4
            assert len(evidence['compiled_output_hashes']) == 2
        elif case in ('cold_fail', 'cold_hash'):
            assert calls == []
        elif case == 'verifier_fail':
            assert calls == QUEUE[:1] and evidence['records'][-1]['exit'] == 9
            assert evidence['error'] == "RuntimeError('FIRST_ERROR=verify_cold_evidence')"
        elif case == 'repro_fail':
            assert calls == QUEUE[:7] and evidence['records'][-1]['exit'] == 7
            assert evidence['error'] == "RuntimeError('FIRST_ERROR=mathlib_carrier_repro')"
        elif case in ('forbidden_axiom', 'missing_output'):
            assert calls == QUEUE[:9]
            assert 'HOT_DEBUG_STATUS=PASS' not in capture.getvalue()


def main():
    start = time.perf_counter()
    cases = ['pass', 'cold_fail', 'cold_hash', 'verifier_fail', 'repro_fail',
             'forbidden_axiom', 'missing_output', 'duplicate_start']
    for case in cases:
        one_case(case)
    print('PHYSICAL_REAL_SLICE_RUNNER_SYNTHETIC_TEST=PASS cases=' + str(len(cases)))
    print('REAL_SUBPROCESS_CALLS=0 REAL_NETWORK_CALLS=0 LEAN_EVIDENCE=0')
    print('seconds=' + str(time.perf_counter() - start))
    if os.name == 'nt':
        class PMC(ctypes.Structure):
            _fields_ = [('cb', ctypes.c_ulong), ('faults', ctypes.c_ulong)] + [
                (n, ctypes.c_size_t) for n in ('peak_rss', 'rss', 'peak_page', 'page',
                    'peak_nonpage', 'nonpage', 'pagefile', 'peak_pagefile')]
        memory = PMC()
        memory.cb = ctypes.sizeof(memory)
        ok = ctypes.windll.psapi.GetProcessMemoryInfo(ctypes.c_void_p(-1),
            ctypes.byref(memory), memory.cb)
        assert ok
        print('peak_rss=' + str(memory.peak_rss))


if __name__ == '__main__':
    main()
