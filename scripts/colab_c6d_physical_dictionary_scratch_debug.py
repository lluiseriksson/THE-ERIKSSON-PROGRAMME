#!/usr/bin/env python3
"""Retained diagnostic only for the C6d physical precision dictionary.

Passing this script is not a cold seal, does not remove PRE-VALIDATION and
does not move 20/41, attain window 15 or inhabit TermSource.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import subprocess
import time
import urllib.request


BASE_RUNNER = Path("/content/colab_qprime_row_validation.py")
BASE_RUNNER_URL = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/bcc852cee5e709bff91fad7de26fa21cff754e1f/scripts/colab_qprime_row_validation.py'
BASE_RUNNER_SHA256 = 'd06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee'
with urllib.request.urlopen(BASE_RUNNER_URL) as response:
    base_source = response.read()
if hashlib.sha256(base_source).hexdigest() != BASE_RUNNER_SHA256:
    raise RuntimeError("C6D_PHYSICAL_DICTIONARY_DEBUG_BASE_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("c6d_physical_dictionary_debug_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_PHYSICAL_DICTIONARY_DEBUG_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def streaming_run(stage, command, cwd=None):
    print("STAGE=" + stage + " CMD=" + repr(command), flush=True)
    started = time.perf_counter()
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    output_path = runner.EVIDENCE / f"{len(runner.RECORDS):03d}-{stage}.stdout"
    with output_path.open("w", encoding="utf-8", newline="\n") as stream:
        child = subprocess.Popen(
            command, cwd=cwd, text=True, stdout=stream, stderr=subprocess.STDOUT
        )
        next_heartbeat = started + 30
        while True:
            try:
                returncode = child.wait(timeout=1)
                break
            except subprocess.TimeoutExpired:
                now = time.perf_counter()
                if now >= next_heartbeat:
                    stream.flush()
                    print(
                        "STAGE=" + stage + " HEARTBEAT_SECONDS=%.3f" % (now - started),
                        flush=True,
                    )
                    next_heartbeat = now + 30
    seconds = time.perf_counter() - started
    output = output_path.read_text(encoding="utf-8")
    print(output, flush=True)
    runner.RECORDS.append({
        "stage": stage,
        "exit": returncode,
        "seconds": seconds,
        "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
    })
    print(f"STAGE={stage} EXIT={returncode} SECONDS={seconds:.3f}", flush=True)
    if returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


runner.run = streaming_run
runner.RUNNER_REV = "c6d-physical-dictionary-scratch-debug-v1"
runner.SOURCE_SHA = 'b2ad8e04d50f7f4bdb5e5df914ba4a54571a5dc6'
runner.ROOT = Path("/content/hrpoly-c6d-physical-dictionary-debug")
runner.EVIDENCE = Path("/content/hrpoly-c6d-physical-dictionary-debug-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-physical-dictionary-debug-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-physical-dictionary-debug-paths.txt")
runner.SOURCE_BLOBS = {
    'tmp/FinitePiLpTypedKernelReindexRectangularAlgebra.draft.lean': '5cbdf2f61b74af319d1e7ffde5f2e56482aa94c7cf90ebb835b65d52152d4973',
    'tmp/BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackground.draft.lean': 'de492b6eae8015d3f74fd73010d56d531bb9e3df1ae7a7b945723f6c29fa4ea5',
    'tmp/BalabanCMP99Eq360C6dSourceSeparatedPhysicalPrecisionDictionary.draft.lean': '07ed3ba8be8cb3eec624747b516fe86f110d2070a45573ab83b08226958bd897',
}
runner.QUEUE = [
    (
        "01_c6d_physical_dictionary_warm_debug",
        [
            "python3", "tmp/run_c6d_physical_precision_dictionary_warm_debug.py",
            "--repo", str(runner.ROOT), "--source-sha", runner.SOURCE_SHA,
        ],
        None,
    ),
]


if __name__ == "__main__":
    try:
        from google.colab import runtime
        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    runner_exit = runner.main()
    print("RUNTIME_RETAINED_FOR_DEBUG=1", flush=True)
    raise SystemExit(runner_exit)
