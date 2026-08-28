#!/usr/bin/env python3
"""Fresh Colab gate for canonical regional ambient completion.

This runner validates one source/audit pair, all nine public axiom
readouts and every repository consumer through ``YangMillsCore``.
Passing closes only the carrier/inverse adapter; it does not prove the
four actions, attain window 15, move ``20/41`` or inhabit ``TermSource``.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import subprocess
import time
import urllib.request

HERE = Path("/content")
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
BASE_RUNNER_URL = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/bcc852cee5e709bff91fad7de26fa21cff754e1f/scripts/colab_qprime_row_validation.py'
BASE_RUNNER_SHA256 = 'd06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee'
with urllib.request.urlopen(BASE_RUNNER_URL) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location("c6d_source_green_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def streaming_run(stage, command, cwd=None):
    print("STAGE=" + stage + " CMD=" + repr(command), flush=True)
    started = time.perf_counter()
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    stdout_path = runner.EVIDENCE / (
        f"{len(runner.RECORDS):03d}-{stage}.stdout"
    )
    with stdout_path.open("w", encoding="utf-8", newline="\n") as stream:
        child = subprocess.Popen(
            command,
            cwd=cwd,
            text=True,
            stdout=stream,
            stderr=subprocess.STDOUT,
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
                        "STAGE=" + stage + " HEARTBEAT_SECONDS=%.3f"
                        % (now - started),
                        flush=True,
                    )
                    next_heartbeat = now + 30
    elapsed = time.perf_counter() - started
    output = stdout_path.read_text(encoding="utf-8")
    print(output, flush=True)
    runner.RECORDS.append({
        "stage": stage,
        "exit": returncode,
        "seconds": elapsed,
        "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
    })
    print(
        "STAGE=" + stage + " EXIT=" + str(returncode)
        + " SECONDS=%.3f" % elapsed,
        flush=True,
    )
    if returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


runner.run = streaming_run

runner.RUNNER_REV = "c6d-canonical-ambient-completion-v1"
runner.SOURCE_SHA = 'f987504bb338c1366691facf9ab6ce4ddaec1c60'
runner.ROOT = Path("/content/hrpoly-c6d-canonical-ambient-completion")
runner.EVIDENCE = Path("/content/hrpoly-c6d-canonical-ambient-completion-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-c6d-canonical-ambient-completion-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-c6d-canonical-ambient-completion-paths.txt"
)
runner.SOURCE_BLOBS = {
    'YangMills/RG/BalabanCMP99ActiveRegionCanonicalAmbientCompletion.lean': 'acd97361c19ed9ffff3c5d040d6a52bf3ecf478849c9d13629d863cc5ceb28eb',
    'YangMills/RG/BalabanCMP99ActiveRegionCanonicalAmbientCompletionAudit.lean': 'ae2fe1641304bfa87933e40681075631bf986e54a2e5dc6ce3b0acf499d037c6',
    'YangMillsCore.lean': 'd84dbb8897ee2086004bad4d37eecfa035ba3e17a7106e0f45bd348dcb147471',
}
runner.QUEUE = [
    (
        '01_cmp99activeregioncanonicalambientcompletion_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99ActiveRegionCanonicalAmbientCompletion'],
        None,
    ),
    (
        '01_cmp99activeregioncanonicalambientcompletion_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99ActiveRegionCanonicalAmbientCompletionAudit.lean'],
        9,
    ),
    (
        '02_c6d_canonical_ambient_completion_yang_mills_core_root',
        ['lake', 'build', 'YangMillsCore'],
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
    try:
        from google.colab import files
        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    except Exception as error:
        print("EVIDENCE_DOWNLOAD_ERROR=" + repr(error), flush=True)
    raise SystemExit(runner_exit)
