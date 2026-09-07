#!/usr/bin/env python3
"""Fresh Colab gate for exact rectangular kernel-distance rescaling.

This runner validates one algebraic distance-rescaling theorem, its
single public axiom readout and every repository consumer through
``YangMillsCore``. Passing does not construct D2, any physical action,
uniform B0/delta0, window 15, move ``20/41`` or inhabit ``TermSource``.
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

runner.RUNNER_REV = "finite-pilp-distance-rescaling-v1"
runner.SOURCE_SHA = 'ebeea96235ac89a0a9598593855119d4bfe3ea04'
runner.ROOT = Path("/content/hrpoly-finite-pilp-distance-rescaling")
runner.EVIDENCE = Path("/content/hrpoly-finite-pilp-distance-rescaling-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-finite-pilp-distance-rescaling-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-finite-pilp-distance-rescaling-paths.txt"
)
runner.SOURCE_BLOBS = {
    'YangMills/RG/FinitePiLpTypedKernelDistanceRescaling.lean': '6b2428efc25d189135c6e6f59f5a830c2f8b1d0e53b500577ab8418a788105d4',
    'YangMills/RG/FinitePiLpTypedKernelDistanceRescalingAudit.lean': '71a7f44d4f332a3c611dcdbe0bf2748baa30de74490126d3e23c3553e958de48',
    'YangMillsCore.lean': '35c2f137d26219612850d9a03679ef2c50dad3ededa9fdb05a32021d3405c7f6',
}
runner.QUEUE = [
    (
        '01_finitepilptypedkerneldistancerescaling_focal',
        ['lake', 'build', 'YangMills.RG.FinitePiLpTypedKernelDistanceRescaling'],
        None,
    ),
    (
        '01_finitepilptypedkerneldistancerescaling_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/FinitePiLpTypedKernelDistanceRescalingAudit.lean'],
        1,
    ),
    (
        '02_finite_pilp_distance_rescaling_yang_mills_core_root',
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
