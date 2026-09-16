#!/usr/bin/env python3
"""Fresh Colab gate for both source-carrier C6d ambient Green branches.

This runner validates the positive- and zero-depth source/audit pairs, all
twenty-five public axiom readouts and every repository consumer through
the repaired canonical-completion consumer and every remaining repository
consumer through ``YangMillsCore``.  Passing
does not attain window 15, move ``20/41`` or inhabit ``TermSource``.
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

runner.RUNNER_REV = "c6d-source-separated-ambient-green-v4"
runner.SOURCE_SHA = '7e90203e8bfd1deb58d998fb5cdad0baab925af5'
runner.ROOT = Path("/content/hrpoly-c6d-source-separated-ambient-green")
runner.EVIDENCE = Path("/content/hrpoly-c6d-source-separated-ambient-green-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-c6d-source-separated-ambient-green-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-c6d-source-separated-ambient-green-paths.txt"
)
runner.SOURCE_BLOBS = {
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen.lean': 'eaf8561ebd61df8332b1bfa30d5ef524a8fe2065eb781cad6205a152cba972e7',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenAudit.lean': '7713f038fd95e52cfe694c23770912d2498ff7222bc935f91f03f6a9865c0893',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepth.lean': '6ca49eff15ce182b89dd515eb742fcd9cd2c6b5f094a964b0e778a8acdd430cb',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthAudit.lean': '621e01eda7ad5a74d120da2cad97d11fb076a76aed1f89bb6b7cc4f4f0bd82c4',
    'YangMills/RG/BalabanCMP99Eq360C6dCanonicalAmbientCompletion.lean': 'c93a2dc1485bdaef6c3ba039250412cfc64314b369112e21d89eaa3870b099ea',
    'YangMills/RG/BalabanCMP99Eq360C6dCanonicalAmbientCompletionAudit.lean': '9c83decedb2f05184b23344694978314da26350ccdd670ded383b27c80c6ccda',
    'YangMillsCore.lean': '1f3a1dc00cfb8705d2abb803e2ff2718bcd45bdd136b93e013034a075b890434',
}
runner.QUEUE = [
    (
        '01_cmp99eq360c6dsourceseparatedambientgreen_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen'],
        None,
    ),
    (
        '01_cmp99eq360c6dsourceseparatedambientgreen_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenAudit.lean'],
        15,
    ),
    (
        '02_cmp99eq360c6dsourceseparatedambientgreenzerodepth_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepth'],
        None,
    ),
    (
        '02_cmp99eq360c6dsourceseparatedambientgreenzerodepth_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthAudit.lean'],
        10,
    ),
    (
        '03_cmp99eq360c6dcanonicalambientcompletion_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dCanonicalAmbientCompletion'],
        None,
    ),
    (
        '03_cmp99eq360c6dcanonicalambientcompletion_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dCanonicalAmbientCompletionAudit.lean'],
        2,
    ),
    (
        '04_c6d_source_green_yang_mills_core_root',
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
