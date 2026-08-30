#!/usr/bin/env python3
"""Fresh Colab gate for the CMP89 centered rectangular representative.

The source checkpoint constructs the coordinatewise representative and carry
for the literal periods ``2*m_mu`` and identifies the reflected magnitude with
the printed two-endpoint minimum.  Passing is infrastructure toward uniform
regional ``B0, delta0`` only: it does not move ``20/41``, attain window 15, or
instantiate ``TermSource``.
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
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "bcc852cee5e709bff91fad7de26fa21cff754e1f/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)

with urllib.request.urlopen(BASE_RUNNER_URL) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)

spec = importlib.util.spec_from_file_location(
    "cmp89_neumann_centered_rectangular_base", BASE_RUNNER
)
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
runner.RUNNER_REV = "cmp89-neumann-centered-rectangular-v1"
runner.SOURCE_SHA = "5b6e0b6d661f5b0b0fdf9bad851d6cfbf522be11"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-centered-rectangular")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-neumann-centered-rectangular-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-neumann-centered-rectangular-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-neumann-centered-rectangular-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89NeumannCenteredRectangularRepresentative.lean":
        "68065abe412aebf34e6020d4bd92a73233c2111c740880ac817088ccd4079b22",
    "YangMills/RG/BalabanCMP89NeumannCenteredRectangularRepresentativeAudit.lean":
        "f05bcb77249ccd0e53c7dde66b6908fd2b3a9564220902850a922b1e2664a645",
}
runner.QUEUE = [
    (
        "01_cmp89_neumann_centered_rectangular_representative_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP89NeumannCenteredRectangularRepresentative",
        ],
        None,
    ),
    (
        "01_cmp89_neumann_centered_rectangular_representative_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/"
            "BalabanCMP89NeumannCenteredRectangularRepresentativeAudit.lean",
        ],
        10,
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
