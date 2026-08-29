#!/usr/bin/env python3
"""Fresh Colab gate for the exact post-Green localization prefix.

This runner validates the literal full-companion precision localization
and all three named metric transports, their ten public axiom readouts,
and every repository consumer through ``YangMillsCore``. Passing is only
the D1/metric prefix: it does not yet prove the regional Green decay, the
four actions, uniform B0/delta0, window 15, ``20/41`` or ``TermSource``.

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

runner.RUNNER_REV = "c6d-post-green-decay-prefix-v1"
runner.SOURCE_SHA = 'a554cba0c398e816316e53d76a4fe08bf379d931'
runner.ROOT = Path("/content/hrpoly-c6d-post-green-decay-prefix")
runner.EVIDENCE = Path("/content/hrpoly-c6d-post-green-decay-prefix-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-c6d-post-green-decay-prefix-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-c6d-post-green-decay-prefix-paths.txt"
)
runner.SOURCE_BLOBS = {
    'YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionPrecisionDecay.lean': '3d8ede2d5ac4338059ee5d85ba8aeb0451fcb0cf9239e334851187f6ab1ab546',
    'YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionPrecisionDecayAudit.lean': 'd1d6a72f3b7d1cf0aabe0c02de6e94c614a30e6c765c90cfaf6680706ed09f4b',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientMetric.lean': 'e91471c2ae3d4c4e5784d1019c53a2455db1e8511ab9f98a9974d0799f2baf0c',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientMetricAudit.lean': '112366cc294f363d1eaeeb497ffa2976225112f088b57b62718c1051191ef8d1',
    'YangMillsCore.lean': '7ccf4f698d9c755218e6ca97ee3f56a8e0ed7f97988a0cedb8c77161aaf52c2f',
}
runner.QUEUE = [
    (
        '01_cmp99sourceactiveregionfullcompanionprecisiondecay_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanionPrecisionDecay'],
        None,
    ),
    (
        '01_cmp99sourceactiveregionfullcompanionprecisiondecay_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionPrecisionDecayAudit.lean'],
        7,
    ),
    (
        '02_cmp99eq360c6dsourceseparatedambientmetric_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientMetric'],
        None,
    ),
    (
        '02_cmp99eq360c6dsourceseparatedambientmetric_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientMetricAudit.lean'],
        3,
    ),
    (
        '03_c6d_post_green_decay_prefix_yang_mills_core_root',
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
