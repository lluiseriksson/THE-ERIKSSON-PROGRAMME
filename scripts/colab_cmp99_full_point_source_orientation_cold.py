#!/usr/bin/env python3
"""Cold Colab diagnostic for the full Eq. (2.46) orientation queue.

This wrapper imports one hash-gated immutable copy of the retained-runtime
runner, reuses its exact source manifest, queue and axiom parser, but invokes
the base runner's fresh-checkout bootstrap.  The Colab runtime is retained at
the end so that a first real elaboration error can be repaired against the
materialized graph.  A PASS is cold compiler evidence for the listed source
checkpoint but does not by itself retire PRE-VALIDATION notices.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


HERE = Path("/content")
HOT_RUNNER = HERE / "colab_cmp99_full_point_source_orientation_hot_v6.py"
HOT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "0a8d75cdcf3e2d17779bb8661b8b9e50dd04a819/"
    "scripts/colab_cmp99_full_point_source_mixed_domain_retained_hot.py"
)
HOT_RUNNER_SHA256 = (
    "a45b8af72656116d518cfc7c8bcf97fee17e5a00a3958e3841f056130a6a9dbd"
)

with urllib.request.urlopen(HOT_RUNNER_URL, timeout=60) as response:
    hot_runner_source = response.read()
hot_runner_hash = hashlib.sha256(hot_runner_source).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + hot_runner_hash, flush=True)
if hot_runner_hash != HOT_RUNNER_SHA256:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
HOT_RUNNER.write_bytes(hot_runner_source)

spec = importlib.util.spec_from_file_location(
    "cmp99_full_point_source_orientation_hot_v6", HOT_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load hot runner: {HOT_RUNNER}")
hot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(hot)
runner = hot.runner

runner.RUNNER_REV = "cmp99-full-point-source-orientation-cold-v2"
runner.ROOT = Path("/content/hrpoly-cmp99-full-point-source-orientation-cold-v2")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-full-point-source-orientation-cold-v2-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-full-point-source-orientation-cold-v2-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-full-point-source-orientation-cold-v2-paths.txt"
)


if __name__ == "__main__":
    saved_unassign = None
    try:
        from google.colab import runtime

        saved_unassign = runtime.unassign
        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_FOR_BOUNDED_DEBUG=1", flush=True
        )
    except ImportError:
        pass
    try:
        raise SystemExit(runner.main())
    finally:
        if saved_unassign is not None:
            from google.colab import runtime

            runtime.unassign = saved_unassign
