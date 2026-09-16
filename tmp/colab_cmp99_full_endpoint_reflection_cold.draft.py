#!/usr/bin/env python3
"""Fresh-checkout cold gate for endpoint reflection and owner orientation.

This wrapper imports one immutable, hash-gated copy of the retained-runtime
runner and invokes the underlying fresh-checkout bootstrap.  It must only be
promoted after the exact hot queue has passed.  The runtime is retained at
the end solely for one bounded first-error repair.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


HERE = Path("/content")
HOT_RUNNER = HERE / "colab_cmp99_full_endpoint_reflection_retained_hot_v2.py"
HOT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "71b47b53/"
    "scripts/colab_cmp99_full_endpoint_reflection_retained_hot.py"
)
HOT_RUNNER_SHA256 = (
    "262e1daa07610a2d93cef65e327165d24d8b2819501d2e1d4c271e66ece5033b"
)

with urllib.request.urlopen(HOT_RUNNER_URL, timeout=60) as response:
    hot_runner_source = response.read()
hot_runner_hash = hashlib.sha256(hot_runner_source).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + hot_runner_hash, flush=True)
if hot_runner_hash != HOT_RUNNER_SHA256:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
HOT_RUNNER.write_bytes(hot_runner_source)

spec = importlib.util.spec_from_file_location(
    "cmp99_full_endpoint_reflection_retained_hot_v2", HOT_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load hot runner: {HOT_RUNNER}")
hot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(hot)
runner = hot.runner

runner.RUNNER_REV = "cmp99-full-endpoint-reflection-cold-v1"
runner.ROOT = Path("/content/hrpoly-cmp99-full-endpoint-reflection-cold-v1")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-full-endpoint-reflection-cold-v1-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-full-endpoint-reflection-cold-v1-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-full-endpoint-reflection-cold-v1-paths.txt"
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
