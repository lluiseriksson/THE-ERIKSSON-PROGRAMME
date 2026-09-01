#!/usr/bin/env python3
"""Hot-debug only the first failing CMP89 three-species target.

This wrapper deliberately reuses the exact v5 runner and source checkpoint
whose durable evidence stopped at ``neumann_precision_three_species_focal``.
It removes the already-green mass stages so that the next Colab session
reports the first real error without repeating unrelated focal work.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


HERE = Path("/content")
BASE_RUNNER = HERE / "colab_cmp89_physical_neumann_inverse_producer_debug_v5.py"
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "17d73a00c05e7324bba6aa21528b09beaae97884/"
    "scripts/colab_cmp89_physical_neumann_inverse_producer_debug.py"
)
BASE_RUNNER_SHA256 = (
    "33a4b2d1b1ee424882d3d9e4f760ea61110d8871257bcf3d907ecf49baec0a24"
)


with urllib.request.urlopen(BASE_RUNNER_URL, timeout=60) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)

spec = importlib.util.spec_from_file_location(
    "cmp89_physical_neumann_inverse_producer_debug_v5", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)

runner = gate.runner
runner.RUNNER_REV = "cmp89-neumann-three-species-debug-v1"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-three-species-debug-v1")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-neumann-three-species-debug-v1-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-neumann-three-species-debug-v1-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-neumann-three-species-debug-v1-paths.txt"
)
runner.QUEUE = gate.runner.QUEUE[2:4]


if __name__ == "__main__":
    try:
        from google.colab import runtime

        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_FOR_DEBUG=1", flush=True
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
