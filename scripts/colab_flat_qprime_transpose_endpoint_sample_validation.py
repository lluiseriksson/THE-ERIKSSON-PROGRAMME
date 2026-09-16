#!/usr/bin/env python3
"""Colab diagnostic gate for the row-oriented endpoint sample normal form.

The immutable mathematical source is ``SOURCE_SHA``.  This runner reuses the
fresh-clone transport, exact pin gates, robust axiom parser, evidence archive,
and runtime release protocol.  A Mathlib-only repro checks the two algebraic
rewrites before the expensive project focal.

Honest scope: this does not identify row and column amplitudes, reindex through
cross-fibre Fourier negation, periodize a Green integrand, construct regional
``B0``, attain window 15 or discharge a terminal field.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
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
SPEC = importlib.util.spec_from_file_location(
    "flat_qprime_transpose_endpoint_sample_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-flat-qprime-transpose-endpoint-sample-v1"
runner.SOURCE_SHA = "62862316ed330ef0efa8db676fa3b3f97b441c6e"
runner.ROOT = Path("/content/hrpoly-flat-qprime-transpose-endpoint-sample")
runner.EVIDENCE = Path(
    "/content/hrpoly-flat-qprime-transpose-endpoint-sample-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-flat-qprime-transpose-endpoint-sample-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-flat-qprime-transpose-endpoint-sample-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatQprimeTransposeEndpointSample.lean":
        "bb7fb89b9366d99eaed0f98105f64a628c562657bc9b54f94f542a29b4415012",
    "YangMills/RG/BalabanCMP99SourceFlatQprimeTransposeEndpointSampleAudit.lean":
        "9bc50c439e007be0024db76ee5a807d67689710a2c7d652aa3f0b06cc2965b2a",
}

REPRO = HERE / "flat_qprime_transpose_endpoint_sample_repro.lean"
REPRO.write_text(
    """import Mathlib

open scoped BigOperators

example (a b c : ℂ) : (a * b) * c = (a * c) * b := by
  ring

example {ι : Type*} [Fintype ι] (f : ι → ℂ) (a : ℂ) :
    (∑ i, f i) * a = ∑ i, f i * a := by
  rw [Finset.sum_mul]
""",
    encoding="utf-8",
)

runner.QUEUE = [
    (
        "flat_qprime_transpose_endpoint_sample_repro",
        ["lake", "env", "lean", str(REPRO)],
        None,
    ),
    (
        "flat_qprime_transpose_endpoint_sample_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceFlatQprimeTransposeEndpointSample",
        ],
        None,
    ),
    (
        "flat_qprime_transpose_endpoint_sample_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/"
            "BalabanCMP99SourceFlatQprimeTransposeEndpointSampleAudit.lean",
        ],
        3,
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
    raise SystemExit(runner.main())
