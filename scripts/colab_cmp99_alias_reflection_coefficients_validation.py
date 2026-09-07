#!/usr/bin/env python3
"""Colab diagnostic gate for the alias-reflection coefficient bridge.

The immutable mathematical source is ``SOURCE_SHA``.  This runner reuses the
fresh-clone transport, exact pin gates, robust axiom parser, evidence archive,
and runtime release protocol.  A Mathlib-only repro checks the two elementary
algebraic orientations before the expensive project focal.

Honest scope: this is coefficient algebra only.  It does not identify the
stabilized denominator or solution, reindex a physical cross-fibre sum,
construct regional ``B0``, attain window 15 or discharge a terminal field.
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
    "cmp99_alias_reflection_coefficients_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-alias-reflection-coefficients-v3"
runner.SOURCE_SHA = "c669f5f5e081c316186bfbeade7a6a79752db418"
runner.ROOT = Path("/content/hrpoly-cmp99-alias-reflection-coefficients")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-alias-reflection-coefficients-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-alias-reflection-coefficients-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-alias-reflection-coefficients-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceAliasReflectionCoefficients.lean":
        "e2675eb46f47dad3fa60d0d88e29edd3f62ba6c5c8dc9f04d250343446a915f7",
    "YangMills/RG/BalabanCMP99SourceAliasReflectionCoefficientsAudit.lean":
        "3e5259c476fcc0de4095cb06d722c529d57580ad4d24f6363701edc511618ee9",
}

REPRO = HERE / "cmp99_alias_reflection_coefficients_repro.lean"
REPRO.write_text(
    """import Mathlib

example (z a b p : ℂ) (h : a + b = p) :
    -z + a = -(z + b) + p := by
  linear_combination h

example (z p : ℂ) : -(z + p) = -z + (-p) := by ring

example (a b : ℂ) : b * a = a * b := by ring

example (z a b M w p : ℂ) (h : a + b = M * w) :
    -z + 2 * p * a = -(z + 2 * p * b) + w * (2 * p * M) := by
  ring_nf at h ⊢
  linear_combination (2 * p) * h
""",
    encoding="utf-8",
)

runner.QUEUE = [
    (
        "cmp99_alias_reflection_coefficients_repro",
        ["lake", "env", "lean", str(REPRO)],
        None,
    ),
    (
        "cmp99_alias_reflection_coefficients_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceAliasReflectionCoefficients",
        ],
        None,
    ),
    (
        "cmp99_alias_reflection_coefficients_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/"
            "BalabanCMP99SourceAliasReflectionCoefficientsAudit.lean",
        ],
        5,
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
