#!/usr/bin/env python3
"""Colab diagnostic gate for the stabilized CMP89 column endpoint.

The immutable mathematical source is ``SOURCE_SHA``.  This runner reuses the
fresh-clone transport, exact pin gates, robust axiom parser, evidence archive,
and runtime release protocol.  A Mathlib-only repro checks the finite-sum
split and common-factor rewrites before the expensive project focal.

Honest scope: this does not identify the physical row and column sums,
reindex through cross-fibre Fourier negation, periodize a Green integrand,
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
    "cmp89_stabilized_alias_column_solution_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp89-stabilized-alias-column-solution-v2"
runner.SOURCE_SHA = "5d3fab0e1d3513a5733ce525a05edb06a05731bf"
runner.ROOT = Path("/content/hrpoly-cmp89-stabilized-alias-column-solution")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-stabilized-alias-column-solution-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-stabilized-alias-column-solution-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-stabilized-alias-column-solution-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq249StabilizedAliasColumnSolution.lean":
        "8f54dad29eb3040d0c59cd90eea693333cfe745f6c73d51175d16288247461df",
    "YangMills/RG/BalabanCMP89Eq249StabilizedAliasColumnSolutionAudit.lean":
        "2ef8189260419385af18bfd34ad0fb55e29886aae8a916d092cd816ced742fef",
}

REPRO = HERE / "cmp89_stabilized_alias_column_solution_repro.lean"
REPRO.write_text(
    """import Mathlib

open scoped BigOperators

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (central : ι) (f : ι → ℂ) :
    (∑ n, f n) = f central + ∑ n ∈ Finset.univ.erase central, f n := by
  rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ central)]
  ring

example {ι : Type*} [Fintype ι] (c s : ℂ) (f : ι → ℂ) :
    (∑ n, c * f n / s) = c * (∑ n, f n) / s := by
  rw [← Finset.sum_div, ← Finset.mul_sum]
""",
    encoding="utf-8",
)

runner.QUEUE = [
    (
        "cmp89_stabilized_alias_column_solution_repro",
        ["lake", "env", "lean", str(REPRO)],
        None,
    ),
    (
        "cmp89_stabilized_alias_column_solution_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP89Eq249StabilizedAliasColumnSolution",
        ],
        None,
    ),
    (
        "cmp89_stabilized_alias_column_solution_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/"
            "BalabanCMP89Eq249StabilizedAliasColumnSolutionAudit.lean",
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
