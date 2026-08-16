#!/usr/bin/env python3
"""Colab diagnostic gate for the reflected stabilized-solution bridge.

The immutable mathematical source is ``SOURCE_SHA``.  This runner reuses the
fresh-clone transport, exact pin gates, robust axiom parser, evidence archive,
and runtime release protocol.  A Mathlib-only repro checks the finite-sum
reindex-and-erase pattern before the expensive project focal.

Honest scope: this seals only the simple CMP89 alias reflection, stabilized
denominator and transpose-to-column solution transport.  It does not identify
the affine physical cross-fibre carry, construct regional ``B0``, attain
window 15 or discharge a terminal field.
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
    "cmp99_alias_reflection_stabilized_solution_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-alias-reflection-stabilized-solution-v3"
runner.SOURCE_SHA = "ce00198eb10766b15e3fb90dc756cbf634e34740"
runner.ROOT = Path("/content/hrpoly-cmp99-alias-reflection-stabilized-solution")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-alias-reflection-stabilized-solution-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-alias-reflection-stabilized-solution-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-alias-reflection-stabilized-solution-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceAliasReflectionStabilizedSolution.lean":
        "0925f929542853a1826bd61dbeed67ccb2679b4679ac328c8ba8e7e2746b9591",
    "YangMills/RG/BalabanCMP99SourceAliasReflectionStabilizedSolutionAudit.lean":
        "579d4b8ea2d6988528c66fc19aeec46c3565a5dd77f8ea386c653c8184ffc61d",
}

REPRO = HERE / "cmp99_alias_reflection_stabilized_solution_repro.lean"
REPRO.write_text(
    """import Mathlib

open scoped BigOperators

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (reflect : Equiv.Perm ι) (central : ι) (f g : ι → ℂ)
    (hreflectCentral : reflect central = central)
    (hterm : ∀ n, g (reflect n) = f n) :
    (∑ n ∈ Finset.univ.erase central, g n) =
      ∑ n ∈ Finset.univ.erase central, f n := by
  have hfull : (∑ n, g n) = ∑ n, f n := by
    calc
      (∑ n, g n) = ∑ n, g (reflect n) := by
        exact (Equiv.sum_comp reflect g).symm
      _ = ∑ n, f n := by
        apply Finset.sum_congr rfl
        intro n _
        exact hterm n
  have hcentral : g central = f central := by
    have h := hterm central
    simpa only [hreflectCentral] using h
  have hleft := Finset.sum_erase_add Finset.univ g
    (Finset.mem_univ central)
  have hright := Finset.sum_erase_add Finset.univ f
    (Finset.mem_univ central)
  calc
    (∑ n ∈ Finset.univ.erase central, g n) =
        (∑ n, g n) - g central := by
      rw [← hleft]
      ring
    _ = (∑ n, f n) - f central := by rw [hfull, hcentral]
    _ = ∑ n ∈ Finset.univ.erase central, f n := by
      rw [← hright]
      ring
""",
    encoding="utf-8",
)

runner.QUEUE = [
    (
        "cmp99_alias_reflection_stabilized_solution_repro",
        ["lake", "env", "lean", str(REPRO)],
        None,
    ),
    (
        "cmp99_alias_reflection_stabilized_solution_focal",
        [
            "lake",
            "build",
            "YangMills.RG."
            "BalabanCMP99SourceAliasReflectionStabilizedSolution",
        ],
        None,
    ),
    (
        "cmp99_alias_reflection_stabilized_solution_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/"
            "BalabanCMP99SourceAliasReflectionStabilizedSolutionAudit.lean",
        ],
        7,
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
