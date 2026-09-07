#!/usr/bin/env python3
"""Retained-runtime diagnostic for the full physical CMP99 Eq. (2.46) point-source solution."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import re
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

with urllib.request.urlopen(BASE_RUNNER_URL, timeout=60) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location("cmp99_full_point_source_solution_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_DECLARATIONS = {
    "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceFibreCoefficients",
    "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution",
    "YangMills.RG.cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fixedCoarseFibreSolution_eq_zero_of_coarseAlias_ne",
    "YangMills.RG.cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_pointSourceFibreSolution",
    "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceSolution",
    "YangMills.RG.cmp99SourceFlatFullComplexPrecisionAction_pointSourceSolution",
}


def parse_axioms_exact(output: str, expected: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    with_axioms = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    without_axioms = re.findall(r"'([^']+)'doesnotdependonanyaxioms", compact)
    names = {name for name, _ in with_axioms} | set(without_axioms)
    if len(with_axioms) + len(without_axioms) != expected:
        raise RuntimeError("AXIOM_BLOCK_COUNT_MISMATCH=" + repr((with_axioms, without_axioms)))
    if names != EXPECTED_DECLARATIONS:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(sorted(names)))
    for name, raw_axioms in with_axioms:
        axioms = {item for item in raw_axioms.split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)
    for name in without_axioms:
        print("AXIOM_GATE=" + name + " AXIOMS=", flush=True)


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp99-full-point-source-solution-debug-v1"
runner.SOURCE_SHA = "f78d8b41193b1f1872c8736f56e66996abd286a6"
runner.ROOT = Path("/content/hrpoly-cmp99-full-point-source-solution-debug-v1")
runner.EVIDENCE = Path("/content/hrpoly-cmp99-full-point-source-solution-debug-v1-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp99-full-point-source-solution-debug-v1-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp99-full-point-source-solution-debug-v1-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatFullComplexPrecisionPointSourceSolution.lean":
        "93ab1a79cc4da4cfaa9ae252f72ea60b16d31caf12973455fd92f1665309071e",
    "YangMills/RG/BalabanCMP99SourceFlatFullComplexPrecisionPointSourceSolutionAudit.lean":
        "409ab4c249da54c62b29ca8f8b57dc7a0aba21b1bfa26920335fef2e0b494cb1",
}
runner.QUEUE = [
    (
        "full_point_source_solution_focal",
        ["lake", "build",
         "YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionPointSourceSolution"],
        None,
    ),
    (
        "full_point_source_solution_audit",
        ["lake", "env", "lean",
         "YangMills/RG/BalabanCMP99SourceFlatFullComplexPrecisionPointSourceSolutionAudit.lean"],
        6,
    ),
]


if __name__ == "__main__":
    saved_unassign = None
    try:
        from google.colab import runtime

        saved_unassign = runtime.unassign
        runtime.unassign = lambda: print("RUNTIME_RETAINED_FOR_DEBUG=1", flush=True)
    except ImportError:
        pass
    try:
        raise SystemExit(runner.main())
    finally:
        if saved_unassign is not None:
            from google.colab import runtime

            runtime.unassign = saved_unassign
