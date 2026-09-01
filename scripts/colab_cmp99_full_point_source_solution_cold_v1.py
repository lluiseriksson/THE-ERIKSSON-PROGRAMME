#!/usr/bin/env python3
"""Cold Colab seal for the full periodic Eq. (2.46) point-source solution."""

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
spec = importlib.util.spec_from_file_location("cmp99_full_point_source_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED = {
    61: {
        "YangMills.RG.cmp99SourceFlatFixedCoarseFibreCoefficientExtension_apply",
        "YangMills.RG.cmp99FlatPhysicalFibreDFT_fixedCoarseFibreFourierSynthesis",
        "YangMills.RG.cmp99SourceFlatFixedCoarseFibreFourierSynthesis_eq_sum",
        "YangMills.RG.cmp99SourceFlatFullComplexPrecisionAction_add",
        "YangMills.RG.cmp99SourceFlatFullComplexPrecisionAction_finset_sum",
        "YangMills.RG.cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fixedCoarseFibre",
    },
    62: {
        "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceFibreCoefficients",
        "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution",
        "YangMills.RG.cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fixedCoarseFibreSolution_eq_zero_of_coarseAlias_ne",
        "YangMills.RG.cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_pointSourceFibreSolution",
        "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceSolution",
        "YangMills.RG.cmp99SourceFlatFullComplexPrecisionAction_pointSourceSolution",
    },
}


def parse_axioms_exact(output: str, expected_key: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    with_axioms = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    without_axioms = re.findall(r"'([^']+)'doesnotdependonanyaxioms", compact)
    names = {name for name, _ in with_axioms} | set(without_axioms)
    expected_names = EXPECTED.get(expected_key)
    if expected_names is None:
        raise RuntimeError("UNEXPECTED_AXIOM_GATE_KEY=" + str(expected_key))
    if len(with_axioms) + len(without_axioms) != len(expected_names):
        raise RuntimeError(
            "AXIOM_BLOCK_COUNT_MISMATCH=" + repr((with_axioms, without_axioms))
        )
    if names != expected_names:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(sorted(names)))
    for name, raw_axioms in with_axioms:
        axioms = {item for item in raw_axioms.split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)
    for name in without_axioms:
        print("AXIOM_GATE=" + name + " AXIOMS=", flush=True)


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp99-full-point-source-solution-cold-v1"
runner.SOURCE_SHA = "7b9d0f9b9e292d48c479477aa336a353a3bb10ea"
runner.ROOT = Path("/content/hrpoly-cmp99-full-point-source-solution-cold-v1")
runner.EVIDENCE = Path("/content/hrpoly-cmp99-full-point-source-solution-cold-v1-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp99-full-point-source-solution-cold-v1-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp99-full-point-source-solution-cold-v1-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatFullComplexPrecisionFibreAction.lean":
        "68e51fb1899d4c5c4225a95179a390e3bacb91cd64828400c548d9ba0a95449f",
    "YangMills/RG/BalabanCMP99SourceFlatFullComplexPrecisionFibreActionAudit.lean":
        "c6d028aec740d08f8c53e99ffffed234a33062c2ba755ce93e079b17cc3f04c0",
    "YangMills/RG/BalabanCMP99SourceFlatFullComplexPrecisionPointSourceSolution.lean":
        "85b4245aa0d9d5dd5daa5b6a0d5097baac1c424ea62b60e846e93f2c275bac1b",
    "YangMills/RG/BalabanCMP99SourceFlatFullComplexPrecisionPointSourceSolutionAudit.lean":
        "409ab4c249da54c62b29ca8f8b57dc7a0aba21b1bfa26920335fef2e0b494cb1",
}
runner.QUEUE = [
    (
        "full_complex_precision_fibre_action_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionFibreAction"],
        None,
    ),
    (
        "full_complex_precision_fibre_action_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatFullComplexPrecisionFibreActionAudit.lean"],
        61,
    ),
    (
        "full_point_source_solution_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionPointSourceSolution"],
        None,
    ),
    (
        "full_point_source_solution_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatFullComplexPrecisionPointSourceSolutionAudit.lean"],
        62,
    ),
]


if __name__ == "__main__":
    saved_unassign = None
    try:
        from google.colab import runtime

        saved_unassign = runtime.unassign
        runtime.unassign = lambda: print("RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True)
    except ImportError:
        pass
    try:
        raise SystemExit(runner.main())
    finally:
        if saved_unassign is not None:
            from google.colab import runtime

            runtime.unassign = saved_unassign
