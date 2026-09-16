#!/usr/bin/env python3
"""Cold Colab validation for the next two physical Eq. (2.46) bricks."""

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
spec = importlib.util.spec_from_file_location("cmp99_physical_eq246_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_BY_COUNT = {
    4: {
        "YangMills.RG.cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolution",
        "YangMills.RG.cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_transpose_mulVec_fullSolution",
        "YangMills.RG.cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeFullVectorSolution",
        "YangMills.RG.cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_transpose_sum_smul_fullVectorSolution",
    },
    1: {"YangMills.RG.cmp99FlatPhysicalFibreDFT_pointSource"},
}


def parse_axioms_exact(output: str, expected: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    with_axioms = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    without_axioms = re.findall(r"'([^']+)'doesnotdependonanyaxioms", compact)
    names = {name for name, _ in with_axioms} | set(without_axioms)
    expected_names = EXPECTED_BY_COUNT.get(expected)
    if expected_names is None:
        raise RuntimeError("UNEXPECTED_AXIOM_COUNT_REQUEST=" + str(expected))
    if len(with_axioms) + len(without_axioms) != expected:
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
runner.RUNNER_REV = "cmp99-physical-eq246-next-cold-v1"
runner.SOURCE_SHA = "76d8aa0c083dd1061ea50580889d0316bc0cad3d"
runner.ROOT = Path("/content/hrpoly-cmp99-physical-eq246-next-cold-v1")
runner.EVIDENCE = Path("/content/hrpoly-cmp99-physical-eq246-next-cold-v1-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp99-physical-eq246-next-cold-v1-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp99-physical-eq246-next-cold-v1-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolution.lean":
        "b95adb2c3026e39b8846b16d8f7aaed07776b7ac63dcb0b9cf72ed6a2651bd78",
    "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolutionAudit.lean":
        "2afa20a4a147c36e7c474bad0df1f33c814b5a7814ed33f4eb50ca1ed6a7d4bd",
    "YangMills/RG/BalabanCMP99FlatPhysicalFibrePointSourceDFT.lean":
        "393692ae5dd94df1bc2138b24ae1fb198712af0dc7b1a5471b733a3c8bce1a84",
    "YangMills/RG/BalabanCMP99FlatPhysicalFibrePointSourceDFTAudit.lean":
        "9a04dd238d71fb1a73043ccea31930d0aac7eb177a016724c3f43f0516e81221",
}
runner.QUEUE = [
    (
        "physical_eq246_transpose_full_solution_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolution"],
        None,
    ),
    (
        "physical_eq246_transpose_full_solution_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolutionAudit.lean"],
        4,
    ),
    (
        "physical_point_source_dft_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99FlatPhysicalFibrePointSourceDFT"],
        None,
    ),
    (
        "physical_point_source_dft_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99FlatPhysicalFibrePointSourceDFTAudit.lean"],
        1,
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
