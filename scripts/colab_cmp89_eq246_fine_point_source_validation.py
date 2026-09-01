#!/usr/bin/env python3
"""Colab validation queue for the source-faithful fine-point CMP89 (2.46)."""

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
spec = importlib.util.spec_from_file_location("cmp89_eq246_fine_point_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_BY_COUNT = {
    3: {
        "YangMills.RG.sub_variation_le_norm_cmp89Eq249CentralEntireAveragePair",
        "YangMills.RG.cmp89Eq249CentralEntireAveragePair_ne_zero",
        "YangMills.RG.exists_cmp89Eq249CentralStabilizedComplexRadius_with_pair",
    },
    9: {
        "YangMills.RG.cmp89Eq243FineLatticeFourierTransform_normalizedPointSource",
        "YangMills.RG.cmp89Eq246FinePointSourceAliasVector_eq_fourierTransform",
        "YangMills.RG.cmp89Eq246CentralAverageRow_ne_zero_of_pair_ne_zero",
        "YangMills.RG.cmp89Eq246EntireAliasPrecisionMatrix_mulVec_finePointSourceSolution",
        "YangMills.RG.cmp89Eq246EntireAliasPrecisionMatrix_mulVec_finePointSourceSolution_of_pair_ne_zero",
        "YangMills.RG.cmp89Eq246EntireAliasPrecisionMatrix_mulVec_normalizedFinePointSourceSolution",
        "YangMills.RG.cmp89Eq246EntireAliasPrecisionMatrix_mulVec_normalizedFinePointSourceSolution_of_commonRadius",
        "YangMills.RG.cmp89Eq246StabilizedFineToFineGreenIntegrand_eq",
        "YangMills.RG.cmp89Eq246PhysicalFineToFineGreenIntegrand_eq",
    },
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
runner.RUNNER_REV = "cmp89-eq246-fine-point-source-debug-v1"
runner.SOURCE_SHA = "4035d105e264464248aed499e1686e83e320ac50"
runner.ROOT = Path("/content/hrpoly-cmp89-eq246-fine-point-source-debug-v1")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-eq246-fine-point-source-debug-v1-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-eq246-fine-point-source-debug-v1-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-eq246-fine-point-source-debug-v1-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq249CentralAveragePairComplexNonzero.lean":
        "4d2e8b25b323872822f8b9136fb9fe22a46bcd5e53595620075935eb1bb4f4c2",
    "YangMills/RG/BalabanCMP89Eq249CentralAveragePairComplexNonzeroAudit.lean":
        "24de9d4a0bfe0082671cb88a08f2dd039135405997f9c8410b8d8ab6ff1c1c42",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceFibreGreen.lean":
        "bc4a56d0694001d2bf811623d96a2f84fd9fd807db4f5b4014506fd4785b7343",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceFibreGreenAudit.lean":
        "82e1d65b3747860dcd068b1a094818aa1665f4f4569191784109549b1fe44a64",
}
runner.QUEUE = [
    (
        "eq249_central_pair_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq249CentralAveragePairComplexNonzero"],
        None,
    ),
    (
        "eq249_central_pair_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP89Eq249CentralAveragePairComplexNonzeroAudit.lean",
        ],
        3,
    ),
    (
        "eq246_fine_point_source_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq246FinePointSourceFibreGreen"],
        None,
    ),
    (
        "eq246_fine_point_source_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP89Eq246FinePointSourceFibreGreenAudit.lean",
        ],
        9,
    ),
]


if __name__ == "__main__":
    saved_unassign = None
    try:
        from google.colab import runtime

        saved_unassign = runtime.unassign
        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    try:
        raise SystemExit(runner.main())
    finally:
        if saved_unassign is not None:
            from google.colab import runtime

            runtime.unassign = saved_unassign
