#!/usr/bin/env python3
"""Colab validation queue for fine-point CMP89 (2.46) holomorphy and integral."""

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
spec = importlib.util.spec_from_file_location(
    "cmp89_eq246_fine_point_holomorphy_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_BY_COUNT = {
    10: {
        "YangMills.RG.differentiable_cmp89Eq246FinePointSourceAliasVector_component",
        "YangMills.RG.differentiableAt_cmp89Eq246StabilizedAliasNoncentralPointSourceMoment",
        "YangMills.RG.differentiableAt_cmp89Eq246StabilizedFinePointSourceSolutionMoment",
        "YangMills.RG.differentiableAt_cmp89Eq246StabilizedFinePointSourceSolution_component",
        "YangMills.RG.differentiableAt_cmp89Eq246StabilizedFineToFineGreenIntegrand",
        "YangMills.RG.differentiableAt_cmp89Eq246StabilizedFineToFineGreenIntegrand_of_commonRadius",
        "YangMills.RG.integrable_cmp89Eq246PhysicalFineToFineGreenIntegrand_real",
        "YangMills.RG.integral_cmp89Eq246FinePointSourceFibreEquation_of_commonRadius",
        "YangMills.RG.cmp89Eq246NormalizedPhysicalFineToFineGreen",
        "YangMills.RG.cmp89Eq246NormalizedPhysicalFineToFineGreen_eq",
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
runner.RUNNER_REV = "cmp89-eq246-fine-point-holomorphy-cold-v2"
runner.SOURCE_SHA = "2522d03fe2255f64ddf8513e267efd54e8f36136"
runner.ROOT = Path("/content/hrpoly-cmp89-eq246-fine-point-holomorphy-cold-v2")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-eq246-fine-point-holomorphy-cold-v2-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-eq246-fine-point-holomorphy-cold-v2-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-eq246-fine-point-holomorphy-cold-v2-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceHolomorphy.lean":
        "3a82ad645d24263422ed47954226cb2fe1364324db434f98c2b756fb0a343bc8",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceHolomorphyAudit.lean":
        "918a8a223732384815da1e295cf2158b6e79814de7f3d87ef59e1b87585dc03c",
}
runner.QUEUE = [
    (
        "eq246_fine_point_holomorphy_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq246FinePointSourceHolomorphy"],
        None,
    ),
    (
        "eq246_fine_point_holomorphy_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP89Eq246FinePointSourceHolomorphyAudit.lean",
        ],
        10,
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
