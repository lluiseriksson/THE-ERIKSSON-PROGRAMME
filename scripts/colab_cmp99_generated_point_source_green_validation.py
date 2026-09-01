#!/usr/bin/env python3
"""Colab validation for the generated physical point-source Green bridge."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import re
import urllib.request
import hashlib


HERE = Path("/content")
PARENT = HERE / "colab_cmp99_full_point_source_solution_cold_v1.py"
PARENT_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "83a7d485f1cf9898e3014efcb6a1a43da4e9d386/"
    "scripts/colab_cmp99_full_point_source_solution_cold_v1.py"
)
PARENT_SHA256 = "efe15c9e952445a70e698c8d84b5f779763e10c174055c20111efb55a64315e7"

with urllib.request.urlopen(PARENT_URL, timeout=60) as response:
    parent_source = response.read()
parent_hash = hashlib.sha256(parent_source).hexdigest()
print("PARENT_RUNNER_TRANSPORT_SHA256=" + parent_hash, flush=True)
if parent_hash != PARENT_SHA256:
    raise RuntimeError("PARENT_RUNNER_TRANSPORT_HASH_MISMATCH")
PARENT.write_bytes(parent_source)
spec = importlib.util.spec_from_file_location("cmp99_point_source_parent", PARENT)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load parent runner: {PARENT}")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)
runner = parent.runner


EXPECTED = {
    63: {
        "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceSolution_eq_inverse_apply",
    },
    64: {
        "YangMills.RG.cmp89Eq249CentralEntireAveragePair_physicalCoarse_ne_zero",
    },
    65: {
        "YangMills.RG.cmp99SourceGeneratedFlatPhysicalPointSourceSolution_eq_green_apply",
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
        raise RuntimeError("AXIOM_BLOCK_COUNT_MISMATCH=" + repr((with_axioms, without_axioms)))
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
runner.RUNNER_REV = "cmp99-generated-point-source-green-v1"
runner.SOURCE_SHA = "bd89724bbb926da4af507690773f32a84a657ccf"
runner.ROOT = Path("/content/hrpoly-cmp99-generated-point-source-green-v1")
runner.EVIDENCE = Path("/content/hrpoly-cmp99-generated-point-source-green-v1-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp99-generated-point-source-green-v1-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp99-generated-point-source-green-v1-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatFullComplexPrecisionPointSourceInverseUniqueness.lean":
        "896874e6bb5bf520c45c00f2276e4a7e94716bda38f54e2d3634e13e1fac540f",
    "YangMills/RG/BalabanCMP99SourceFlatFullComplexPrecisionPointSourceInverseUniquenessAudit.lean":
        "d05c02dd3fd4c4f1ed213813acabefd834b9cf63c69183e5efb4d0d4291f2a96",
    "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalCentralAveragePairNonvanishing.lean":
        "dbf8ddc6bb2984d834a9cbbd79381437b60cab3300eda0119bb72c284656e59f",
    "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalCentralAveragePairNonvanishingAudit.lean":
        "9eb6620f67393812cda5de77c89ae0c8d860dd731b38ba72ac32d9b67d23ec4b",
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPointSourceGreenIdentification.lean":
        "8681400372c01d2a92e26041c5741dfc9ba634a1732f25f1efb7e31994a794d2",
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPointSourceGreenIdentificationAudit.lean":
        "1700c74f062cede5c6ba2a6073ab914a2530e63112bbcbaea722c17eaf513c4b",
}
runner.QUEUE = [
    (
        "point_source_inverse_uniqueness_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionPointSourceInverseUniqueness"],
        None,
    ),
    (
        "point_source_inverse_uniqueness_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatFullComplexPrecisionPointSourceInverseUniquenessAudit.lean"],
        63,
    ),
    (
        "central_average_pair_nonvanishing_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalCentralAveragePairNonvanishing"],
        None,
    ),
    (
        "central_average_pair_nonvanishing_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalCentralAveragePairNonvanishingAudit.lean"],
        64,
    ),
    (
        "generated_point_source_green_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalPointSourceGreenIdentification"],
        None,
    ),
    (
        "generated_point_source_green_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPointSourceGreenIdentificationAudit.lean"],
        65,
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
