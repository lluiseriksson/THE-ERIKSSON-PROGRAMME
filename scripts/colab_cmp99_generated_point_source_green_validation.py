#!/usr/bin/env python3
"""Cold Colab validation for the generated physical point-source Green bridge.

This revision is the explicit standard-RAM CPU fallback for periods when the
Colab Pro+ allocator ignores the high-RAM selector.  The imported base runner
keeps 40 GiB as its default; this queue lowers its declared gate to 11 GiB and
records that choice in the evidence JSON.  GPU runtimes remain forbidden.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import re
import urllib.request
import hashlib


HERE = Path("/content")
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "2dfaa8634203470608cc341d36e5d1fab4a546c4/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = "2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e"

with urllib.request.urlopen(BASE_RUNNER_URL, timeout=60) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location("cmp99_point_source_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


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
runner.RUNNER_REV = "cmp99-generated-point-source-green-v2-standard-ram-fallback"
runner.SOURCE_SHA = "bd89724bbb926da4af507690773f32a84a657ccf"
runner.MIN_RAM_GIB = 11.0
runner.ALLOW_GPU_RUNTIME = False
runner.ROOT = Path("/content/hrpoly-cmp99-generated-point-source-green-v2-standard-ram-fallback")
runner.EVIDENCE = Path("/content/hrpoly-cmp99-generated-point-source-green-v2-standard-ram-fallback-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp99-generated-point-source-green-v2-standard-ram-fallback-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp99-generated-point-source-green-v2-standard-ram-fallback-paths.txt")
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
