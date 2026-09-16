#!/usr/bin/env python3
"""Fresh Colab seal for the current CMP89 Neumann source chain.

This gate validates four leaf bricks on one cold checkout: the literal
three-term precision and canonical inverse, fixed-region Poincare existence
from an explicit joint-kernel gate, the weighted/counting dictionary, and the
canonical regional entry in the reflection formula. It does not prove the
joint-kernel gate, the rectangle/full-lattice dictionaries, CMP89 (3.42),
window 15, move ``20/41`` or instantiate a ``TermSource``.
"""

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
with urllib.request.urlopen(BASE_RUNNER_URL) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location("cmp89_neumann_source_chain_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_BY_GATE = {
    101: {
        "YangMills.RG.inner_cmp89SourceNeumannRegionalGaugePrecision",
        "YangMills.RG.cmp89SourceNeumannRegionalGaugePrecision_isSymmetric",
        "YangMills.RG.isCoerciveCLM_cmp89SourceNeumannRegionalGaugePrecision",
        "YangMills.RG.cmp89SourceNeumannRegionalGaugePrecision_comp_green",
        "YangMills.RG.cmp89SourceNeumannRegionalGreen_comp_gaugePrecision",
        "YangMills.RG.inner_cmp89SourceRetainedNeumannPrefixGaugePrecision",
        "YangMills.RG.cmp89SourceRetainedNeumannPrefixGaugePrecision_isSymmetric",
        "YangMills.RG.isCoerciveCLM_cmp89SourceRetainedNeumannPrefixGaugePrecision",
        "YangMills.RG.cmp89SourceRetainedNeumannPrefixGaugePrecision_comp_green",
        "YangMills.RG.cmp89SourceRetainedNeumannPrefixGreen_comp_gaugePrecision",
    },
    102: {
        "YangMills.RG.CMP89SourceNeumannRegionalJointKernelTrivial",
        "YangMills.RG.exists_cmp89SourceNeumannRegionalPoincare_of_jointKernel",
        "YangMills.RG.CMP89SourceRetainedNeumannPrefixJointKernelTrivial",
        "YangMills.RG.exists_cmp89SourceRetainedNeumannPrefixPoincare_of_jointKernel",
    },
    103: {
        "YangMills.RG.cmp89SourceCommonSpacingWeight_adjoint",
        "YangMills.RG.cmp99SourceSpacingPairing_neumannRegionalLaplacian",
        "YangMills.RG.cmp85SourcePrefixCountingCoefficient_mul_fineVolume",
        "YangMills.RG.cmp99SourceSpacingPairing_retainedNeumannPrefixGaugePrecision",
    },
    104: {
        "YangMills.RG.cmp89FinitePiLpGreenEntryAt",
        "YangMills.RG.CMP89CanonicalNeumannReflectionRepresentation",
        "YangMills.RG.cmp89CanonicalNeumannReflectionRepresentation_eq_series",
        "YangMills.RG.CMP89SourceRetainedCanonicalNeumannReflectionRepresentation",
        "YangMills.RG.cmp89SourceRetainedCanonicalNeumannReflectionRepresentation_eq_series",
    },
}


def parse_axioms_exact(output: str, gate: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    found = {name: body for name, body in blocks}
    expected = EXPECTED_BY_GATE[gate]
    if set(found) != expected:
        raise RuntimeError(
            "AXIOM_DECLARATIONS_MISMATCH="
            + repr({"found": sorted(found), "expected": sorted(expected)})
        )
    for name in sorted(expected):
        axioms = {item for item in found[name].split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp89-neumann-source-chain-cold-v1"
runner.SOURCE_SHA = "a1fe7d151400d99fe0d89e5d430ddb992a6168b8"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-source-chain-cold")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-neumann-source-chain-cold-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp89-neumann-source-chain-cold-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp89-neumann-source-chain-cold-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalGaugePrecision.lean":
        "dfef4cef851c6062632098b3ab49971c0bf9cb6fe6ec9f2219f961cff4706a73",
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalGaugePrecisionAudit.lean":
        "3dff5e6ea6a93f743820b9710ac10e295e55587194e7bb826a7580e9c9051e1f",
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalPoincareExistence.lean":
        "b79a070f779583058f0b2cfa984f5b05efc05af34f36f7d3fd4a7a1d577151de",
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalPoincareExistenceAudit.lean":
        "3a3673a2be7178b4a4551fbb2a680f9b045ff2c2039328fba7a8139d77dcef16",
    "YangMills/RG/BalabanCMP89SourceNeumannWeightedCountingDictionary.lean":
        "12e40bfca4885f5defd2536ef64555705e04175d9d88a6eb40d26cb6ab537be2",
    "YangMills/RG/BalabanCMP89SourceNeumannWeightedCountingDictionaryAudit.lean":
        "2bf9522efbace7e746da0d13c66ecbd060b803ada81fe39040fa4768431aa6e4",
    "YangMills/RG/BalabanCMP89CanonicalNeumannReflectionRepresentation.lean":
        "d606f4180d293cb9e1976190333b2736b729006c4c90ed65c678c4e388c6c277",
    "YangMills/RG/BalabanCMP89CanonicalNeumannReflectionRepresentationAudit.lean":
        "bb4f46522fbdc47c705b1b4b00fa53e5d6f6be170c4872210f9d509a9e745df7",
}
runner.QUEUE = [
    ("cmp89_neumann_gauge_precision_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannRegionalGaugePrecision"], None),
    ("cmp89_neumann_gauge_precision_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceNeumannRegionalGaugePrecisionAudit.lean"], 101),
    ("cmp89_neumann_poincare_existence_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannRegionalPoincareExistence"], None),
    ("cmp89_neumann_poincare_existence_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceNeumannRegionalPoincareExistenceAudit.lean"], 102),
    ("cmp89_neumann_weighted_counting_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannWeightedCountingDictionary"], None),
    ("cmp89_neumann_weighted_counting_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceNeumannWeightedCountingDictionaryAudit.lean"], 103),
    ("cmp89_canonical_neumann_reflection_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP89CanonicalNeumannReflectionRepresentation"], None),
    ("cmp89_canonical_neumann_reflection_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP89CanonicalNeumannReflectionRepresentationAudit.lean"], 104),
]


if __name__ == "__main__":
    try:
        from google.colab import runtime

        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    runner_exit = runner.main()
    try:
        from google.colab import files

        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    except Exception as error:
        print("EVIDENCE_DOWNLOAD_ERROR=" + repr(error), flush=True)
    raise SystemExit(runner_exit)
