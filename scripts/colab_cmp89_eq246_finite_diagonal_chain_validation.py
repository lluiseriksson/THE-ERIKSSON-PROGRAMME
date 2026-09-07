#!/usr/bin/env python3
"""Fresh-checkout Colab seal for the CMP89 (2.46) finite diagonal chain."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import re
import urllib.request


BASE_RUNNER = Path("/content/colab_qprime_row_validation.py")
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
spec = importlib.util.spec_from_file_location("cmp89_eq246_finite_diagonal_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED = {
    101: {
        "YangMills.RG.cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound",
        "YangMills.RG.norm_cmp89Eq246FinePointSourceNoncentralCorrection_le",
    },
    102: {
        "YangMills.RG.cmp89Eq251HalfAliasPositiveTail_le_integral",
        "YangMills.RG.cmp89Eq251HalfAliasIntegral_eq",
    },
    103: {
        "YangMills.RG.cmp89Eq251BareInverseLaplacian_le_nine_mul_halfWeight",
    },
    104: {
        "YangMills.RG.cmp89Eq251OneDimensionalAliasWeight_half_le_shiftedAbs",
        "YangMills.RG.cmp89Eq245CenteredAliasIntegers_subset_Icc_radius",
        "YangMills.RG.cmp89Eq251CenteredOneDimensionalAliasSum_half_le",
        "YangMills.RG.cmp89Eq251CenteredFourDimensionalAliasSum_half_le",
    },
    105: {
        "YangMills.RG.cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound",
        "YangMills.RG.norm_cmp89Eq246FinePointSourceBareDiagonal_le",
    },
    106: {
        "YangMills.RG.cmp89Eq246FinePointSourceBareDiagonalSumBound",
        "YangMills.RG.sum_norm_cmp89Eq246FinePointSourceBareDiagonal_le",
    },
    107: {
        "YangMills.RG.cmp89Eq246FinePointSourceNoncentralCorrectionSumBound",
        "YangMills.RG.sum_norm_cmp89Eq246FinePointSourceNoncentralCorrection_le",
    },
    108: {
        "YangMills.RG.cmp89Eq246FinePointSourceNoncentralSolutionSumBound",
        "YangMills.RG.sum_norm_cmp89Eq246FinePointSourceNoncentralSolution_le",
    },
    109: {
        "YangMills.RG.cmp89Eq246FinePointSourceCentralNumerator_eq",
    },
    110: {
        "YangMills.RG.cmp89Eq246FinePointSourceCentralComponentAmplitudeBound",
        "YangMills.RG.norm_cmp89Eq246FinePointSourceCentralComponent_le",
    },
    111: {
        "YangMills.RG.cmp89Eq246FinePointSourceFullSolutionSumBound",
        "YangMills.RG.sum_norm_cmp89Eq246FinePointSourceFullSolution_le",
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
runner.RUNNER_REV = "cmp89-eq246-finite-diagonal-chain-cold-v1"
runner.SOURCE_SHA = "c1cdd849d0117cdf18724ac076cd4a5bbfd67b35"
runner.MIN_RAM_GIB = 11.0
runner.ALLOW_GPU_RUNTIME = False
runner.ROOT = Path("/content/hrpoly-cmp89-eq246-finite-diagonal-chain-cold-v1")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-eq246-finite-diagonal-chain-cold-v1-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp89-eq246-finite-diagonal-chain-cold-v1-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp89-eq246-finite-diagonal-chain-cold-v1-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceNoncentralCorrectionBound.lean": "996d20df188640c8a807da0cf35133241cc8540805ee5e22db75f2934781d968",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceNoncentralCorrectionBoundAudit.lean": "a40ed4762d302b41572167946bd5d9b83e3a8a86d9a7e2a9dd62862661707e8e",
    "YangMills/RG/BalabanCMP89Eq251HalfAliasTailIntegral.lean": "4c5b04379529d787d8e50cfe4be800fc40b1351f472bf65f8dfbf50536611b1c",
    "YangMills/RG/BalabanCMP89Eq251HalfAliasTailIntegralAudit.lean": "34fda564a9c88235ae8c739197526845a5d6f7bf9012d3f52a9aaf404cbe56a0",
    "YangMills/RG/BalabanCMP89Eq251BareInverseLaplacianHalfWeight.lean": "2e6ebfaf646e4a41def63bf398786790c4f5958ced4c4b24fd52321f687e8606",
    "YangMills/RG/BalabanCMP89Eq251BareInverseLaplacianHalfWeightAudit.lean": "d01bb463e9f09b1db0680c2a2aa600f608eae809b72ba452d73d83f1b49ea3e7",
    "YangMills/RG/BalabanCMP89Eq251CenteredHalfAliasSum.lean": "bbf0234f73f27d02ec97c5f1220ab7755905cec4491c7a239a98b2e10c6c7f18",
    "YangMills/RG/BalabanCMP89Eq251CenteredHalfAliasSumAudit.lean": "e360002e4f5f90cca46299c4183a52626889474ef0a03ceab39500bac0520553",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceBareDiagonalBound.lean": "b29f637585bf518ae98a5789bce524e4ae294f8fa99eeab5778aea0d8efd11e4",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceBareDiagonalBoundAudit.lean": "7c14d0baef8e1825d4d67a4f8495d9429b87b7fa46ad5f6663a037c72413f3a3",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceBareDiagonalSum.lean": "e9a4ba8557ce3edfca96c0f9960ce8d2de3e4f9fb9b59c1faf9407ffb89fba99",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceBareDiagonalSumAudit.lean": "f8a2d5ed50cae8b225cf2ce1521b9814b9497f94e4ed02e7cf63b7a24b96d23d",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceNoncentralCorrectionSum.lean": "f526bae53df34b31c891e147d9ab4a9b7a4afceb3a03f190fcb92e9181be738b",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceNoncentralCorrectionSumAudit.lean": "c357d2941c6e7c7076e46bc6d06ba10c5f03b05f4c76f8b5585a80c8c5c15d11",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceNoncentralSolutionSum.lean": "67fe60511421973758fcc8ede0c762d91114baba5a1e5da7a29b77458c1a05ef",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceNoncentralSolutionSumAudit.lean": "86a995125df15f333892224b5645a8f2e9c0fbb7c98dcd57b184597205d78d7b",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceCentralNumeratorIdentity.lean": "84e4f7db8ab83fa5c1459790a684026ec7b4bd4d069fc45d4383ba7d9e8915ca",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceCentralNumeratorIdentityAudit.lean": "32fe866f0a19741bd4f55224465d73ca25a860007e04b6df01fbffc83fdbb8bf",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceCentralComponentBound.lean": "010adeac0b9c63073bff65843b5af4a5cc75345f4ed1cd72012396526be04383",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceCentralComponentBoundAudit.lean": "4291b4df82274e8164f49626f5af5a44b449b40fe3c5baeae17ad9fa15346bd1",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceFullSolutionSum.lean": "0eab7af11e26f03b414baff2f94f195258850f3d5e991d170f668b573b53a2d4",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceFullSolutionSumAudit.lean": "2df9efa762e214ae926640009dbd611644ea88d0f9de5179539ac81c4530e1d1",
}

runner.QUEUE = [
    ("finite_diagonal_chain_focal", ["lake", "build", "YangMills.RG.BalabanCMP89Eq246FinePointSourceFullSolutionSum"], None),
]
for key, stem in [
    (101, "BalabanCMP89Eq246FinePointSourceNoncentralCorrectionBound"),
    (102, "BalabanCMP89Eq251HalfAliasTailIntegral"),
    (103, "BalabanCMP89Eq251BareInverseLaplacianHalfWeight"),
    (104, "BalabanCMP89Eq251CenteredHalfAliasSum"),
    (105, "BalabanCMP89Eq246FinePointSourceBareDiagonalBound"),
    (106, "BalabanCMP89Eq246FinePointSourceBareDiagonalSum"),
    (107, "BalabanCMP89Eq246FinePointSourceNoncentralCorrectionSum"),
    (108, "BalabanCMP89Eq246FinePointSourceNoncentralSolutionSum"),
    (109, "BalabanCMP89Eq246FinePointSourceCentralNumeratorIdentity"),
    (110, "BalabanCMP89Eq246FinePointSourceCentralComponentBound"),
    (111, "BalabanCMP89Eq246FinePointSourceFullSolutionSum"),
]:
    runner.QUEUE.append(
        (
            f"finite_diagonal_audit_{key}",
            ["lake", "env", "lean", f"YangMills/RG/{stem}Audit.lean"],
            key,
        )
    )


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
