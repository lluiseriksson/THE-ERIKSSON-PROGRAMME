#!/usr/bin/env python3
"""Colab hot-debug gate for the first P7 separated precision elaboration.

The immutable mathematical checkpoint is ``SOURCE_SHA``.  This diagnostic
materializes only the already-certified P0--P5 prefix, the exact P7 project
prerequisites, and the P7 source target.  It is not terminal evidence and does
not remove any PRE-VALIDATION marker.
"""

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "74d2c37cc002246a5fec4640e477cb5ee12cf46a"
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    f"{SOURCE_SHA}/scripts/colab_qprime_row_validation.py"
)
BASE_SHA256 = "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
BASE_PATH = Path("/content/colab_qprime_row_validation.py")

with urllib.request.urlopen(BASE_URL) as response:
    base_source = response.read()
measured = hashlib.sha256(base_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != BASE_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("p7_debug_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("P7_DEBUG_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

PREFIX_PATHS = [
    "tmp/P0CanonicalPrefixTower.lean",
    "tmp/P1CoefficientMonotonicity.lean",
    "tmp/P2SourceCoefficientCoercivity.lean",
    "tmp/P2bEffectiveQuadratic.lean",
    "tmp/P2cCoarseCovariance.lean",
    "tmp/P3ScalarRecurrence.lean",
    "tmp/P3BlockGaussianAlgebra.lean",
    "tmp/P3TypedSchurBrackets.lean",
    "tmp/P3TypedGreenInverse.lean",
    "tmp/P3SourceStepCoisometry.lean",
    "tmp/P3PhysicalScalarSpecialization.lean",
    "tmp/P3PhysicalOperatorDictionary.lean",
    "tmp/P3PhysicalGreenRecurrence.lean",
    "tmp/P4aPhysicalBase.lean",
    "tmp/P4bFiniteTelescoping.lean",
    "tmp/P5PhysicalGreenScaleDictionary.lean",
]
P7_PATH = "tmp/P7SourceSeparatedAmbientPrefixPrecision.lean"

runner.RUNNER_REV = "p0-p9-p7-hot-debug-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-p0-p9-p7-debug")
runner.EVIDENCE = Path("/content/hrpoly-p0-p9-p7-debug-evidence")
runner.ARCHIVE = Path("/content/hrpoly-p0-p9-p7-debug-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-p0-p9-p7-debug-paths.txt")
runner.SOURCE_BLOBS = {
    "tmp/P0CanonicalPrefixTower.lean": "69214fa81e1d5a51219e133a2419e014fdc9a2fc51f402d11ac7bea30f92a69c",
    "tmp/P1CoefficientMonotonicity.lean": "c0e1888f55057f3cfd6e5cc02ca5016f6ef2202509fdc4d5310e9e67d08672d8",
    "tmp/P2SourceCoefficientCoercivity.lean": "76ad9f164121fbcaa6a47f1ebaa53d21b3bb4422d6629d10ecec7281914bf559",
    "tmp/P2bEffectiveQuadratic.lean": "07ac62a5b1fde3025c07eae12508e48e69c8780b8585be235cde6e29af0b039f",
    "tmp/P2cCoarseCovariance.lean": "8c8d0f5cb7fb7621df0833bc3568fe60643727edccdc0c078a4260ac2fc8c5fe",
    "tmp/P3ScalarRecurrence.lean": "02de2b81e4d83b8eeb995b24d85899968c365313b5b67b894a5e6e25c45bc224",
    "tmp/P3BlockGaussianAlgebra.lean": "2ab6de19e47297702afd2031bdfb84e9bdb239880ad7ad4a2b295df39ebd1b95",
    "tmp/P3TypedSchurBrackets.lean": "17e3c2aea27917cc2b9cc2cd9396f7aaffac5cccbb70465899fcfa57df4d52ca",
    "tmp/P3TypedGreenInverse.lean": "7d6686c7bb4e4c6bacbb1270305575bc1c4928339c65b5edc42142bb96f22478",
    "tmp/P3SourceStepCoisometry.lean": "a69cb79f8a656d19d82d3858ea4d68a1b0f257a8fa11d0a84f057e98ff91f1fa",
    "tmp/P3PhysicalScalarSpecialization.lean": "c178fa5ce93b172662d9f8e30a895f9289e0ddb791c0f63d77aa07ee0226baa6",
    "tmp/P3PhysicalOperatorDictionary.lean": "e9eca843e00f64795577e11873aa72a9d9ec7c37bebffe4906bdcd5ff4ae7f7a",
    "tmp/P3PhysicalGreenRecurrence.lean": "9dc900ec66108707ea2fdbe59cbca176ef356e987742a5e2d260fd5a4818ff5f",
    "tmp/P4aPhysicalBase.lean": "be6cfff68e18bfce7f6ca4a50390baa4a1bb4681691dc1e35cd3e71dd6334f3a",
    "tmp/P4bFiniteTelescoping.lean": "a436160e68ff7d33d4b62b8afe5ab4d957c7939fa6459c274e26c4d70d4b27e1",
    "tmp/P5PhysicalGreenScaleDictionary.lean": "1db7b0d8fe7663451af3fad091957347eb4731996455be029ff9865f2ff9bc08",
    P7_PATH: "e2118f0968481c0d583cf59f760d7f0614486f4b3fab7fda6196d8752c2421b3",
}

P0_P5_PREREQUISITES = [
    "YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge",
    "YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance",
    "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary",
    "YangMills.RG.FinitePiLpTypedKernelReindexAlgebra",
]
P7_PREREQUISITES = [
    "YangMills.RG.BalabanCMP99SourceGeneratedPhysicalAmbientDictionary",
    "YangMills.RG.BalabanCMP99SourceGeneratedRegionalFinePartition",
    "YangMills.RG.BalabanCMP99SourceSeparatedLargeBlockPartition",
    "YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas",
    "YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay",
]

runner.QUEUE = [
    (
        "p7_debug_materialize_p0_p5_prerequisites",
        ["lake", "build", *P0_P5_PREREQUISITES],
        None,
    ),
    (
        "p7_debug_prepare_scratch_build_dir",
        ["mkdir", "-p", ".lake/build/lib/lean/tmp"],
        None,
    ),
]
for index, path in enumerate(PREFIX_PATHS, start=1):
    runner.QUEUE.append((
        f"p7_debug_prefix_{index:02d}",
        [
            "lake", "env", "lean", path, "-o",
            ".lake/build/lib/lean/" + str(Path(path).with_suffix(".olean")),
        ],
        None,
    ))
runner.QUEUE.extend([
    (
        "p7_debug_materialize_project_prerequisites",
        ["lake", "build", *P7_PREREQUISITES],
        None,
    ),
    (
        "p7_source_separated_ambient_prefix_precision",
        [
            "lake", "env", "lean", P7_PATH, "-o",
            ".lake/build/lib/lean/tmp/P7SourceSeparatedAmbientPrefixPrecision.olean",
        ],
        None,
    ),
])


if __name__ == "__main__":
    raise SystemExit(runner.main())
