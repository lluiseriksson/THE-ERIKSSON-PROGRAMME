#!/usr/bin/env python3
"""Cold Colab seal for the promoted literal complex Eq. (3.37) Ubar radius.

The immutable source checkpoint contains the seven promoted PRE-VALIDATION
source/audit pairs.  The runner validates their exact Git blobs in dependency
order, audits every public declaration, builds ``YangMillsCore`` from the same
fresh checkout, and stops at the first real error.  It does not remove
PRE-VALIDATION, attain a terminal scalar window, or move ``20/41``.
"""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.request


SOURCE_SHA = "d69356d18c6c2392bc8a9599fd1c398109487f57"
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
    raise RuntimeError("COMPLEX_UBAR_RADIUS_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("complex_ubar_radius_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("COMPLEX_UBAR_RADIUS_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

PAIRS = [
    ("BalabanCMP99ComplexUbarSpecialLinear", 13),
    ("BalabanCMP99ComplexUbarCoordinateExponent", 9),
    ("BalabanCMP99Eq337PhysicalComplexPerturbedLinkRadius", 5),
    ("BalabanCMP99ComplexFourFactorDeviation", 2),
    ("BalabanCMP99Eq337PhysicalComplexWilsonLineRadius", 10),
    ("BalabanCMP99ComplexLocalizedUbarBackground", 4),
    ("BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius", 10),
]

PREREQUISITE = ("BalabanCMP99Eq337PhysicalComplexPerturbedBackground", 26)

runner.RUNNER_REV = "eq337-complex-ubar-radius-promoted-cold-v6"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq337-complex-ubar-radius")
runner.EVIDENCE = Path("/content/hrpoly-eq337-complex-ubar-radius-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq337-complex-ubar-radius-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq337-complex-ubar-radius-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMillsCore.lean":
        "fb3764b0d7bbca999ab78c5334771c1053bd83ab5c75b94bf41858502ffdbf7b",
    "YangMills/RG/BalabanCMP99ComplexUbarSpecialLinear.lean":
        "7953e969f37fa64eefbc877a34c8eb22affaa231f1c63f4d56d0019b815451c4",
    "YangMills/RG/BalabanCMP99ComplexUbarSpecialLinearAudit.lean":
        "46147664fa74ba119a8b4b9ecdfa2a49572c3988e7509c51ad845ca09fb57c37",
    "YangMills/RG/BalabanCMP99ComplexUbarCoordinateExponent.lean":
        "c8b2ad4b2a799d2f87fb1a72fa43cc3c8a1c9cfb51cee64bc15b64a0d4d6ed62",
    "YangMills/RG/BalabanCMP99ComplexUbarCoordinateExponentAudit.lean":
        "5a1d613e62fea16d1d22739d161a7c79db139a7a5b1f1dea3305738961edb44e",
    "YangMills/RG/BalabanCMP99Eq337PhysicalComplexPerturbedLinkRadius.lean":
        "67106eb709773bf63bd1945b0326961edde428d15c7164019caf765cbf522420",
    "YangMills/RG/BalabanCMP99Eq337PhysicalComplexPerturbedLinkRadiusAudit.lean":
        "004dec0c3ba76a6e98e57203ba0b1758761193c40e2abc907e5beed30249e4d7",
    "YangMills/RG/BalabanCMP99ComplexFourFactorDeviation.lean":
        "7f19581926f938a55444705181291a93b667a87e3586cc45613a46d0ac9aac7d",
    "YangMills/RG/BalabanCMP99ComplexFourFactorDeviationAudit.lean":
        "92839a61d39512e60edfcf79925f80aaddc950be4ec7056b5e067e532092e751",
    "YangMills/RG/BalabanCMP99Eq337PhysicalComplexWilsonLineRadius.lean":
        "f0eb686a70f94f9aa9b0455a0cf92fd90f129de1c1715e8f28c1fb00de6bddf9",
    "YangMills/RG/BalabanCMP99Eq337PhysicalComplexWilsonLineRadiusAudit.lean":
        "9167f0f8c0ecf3ad2988198dbe42b60ae2580c9b960b35a5acd24883232f1df7",
    "YangMills/RG/BalabanCMP99ComplexLocalizedUbarBackground.lean":
        "3fc0016aa1aa488bbdfa44477bbaa75c2a128869475af63b3f32648d7014a960",
    "YangMills/RG/BalabanCMP99ComplexLocalizedUbarBackgroundAudit.lean":
        "9d4e9aabab9932edef3ef68d5aad1791008dd4a2a618922a01f11843d54dcd04",
    "YangMills/RG/BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius.lean":
        "a0bd3189b28b9da75f04fab6064b7a0f58823a1306fa6f08ddd40b0d89749892",
    "YangMills/RG/BalabanCMP99Eq337PhysicalComplexUbarDeviationRadiusAudit.lean":
        "88d8ec2d94567fde7572afdf8c86b343cac53bdb112aa7e67fec40370d255ee9",
}


def capturing_run(stage: str, command: list[str], *, cwd: Path | None = None) -> str:
    """Run one stage and persist its exact combined stdout before fail-closed exit."""
    started = time.perf_counter()
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    child = subprocess.run(
        command,
        cwd=cwd,
        env=os.environ.copy(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    output = child.stdout
    print(output, flush=True)
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    (runner.EVIDENCE / f"{stage}.stdout").write_text(
        output, encoding="utf-8", newline="\n"
    )
    runner.RECORDS.append(
        {
            "stage": stage,
            "exit": child.returncode,
            "seconds": elapsed,
            "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
        }
    )
    print(
        "STAGE=" + stage + " EXIT=" + str(child.returncode)
        + " SECONDS=%.3f" % elapsed,
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


runner.run = capturing_run

queue = [
    (
        "complex_ubar_radius_materialize_prerequisites",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbedBackground",
            "YangMills.RG.BalabanCMP99SourceUbarContours",
            "YangMills.RG.BalabanCMP99UbarPhysicalDeviation",
            "YangMills.RG.BalabanCMP116FourFactorLipschitz",
            "YangMills.RG.BalabanCMP116DeterminantNearLog",
            "YangMills.RG.MatrixDetExpSkewAdjoint",
            "YangMills.RG.MatrixRealization",
            "YangMills.RG.NearLogDeviationBudget",
            "YangMills.RG.BalabanCMP116WilsonBackgroundFactorBounds",
            "YangMills.RG.BalabanCMP98GAdConjugation",
            "YangMills.RG.OrderedExponentialQuadraticBound",
            "YangMills.RG.OrderedProductQuadraticBound",
            "YangMills.ClayCore.WilsonLine",
            "YangMills.RG.Ubar",
        ],
        None,
    ),
    (
        "complex_ubar_radius_perturbed_background_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/"
            "BalabanCMP99Eq337PhysicalComplexPerturbedBackgroundAudit.lean",
        ],
        PREREQUISITE[1],
    ),
    (
        "complex_ubar_radius_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG", ".lake/build/lib/lean/tmp"],
        None,
    ),
]

for index, (name, expected_axioms) in enumerate(PAIRS, start=1):
    source = f"YangMills/RG/{name}.lean"
    audit = f"YangMills/RG/{name}Audit.lean"
    queue.extend([
        (
            f"complex_ubar_radius_{index:02d}_{name.lower()}_source",
            [
                "lake", "env", "lean", source, "-o",
                f".lake/build/lib/lean/YangMills/RG/{name}.olean",
            ],
            None,
        ),
        (
            f"complex_ubar_radius_{index:02d}_{name.lower()}_audit",
            [
                "lake", "env", "lean", audit, "-o",
                f".lake/build/lib/lean/YangMills/RG/{name}Audit.olean",
            ],
            expected_axioms,
        ),
    ])

queue.append((
    "complex_ubar_radius_promoted_root",
    ["lake", "build", "YangMillsCore"],
    None,
))

runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
