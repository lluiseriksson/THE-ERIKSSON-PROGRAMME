#!/usr/bin/env python3
"""Cold Colab validation for the promoted C6d precision prefix.

The queue compiles six promoted PRE-VALIDATION source/audit pairs in
dependency order, checks twenty-seven public declarations, builds
YangMillsCore from the same fresh checkout, and stops at the first real
error.  It does not attain window 15, move 20/41, or instantiate
TermSource.
"""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.request


SOURCE_SHA = '768bca00ba63e52eccacd8226cee91e6cfafd39e'
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    f"{SOURCE_SHA}/scripts/colab_qprime_row_validation.py"
)
BASE_SHA256 = 'd06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee'
BASE_PATH = Path("/content/colab_qprime_row_validation.py")

with urllib.request.urlopen(BASE_URL) as response:
    base_source = response.read()
measured = hashlib.sha256(base_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != BASE_SHA256:
    raise RuntimeError("C6D_PROMOTED_PRECISION_PREFIX_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("c6d_promoted_precision_prefix_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_PROMOTED_PRECISION_PREFIX_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

MODULES = [
    ('BalabanCMP99SourcePhysicalRealSliceTowerPair', 5),
    ('BalabanCMP99Eq337ComplexClosedRadiusToPhysicalRadiusBudget', 4),
    ('BalabanCMP99Eq360ComplexRegionalLaplacian', 8),
    ('BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice', 3),
    ('BalabanCMP99Eq360ComplexLocalLaplacianPerturbation', 4),
    ('BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation', 3),
]

runner.RUNNER_REV = 'c6d-promoted-precision-prefix-v2'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-c6d-promoted-precision-prefix")
runner.EVIDENCE = Path("/content/hrpoly-c6d-promoted-precision-prefix-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-promoted-precision-prefix-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-promoted-precision-prefix-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMillsCore.lean': '7522e0659a2a9b9c8e9df0f9b68ca21aac254c1dce7edb6d367088fcf18374fc',
    'YangMills/RG/BalabanCMP99SourcePhysicalRealSliceTowerPair.lean': 'f49dcfa2a406cee67f15221c35b68420a839f07922c4ca67ad79e21e0ee97dcd',
    'YangMills/RG/BalabanCMP99SourcePhysicalRealSliceTowerPairAudit.lean': '6041fe8b6e018e2cae0281a844945b2541a015e0d7db68ac1e99e847b4388a1c',
    'YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusToPhysicalRadiusBudget.lean': '2f138396a1f1c92f8acc02c45228065c2b3c5f9ad93df04620186ccf82656dd3',
    'YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusToPhysicalRadiusBudgetAudit.lean': 'fcc370daff7e783ba90ac162869700cded9c6a044b7a15e1593c3e29af892d2b',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacian.lean': 'c08cf0f95ca2f7d47e3b6c2b20ad30f1236458315aed996624238703d9e7e835',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacianAudit.lean': 'ee79bde256a3b422c9f4560a361046a7ef715d8298fdf49545f114af77a82310',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice.lean': '8c4524096bb1f3ecd6b6067646dc0cdbbd66cce886f0efd3963b91f9b5bf4ae8',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacianRealSliceAudit.lean': '05001a36e478c2dce77508383d902bfd668df6c521869c649c980d1faea83d85',
    'YangMills/RG/BalabanCMP99Eq360ComplexLocalLaplacianPerturbation.lean': 'a0b558ead45f37223713fb4b5832b24101431cff33e64af863c4293ddf09aade',
    'YangMills/RG/BalabanCMP99Eq360ComplexLocalLaplacianPerturbationAudit.lean': 'c38c3f6d363bac320c48cace2488bca53a734ce33de358615b05d5b13824bc9e',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation.lean': 'c20ab0a4d2973b71a67af8c7701d48224c5bb9777992830f92c230b548d48f7c',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalPrecisionPerturbationAudit.lean': '5e4b10d9c116f122bead2446fd4eb7fd63cd251284cfb33248e4938e02dd0c30',
}


def capturing_run(stage: str, command: list[str], *, cwd: Path | None = None) -> str:
    """Persist exact combined stdout and the child's real exit code."""
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
        "c6d_promoted_precision_prefix_materialize_dependencies",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourcePhysicalRealSliceTower",
            "YangMills.RG.BalabanCMP99Eq359ComplexRegionalTowerPair",
            "YangMills.RG.BalabanCMP99Eq337ComplexClosedRadiusPhysicalBridge",
            "YangMills.RG.BalabanCMP99SourceUbarRadiusBudget",
            "YangMills.RG.BalabanCMP99ComplexSpecialLinearAdjointAction",
            "YangMills.RG.PhysicalGaugeOperator",
            "YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice",
            "YangMills.RG.BalabanCMP99SourceFlatPhysicalComplexModeAction",
            "YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport",
        ],
        None,
    ),
    (
        "c6d_promoted_precision_prefix_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
        None,
    ),
]

for index, (module, expected_axioms) in enumerate(MODULES, start=1):
    source = f"YangMills/RG/{module}.lean"
    audit = f"YangMills/RG/{module}Audit.lean"
    queue.extend([
        (
            f"c6d_promoted_precision_prefix_{index:02d}_{module.lower()}_source",
            [
                "lake", "env", "lean", source, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}.olean",
            ],
            None,
        ),
        (
            f"c6d_promoted_precision_prefix_{index:02d}_{module.lower()}_audit",
            [
                "lake", "env", "lean", audit, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean",
            ],
            expected_axioms,
        ),
    ])

queue.append(("c6d_promoted_precision_prefix_root", ["lake", "build", "YangMillsCore"], None))
runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
