#!/usr/bin/env python3
"""Cold validation of the literal analytic regional-Laplacian prefix.

The queue certifies the two exact Eq. (3.51) algebraic prerequisites, the
source stencil and its compact real-slice dictionary.  It does not certify
the Eq. (3.51)--(3.54) three-species regrouping/bound, the regional resolvent,
any transported physical action, window 15, 20/41 or TermSource.
"""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.request


SOURCE_SHA = 'abb9dd508e28ebc0b30af4da0ee5a0aaf283151c'
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
    raise RuntimeError("EQ360_REGIONAL_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("eq360_regional_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("EQ360_REGIONAL_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

MODULES = [
    ('BalabanCMP99ComplexSpecialLinearAdjointComposition', 1),
    ('BalabanCMP99Eq351PhysicalComplexPositiveBondFactorization', 6),
    ('BalabanCMP99Eq360ComplexRegionalLaplacian', 8),
    ('BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice', 3),
]

runner.RUNNER_REV = 'eq360-complex-regional-real-slice-v1'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq360-complex-regional")
runner.EVIDENCE = Path("/content/hrpoly-eq360-complex-regional-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq360-complex-regional-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq360-complex-regional-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMillsCore.lean': 'cf95367cb81d3c581b26bb7b336525a365f10ed9ef94e2173d9c0c1430947f75',
    'YangMills/RG/BalabanCMP99ComplexSpecialLinearAdjointComposition.lean': '8a334334c411bfc846e1aa90e1579c947e2197db8e8614c1041b9e9931e7424b',
    'YangMills/RG/BalabanCMP99ComplexSpecialLinearAdjointCompositionAudit.lean': '66c8152302c61a4d159aa665d244bdb61fab02da5dbf7f801cb6d9f4e2f61f9d',
    'YangMills/RG/BalabanCMP99Eq351PhysicalComplexPositiveBondFactorization.lean': '2b66901bc4aa32cbba44d8c78009d15f1282bb68fd2c4d551f54ac144c95b43f',
    'YangMills/RG/BalabanCMP99Eq351PhysicalComplexPositiveBondFactorizationAudit.lean': 'a8dd09186034e5984876d908845c50fbe2f405b64b86a453bbc96b1f2ebaa4d1',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacian.lean': 'c08cf0f95ca2f7d47e3b6c2b20ad30f1236458315aed996624238703d9e7e835',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacianAudit.lean': 'ee79bde256a3b422c9f4560a361046a7ef715d8298fdf49545f114af77a82310',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice.lean': '8c4524096bb1f3ecd6b6067646dc0cdbbd66cce886f0efd3963b91f9b5bf4ae8',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacianRealSliceAudit.lean': '05001a36e478c2dce77508383d902bfd668df6c521869c649c980d1faea83d85',
}


def capturing_run(stage: str, command: list[str], *, cwd: Path | None = None) -> str:
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
        "eq360_regional_materialize_dependencies",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99Eq359TowerRealSliceAgreement",
            "YangMills.RG.BalabanCMP99ComplexSpecialLinearAdjointAction",
            "YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice",
            "YangMills.RG.BalabanCMP99SourceFlatPhysicalComplexModeAction",
            "YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport",
        ],
        None,
    ),
    (
        "eq360_regional_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
        None,
    ),
]

for index, (module, expected_axioms) in enumerate(MODULES, start=1):
    source = f"YangMills/RG/{module}.lean"
    audit = f"YangMills/RG/{module}Audit.lean"
    queue.extend([
        (
            f"eq360_regional_{index:02d}_{module.lower()}_source",
            [
                "lake", "env", "lean", source, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}.olean",
            ],
            None,
        ),
        (
            f"eq360_regional_{index:02d}_{module.lower()}_audit",
            [
                "lake", "env", "lean", audit, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean",
            ],
            expected_axioms,
        ),
    ])

queue.append(("eq360_regional_root", ["lake", "build", "YangMillsCore"], None))
runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
