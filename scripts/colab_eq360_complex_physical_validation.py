#!/usr/bin/env python3
"""Cold validation of the auxiliary complex Eq. (3.60) algebra.

The queue checks five promoted PRE-VALIDATION source/audit pairs (thirty-one
public declarations) and YangMillsCore from one exact fresh checkout.  This
inventory still accepts independent Laplacian backgrounds and does not prove
the printed (3.51)--(3.54) source decomposition.  It therefore does not assert
the source-facing Eq. (3.60) producer, the local bound, the resolvent, any of
the four actions, window 15, 20/41, or a TermSource inhabitant.
"""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.request


SOURCE_SHA = 'dd8f3b3d32e3f5773ed2b6fd701ee8cd13035b7b'
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/" f"{SOURCE_SHA}/scripts/colab_qprime_row_validation.py"
)
BASE_SHA256 = 'd06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee'
BASE_PATH = Path("/content/colab_qprime_row_validation.py")

with urllib.request.urlopen(BASE_URL) as response:
    base_source = response.read()
measured = hashlib.sha256(base_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != BASE_SHA256:
    raise RuntimeError("EQ360_COMPLEX_PHYSICAL_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("eq360_complex_physical_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("EQ360_COMPLEX_PHYSICAL_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

MODULES = [
    ('BalabanCMP99Eq360ComplexRegionalLaplacian', 8),
    ('BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice', 3),
    ('BalabanCMP99Eq360ComplexLocalLaplacianPerturbation', 3),
    ('BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation', 3),
    ('BalabanCMP99Eq360ComplexClosedPhysicalPrecision', 14),
]

runner.RUNNER_REV = 'eq360-complex-physical-v1'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq360-complex-physical")
runner.EVIDENCE = Path("/content/hrpoly-eq360-complex-physical-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq360-complex-physical-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq360-complex-physical-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMillsCore.lean': '982e5963245721317a9413dc9a5bbe6beae51a3c45d8f3c3139bb934d81225fd',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacian.lean': 'c08cf0f95ca2f7d47e3b6c2b20ad30f1236458315aed996624238703d9e7e835',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacianAudit.lean': 'ee79bde256a3b422c9f4560a361046a7ef715d8298fdf49545f114af77a82310',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice.lean': '8c4524096bb1f3ecd6b6067646dc0cdbbd66cce886f0efd3963b91f9b5bf4ae8',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacianRealSliceAudit.lean': '05001a36e478c2dce77508383d902bfd668df6c521869c649c980d1faea83d85',
    'YangMills/RG/BalabanCMP99Eq360ComplexLocalLaplacianPerturbation.lean': '217ead37fdd0f9b8ddb19ee1131ab5611e845e0f0bc0f98c461ebb3827861b75',
    'YangMills/RG/BalabanCMP99Eq360ComplexLocalLaplacianPerturbationAudit.lean': '21019df381378288952aa6484cdd19e300cdcd6571d3e05ed972694bec56525c',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation.lean': '596bf662c94c512757d4f0c71caa2fa99d2ce9000dbc2073d6daddea6ef38f0a',
    'YangMills/RG/BalabanCMP99Eq360ComplexRegionalPrecisionPerturbationAudit.lean': '5e4b10d9c116f122bead2446fd4eb7fd63cd251284cfb33248e4938e02dd0c30',
    'YangMills/RG/BalabanCMP99Eq360ComplexClosedPhysicalPrecision.lean': '26a4b76079970178f8041d9fe2433b56e5374ee3036813566148804287e62cd2',
    'YangMills/RG/BalabanCMP99Eq360ComplexClosedPhysicalPrecisionAudit.lean': '0087bacd7a6f770408d716c9a48aa46485c5532e62214850d51ae736ca34f031',
}


def capturing_run(stage: str, command: list[str], *, cwd: Path | None = None) -> str:
    started = time.perf_counter()
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    child = subprocess.run(
        command, cwd=cwd, env=os.environ.copy(), text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    output = child.stdout
    print(output, flush=True)
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    (runner.EVIDENCE / f"{stage}.stdout").write_text(
        output, encoding="utf-8", newline="\n"
    )
    runner.RECORDS.append({
        "stage": stage,
        "exit": child.returncode,
        "seconds": elapsed,
        "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
    })
    print(
        "STAGE=" + stage + " EXIT=" + str(child.returncode)
        + " SECONDS=%.3f" % elapsed, flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


runner.run = capturing_run
queue = [
    (
        "eq360_complex_physical_materialize_dependencies",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99Eq359ComplexClosedPhysicalTowerPair",
            "YangMills.RG.BalabanCMP99Eq359TowerRealSliceAgreement",
        ],
        None,
    ),
    (
        "eq360_complex_physical_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
        None,
    ),
]
for index, (module, expected_axioms) in enumerate(MODULES, start=1):
    source = f"YangMills/RG/{module}.lean"
    audit = f"YangMills/RG/{module}Audit.lean"
    queue += [
        (
            f"eq360_complex_physical_{index:02d}_{module.lower()}_source",
            ["lake", "env", "lean", source, "-o",
             f".lake/build/lib/lean/YangMills/RG/{module}.olean"],
            None,
        ),
        (
            f"eq360_complex_physical_{index:02d}_{module.lower()}_audit",
            ["lake", "env", "lean", audit, "-o",
             f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean"],
            expected_axioms,
        ),
    ]
queue.append(("eq360_complex_physical_root", ["lake", "build", "YangMillsCore"], None))
runner.QUEUE = queue

if __name__ == "__main__":
    raise SystemExit(runner.main())
