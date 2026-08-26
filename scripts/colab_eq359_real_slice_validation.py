#!/usr/bin/env python3
"""Cold Colab validation for the finite Eq. (3.59) compact real-slice gate.

The queue compiles five promoted PRE-VALIDATION source/audit pairs in
dependency order, checks twenty-four public declarations, builds YangMillsCore
from the same fresh checkout, and stops at the first real error.  It does not
move 20/41 or instantiate TermSource.
"""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.request


SOURCE_SHA = 'e0a2b346ceeb88f476cc80c53df7210b74ae77e0'
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
    raise RuntimeError("EQ359_REAL_SLICE_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("eq359_real_slice_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("EQ359_REAL_SLICE_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

MODULES = [
    ('BalabanCMP99SpecialUnitaryToSpecialLinearRealSlice', 5),
    ('BalabanCMP99Eq359OneScaleRealSlice', 4),
    ('BalabanCMP99Eq359TowerRealSliceAgreement', 3),
    ('BalabanCMP99PhysicalBackgroundRealSlice', 5),
    ('BalabanCMP99ComplexUbarSuccessorRealSlice', 7),
]

runner.RUNNER_REV = 'eq359-real-slice-promoted-cold-v1'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq359-real-slice")
runner.EVIDENCE = Path("/content/hrpoly-eq359-real-slice-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq359-real-slice-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq359-real-slice-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMillsCore.lean': 'c3281f3be85744e6066e9c554571162f99cf89ba1549943bd6faf3beb7bed95a',
    'YangMills/RG/BalabanCMP99SpecialUnitaryToSpecialLinearRealSlice.lean': '49b12079c6882ce8a0269478eaebdfd0dd478bd53e7c2d069f1e95d4970d3929',
    'YangMills/RG/BalabanCMP99SpecialUnitaryToSpecialLinearRealSliceAudit.lean': '36538f496b3941e6a54c4a802303efcdeabdae964579b3eaaa5b48378bf32482',
    'YangMills/RG/BalabanCMP99Eq359OneScaleRealSlice.lean': '39cdaa10036c4f2cdd366711c59499e93b826db8117b66ac08e048a87772f4ff',
    'YangMills/RG/BalabanCMP99Eq359OneScaleRealSliceAudit.lean': 'f94ec4db67ea0cea1e436ec30da66aaa640c7a2e578b15e20afd4f64c68a981b',
    'YangMills/RG/BalabanCMP99Eq359TowerRealSliceAgreement.lean': 'a3168b10ced9316e89b794a5c21abaad1de117c7624bdc284320ad782d8d7655',
    'YangMills/RG/BalabanCMP99Eq359TowerRealSliceAgreementAudit.lean': 'f7335e8c1cd0ddc3a1ab138cf9d2c33f14c247923a9ccdbc97c5753c010b96ed',
    'YangMills/RG/BalabanCMP99PhysicalBackgroundRealSlice.lean': '810d0593173ed6bb39fc74d0885bd882196a68c7a2a83f206708ceeb7ac855f4',
    'YangMills/RG/BalabanCMP99PhysicalBackgroundRealSliceAudit.lean': 'e38343c96d38fe0474c09600cc7e1fbbb27f7c494a7cae3dc17372083c3bcb94',
    'YangMills/RG/BalabanCMP99ComplexUbarSuccessorRealSlice.lean': '13af40b1e18b78cf0f04f3071a6f5a1fdaae15e2f5d0539ab5f28e85f34dd28b',
    'YangMills/RG/BalabanCMP99ComplexUbarSuccessorRealSliceAudit.lean': '6bb64575782451ff337693c07acf77331b769d4ce6416d5a325f4a0f9fb07fe5',
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
        "eq359_real_slice_materialize_dependencies",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99ComplexPhysicalRegionalTower",
            "YangMills.RG.BalabanCMP99SourceRegionalScale",
        ],
        None,
    ),
    (
        "eq359_real_slice_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
        None,
    ),
]

for index, (module, expected_axioms) in enumerate(MODULES, start=1):
    source = f"YangMills/RG/{module}.lean"
    audit = f"YangMills/RG/{module}Audit.lean"
    queue.extend([
        (
            f"eq359_real_slice_{index:02d}_{module.lower()}_source",
            [
                "lake", "env", "lean", source, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}.olean",
            ],
            None,
        ),
        (
            f"eq359_real_slice_{index:02d}_{module.lower()}_audit",
            [
                "lake", "env", "lean", audit, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean",
            ],
            expected_axioms,
        ),
    ])

queue.append(("eq359_real_slice_root", ["lake", "build", "YangMillsCore"], None))
runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
