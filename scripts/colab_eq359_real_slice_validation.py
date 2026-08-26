#!/usr/bin/env python3
"""Cold Colab validation for the finite Eq. (3.59) compact real-slice gate.

The queue compiles six promoted PRE-VALIDATION source/audit pairs in
dependency order, checks thirty public declarations, builds YangMillsCore
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


SOURCE_SHA = '08039bcbc4bc74af072bef0252d7d559cbc80fe5'
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
    ('BalabanCMP99ComplexLocalizedUbarBackground', 4),
    ('BalabanCMP99ComplexUbarSuccessorRealSlice', 9),
]

runner.RUNNER_REV = 'eq359-real-slice-promoted-cold-v2'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq359-real-slice")
runner.EVIDENCE = Path("/content/hrpoly-eq359-real-slice-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq359-real-slice-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq359-real-slice-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMillsCore.lean': 'c3281f3be85744e6066e9c554571162f99cf89ba1549943bd6faf3beb7bed95a',
    'YangMills/RG/BalabanCMP99SpecialUnitaryToSpecialLinearRealSlice.lean': '0dd35a65c8c21033bb9b851ad48b68162dcb99ae745a8aa8a665faaf10299a27',
    'YangMills/RG/BalabanCMP99SpecialUnitaryToSpecialLinearRealSliceAudit.lean': '36538f496b3941e6a54c4a802303efcdeabdae964579b3eaaa5b48378bf32482',
    'YangMills/RG/BalabanCMP99Eq359OneScaleRealSlice.lean': '0b2033475470d4772cf9ca301f8ddeb4218ce878f493c0d286e087c1388b8a96',
    'YangMills/RG/BalabanCMP99Eq359OneScaleRealSliceAudit.lean': 'f94ec4db67ea0cea1e436ec30da66aaa640c7a2e578b15e20afd4f64c68a981b',
    'YangMills/RG/BalabanCMP99Eq359TowerRealSliceAgreement.lean': 'a3168b10ced9316e89b794a5c21abaad1de117c7624bdc284320ad782d8d7655',
    'YangMills/RG/BalabanCMP99Eq359TowerRealSliceAgreementAudit.lean': 'f7335e8c1cd0ddc3a1ab138cf9d2c33f14c247923a9ccdbc97c5753c010b96ed',
    'YangMills/RG/BalabanCMP99PhysicalBackgroundRealSlice.lean': '810d0593173ed6bb39fc74d0885bd882196a68c7a2a83f206708ceeb7ac855f4',
    'YangMills/RG/BalabanCMP99PhysicalBackgroundRealSliceAudit.lean': 'e38343c96d38fe0474c09600cc7e1fbbb27f7c494a7cae3dc17372083c3bcb94',
    'YangMills/RG/BalabanCMP99ComplexLocalizedUbarBackground.lean': '8af5790cd28ffb09810ba720f988e345d4de8b7df10b8af8e398fbbf2a0c1dbf',
    'YangMills/RG/BalabanCMP99ComplexLocalizedUbarBackgroundAudit.lean': '3b9be467c8bdbec0b8d52e15c2eaab433a0771c074631d5aa2f4a553f850f3b1',
    'YangMills/RG/BalabanCMP99ComplexUbarSuccessorRealSlice.lean': '9aa9f959139d15dad132fbb26893c5fc95b77ec74b0d2c6f0e5841e027143600',
    'YangMills/RG/BalabanCMP99ComplexUbarSuccessorRealSliceAudit.lean': '8160f2a58d7d1371acde1df6ccc5b944ad6c7ebda66aade43da0ce0f625dc651',
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
            "YangMills.RG.BalabanCMP99SourceFlatPhysicalComplexModeAction",
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
