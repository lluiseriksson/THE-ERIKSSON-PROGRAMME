#!/usr/bin/env python3
"""Cold Colab validation for the next finite C6d compact real-slice gate.

The queue compiles three promoted PRE-VALIDATION source/audit pairs in
dependency order, checks ten public declarations, builds YangMillsCore
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


SOURCE_SHA = '81cc22e41d46cce150c2a263c85e4acb90087153'
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
    raise RuntimeError("C6D_NEXT_REAL_SLICE_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("c6d_next_real_slice_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_NEXT_REAL_SLICE_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

MODULES = [
    ('BalabanCMP99Eq337PhysicalComplexBaselineRealSlice', 1),
    ('BalabanCMP99SourceRetainedFineOneCochainExtension', 7),
    ('BalabanCMP99SourcePhysicalRealSliceTower', 2),
]

runner.RUNNER_REV = 'c6d-next-real-slice-v3'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-c6d-next-real-slice")
runner.EVIDENCE = Path("/content/hrpoly-c6d-next-real-slice-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-next-real-slice-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-next-real-slice-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMillsCore.lean': '41bfd19dffe9995a98fed1b1e633c8e0c4f8d663076ee9b271621ea91ab878a1',
    'YangMills/RG/BalabanCMP99Eq337PhysicalComplexBaselineRealSlice.lean': '6d022ab4f12d979e4cb3a5e90cc04739ebec033487c71c1b4a12056ed0b980e5',
    'YangMills/RG/BalabanCMP99Eq337PhysicalComplexBaselineRealSliceAudit.lean': '4fd0833d973bc4f4e2b2609486eecfa47e1d25ce9eae346f7d96533cdd017a29',
    'YangMills/RG/BalabanCMP99SourceRetainedFineOneCochainExtension.lean': '6920eb88698be70cfff2077378a6e197ee553d65ef80cd518fe8a0ba801ae032',
    'YangMills/RG/BalabanCMP99SourceRetainedFineOneCochainExtensionAudit.lean': '6b589afafedc93478c39cd80cb10b704f467671699b6c43073101a1caef725ff',
    'YangMills/RG/BalabanCMP99SourcePhysicalRealSliceTower.lean': '2865ece151193d233bf9052bb0e35366960d50de0062d38215bb2d22bd9ecc17',
    'YangMills/RG/BalabanCMP99SourcePhysicalRealSliceTowerAudit.lean': '1c87b64500484f0215f834d9b472c7497e21300d95e98ecab839850acec84dc7',
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
        "c6d_next_real_slice_materialize_dependencies",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99ComplexPhysicalRegionalTower",
            "YangMills.RG.BalabanCMP99ComplexUbarSpecialLinear",
            "YangMills.RG.BalabanCMP99SourceRegionalScale",
            "YangMills.RG.BalabanCMP99SourceFlatPhysicalComplexModeAction",
            "YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice",
            "YangMills.RG.BalabanCMP99SourceRetainedFineExtension",
            "YangMills.RG.BalabanCMP99Eq359TowerRealSliceAgreement",
            "YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime",
        ],
        None,
    ),
    (
        "c6d_next_real_slice_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
        None,
    ),
]

for index, (module, expected_axioms) in enumerate(MODULES, start=1):
    source = f"YangMills/RG/{module}.lean"
    audit = f"YangMills/RG/{module}Audit.lean"
    queue.extend([
        (
            f"c6d_next_real_slice_{index:02d}_{module.lower()}_source",
            [
                "lake", "env", "lean", source, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}.olean",
            ],
            None,
        ),
        (
            f"c6d_next_real_slice_{index:02d}_{module.lower()}_audit",
            [
                "lake", "env", "lean", audit, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean",
            ],
            expected_axioms,
        ),
    ])

queue.append(("c6d_next_real_slice_root", ["lake", "build", "YangMillsCore"], None))
runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
