#!/usr/bin/env python3
"""Cold Colab seal for the closed physical Eq. (3.37) recursion.

The source checkpoint contains three promoted PRE-VALIDATION source/audit
pairs. The queue compiles them in dependency order, audits fourteen public
declarations, builds ``YangMillsCore`` from the same fresh checkout, and stops
at the first real error. It does not move ``20/41`` or instantiate TermSource.
"""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.request


SOURCE_SHA = '6459baccb7d96ed40a0576a362d91a52c1f8888a'
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
    raise RuntimeError("EQ337_CLOSED_PHYSICAL_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("eq337_closed_physical_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("EQ337_CLOSED_PHYSICAL_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

MODULES = [
    ('BalabanCMP99Eq337ComplexClosedRadiusPhysicalBridge', 7),
    ('BalabanCMP99Eq337ComplexClosedRadiusPhysicalGates', 5),
    ('BalabanCMP99Eq337ComplexClosedRecursiveBackground', 2),
]

runner.RUNNER_REV = 'eq337-closed-physical-recursion-promoted-cold-v1'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq337-closed-physical-recursion")
runner.EVIDENCE = Path("/content/hrpoly-eq337-closed-physical-recursion-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq337-closed-physical-recursion-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq337-closed-physical-recursion-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMillsCore.lean': '5283c06603a44906e4765c1c473ba431bbc41a4198e206492f8e015e47372c8e',
    'YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusPhysicalBridge.lean': '856e584a7b8e81544d66314ea68c2cb63cdb0cd2ea7c7658bce46680c228e3ec',
    'YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusPhysicalBridgeAudit.lean': '687375fc504a04a9c89a911284d663eaf93ff1724520f0b35335ca1aebcf0485',
    'YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusPhysicalGates.lean': 'ace4b6000866004fb4a33aec8f9b4cc72829231ba8123917f7ab4e48ee53f851',
    'YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusPhysicalGatesAudit.lean': 'eb7da0b899bbbb8a99b8df1eba6713e207c47f2bbf71840a0f483bcc3eda6f91',
    'YangMills/RG/BalabanCMP99Eq337ComplexClosedRecursiveBackground.lean': 'c35c96e1554102ce131dea39fb27f11da59b272683b6448bacad35d1c5f38e6e',
    'YangMills/RG/BalabanCMP99Eq337ComplexClosedRecursiveBackgroundAudit.lean': 'b23249dedbb5be7b05f1637be360026ee821493bf9d2dc629d0a214574c5a294',
}


def capturing_run(stage: str, command: list[str], *, cwd: Path | None = None) -> str:
    """Persist exact combined stdout for durable archive verification."""
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
        "eq337_closed_physical_materialize_dependencies",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99Eq337ComplexClosedRadiusScalar",
            "YangMills.RG.BalabanCMP99ComplexUbarSmallFieldPropagation",
            "YangMills.RG.BalabanCMP99SourceRegionalLiftTower",
        ],
        None,
    ),
    (
        "eq337_closed_physical_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
        None,
    ),
]

for index, (module, expected_axioms) in enumerate(MODULES, start=1):
    source = f"YangMills/RG/{module}.lean"
    audit = f"YangMills/RG/{module}Audit.lean"
    queue.extend([
        (
            f"eq337_closed_physical_{index:02d}_{module.lower()}_source",
            [
                "lake", "env", "lean", source, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}.olean",
            ],
            None,
        ),
        (
            f"eq337_closed_physical_{index:02d}_{module.lower()}_audit",
            [
                "lake", "env", "lean", audit, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean",
            ],
            expected_axioms,
        ),
    ])

queue.append((
    "eq337_closed_physical_root",
    ["lake", "build", "YangMillsCore"],
    None,
))
runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
