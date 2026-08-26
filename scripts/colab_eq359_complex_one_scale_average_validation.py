#!/usr/bin/env python3
"""Cold Colab validation for the source-specific Eq. (3.59) two-tower pair.

The source checkpoint contains seven promoted PRE-VALIDATION source/audit
pairs. The queue compiles them in dependency order, audits their thirty-one
public declarations, builds ``YangMillsCore`` from the same fresh checkout,
and stops at the first real error. It does not move ``20/41`` or instantiate
``TermSource``.
"""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.request


SOURCE_SHA = 'd1864ae0305b87b3a1812be29ca55577b5cd3240'
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
    raise RuntimeError("EQ359_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("eq359_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("EQ359_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

MODULES = [
    ('BalabanCMP99ComplexSpecialLinearAdjointAction', 3),
    ('BalabanCMP99ComplexTransportedBlockAverage', 8),
    ('BalabanCMP99ComplexRegionalTower', 6),
    ('BalabanCMP99ComplexPhysicalRegionalTower', 6),
    ('BalabanCMP99Eq359ComplexClosedPhysicalTower', 1),
    ('BalabanCMP99Eq359ComplexRegionalTowerPair', 6),
    ('BalabanCMP99Eq359ComplexClosedPhysicalTowerPair', 1),
]

runner.RUNNER_REV = 'eq359-complex-one-scale-average-promoted-cold-v1'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq359-complex-one-scale-average")
runner.EVIDENCE = Path("/content/hrpoly-eq359-complex-one-scale-average-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq359-complex-one-scale-average-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq359-complex-one-scale-average-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMillsCore.lean': '181aab410c53915b564dc0488c401403a4d3191e3fcca14696cad937ac1371fb',
    'YangMills/RG/BalabanCMP99ComplexSpecialLinearAdjointAction.lean': '40ff2ba9507704f2c1af31ae0b47b133e04eb28761840ff09c7ed6600b241454',
    'YangMills/RG/BalabanCMP99ComplexSpecialLinearAdjointActionAudit.lean': 'd11825fb75f15dfb30c5ae46b283e824eb2925f9e5e18f9c7909163797482e1d',
    'YangMills/RG/BalabanCMP99ComplexTransportedBlockAverage.lean': '7b6a53b6a8577b732eeca8c8a25fcba63db14b56d6ca50b9029162bd1d6bba2c',
    'YangMills/RG/BalabanCMP99ComplexTransportedBlockAverageAudit.lean': 'dac59d9638c535f2d8583d8b7168ebb51e09f22bd613e8753ab092fc0bffca30',
    'YangMills/RG/BalabanCMP99ComplexRegionalTower.lean': 'ecbc6808f3e15c83507d212c80c31ab8807c04c58833fcedc75b91b53401f127',
    'YangMills/RG/BalabanCMP99ComplexRegionalTowerAudit.lean': 'f278a5f081415e2737ec2665ceca2d091202ec2e8ba0497e5f06c2893325353e',
    'YangMills/RG/BalabanCMP99ComplexPhysicalRegionalTower.lean': 'bf81190bbaa90d83f9f06ea600a95a11572a7dea481b293a9fc1d685a1098701',
    'YangMills/RG/BalabanCMP99ComplexPhysicalRegionalTowerAudit.lean': '9bb296c9a32a7b0116cb338b53176765d38313ef28de8ef19bcaff4d4a5d6a5b',
    'YangMills/RG/BalabanCMP99Eq359ComplexClosedPhysicalTower.lean': 'd8cc07217f1d4ec7d034c8cbc75e3c1b350da28027e1e147bc17289f8e9fa71e',
    'YangMills/RG/BalabanCMP99Eq359ComplexClosedPhysicalTowerAudit.lean': 'f3782dea68990ea0469fd72955a70f23ae9bfd4d5fa6c0fc0d3fdfb48ce275a3',
    'YangMills/RG/BalabanCMP99Eq359ComplexRegionalTowerPair.lean': '1a17756c7177d1361f9feab5ddc2498c0f9b5e5acbef83b63f6ac1e67b6e7a9d',
    'YangMills/RG/BalabanCMP99Eq359ComplexRegionalTowerPairAudit.lean': '9cc2d6a6d3895c00b0987acbef4a5d4b74a7662c38ef65225718598e03bd0a7a',
    'YangMills/RG/BalabanCMP99Eq359ComplexClosedPhysicalTowerPair.lean': 'eb3a2465debf42f15a6562cbee02d3a571c41eb700fdebd6205144967aa6f6ec',
    'YangMills/RG/BalabanCMP99Eq359ComplexClosedPhysicalTowerPairAudit.lean': 'd92d1e78d4faa06b6722a2f7ab46435ef0e032ef472ad52e7d3a2500bf4f711d',
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
        "eq359_materialize_dependencies",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99Eq337ComplexClosedRecursiveBackground",
            "YangMills.RG.BalabanCMP99SourceWeightedPhysicalTower",
        ],
        None,
    ),
    (
        "eq359_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
        None,
    ),
]

for index, (module, expected_axioms) in enumerate(MODULES, start=1):
    source = f"YangMills/RG/{module}.lean"
    audit = f"YangMills/RG/{module}Audit.lean"
    queue.extend([
        (
            f"eq359_{index:02d}_{module.lower()}_source",
            [
                "lake", "env", "lean", source, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}.olean",
            ],
            None,
        ),
        (
            f"eq359_{index:02d}_{module.lower()}_audit",
            [
                "lake", "env", "lean", audit, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean",
            ],
            expected_axioms,
        ),
    ])

queue.append(("eq359_root", ["lake", "build", "YangMillsCore"], None))
runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
