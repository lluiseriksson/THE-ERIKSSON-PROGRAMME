#!/usr/bin/env python3
"""Cold Colab gate for the remaining Eq. (3.37) coordinate boundary.

The three PRE-VALIDATION source/audit pairs are compiled from one fresh source
checkpoint, their 57 declarations are audited, and ``YangMillsCore`` is built.
This intermediate gate does not move ``20/41`` or instantiate TermSource.
"""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.request


SOURCE_SHA = '573d70e09eb3f069cc3e86f43ab76b16a2349163'
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
    raise RuntimeError("EQ337_COVARIANT_DERIVATIVE_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("eq337_derivative_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("EQ337_COVARIANT_DERIVATIVE_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

MODULES = [
    ('BalabanCMP99Eq337PhysicalRealCovariantDerivative', 8),
    ('BalabanCMP99Eq337PhysicalComplexCovariantDerivative', 23),
    ('BalabanCMP99Eq337PhysicalComplexPerturbedBackground', 26),
]

runner.RUNNER_REV = 'eq337-complex-coordinate-promoted-cold-v2'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq337-covariant-derivative")
runner.EVIDENCE = Path("/content/hrpoly-eq337-covariant-derivative-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq337-covariant-derivative-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq337-covariant-derivative-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMillsCore.lean': '5283c06603a44906e4765c1c473ba431bbc41a4198e206492f8e015e47372c8e',
    'YangMills/RG/BalabanCMP99Eq337PhysicalRealCovariantDerivative.lean': 'fd13c9b57f0b60aef49134106c7d0e4e3fdf4aeafda9c3574f2e5fa63e67f02a',
    'YangMills/RG/BalabanCMP99Eq337PhysicalRealCovariantDerivativeAudit.lean': 'e15b8887cfe9259c8ff44d3cab05d51f110bd0573b1054696b15280b1e48c56f',
    'YangMills/RG/BalabanCMP99Eq337PhysicalComplexCovariantDerivative.lean': '8b2a3830ebd70561b1d08f388c6f8cb5f051b30f5da8d4c521cda84e1123b713',
    'YangMills/RG/BalabanCMP99Eq337PhysicalComplexCovariantDerivativeAudit.lean': '9ec01c5f72dbc1cf49eabfa3c12a84b8bbd9602950c47b35745352c0c0e1fcb9',
    'YangMills/RG/BalabanCMP99Eq337PhysicalComplexPerturbedBackground.lean': '7670b8e6ada64aa6f2549af712b20c6e9abefd9ed10beb33d94e166a6c876952',
    'YangMills/RG/BalabanCMP99Eq337PhysicalComplexPerturbedBackgroundAudit.lean': 'd85ee70b4d46e9b0993154eb71afddf77b8121b1259c175708445190fbbb7bd9',
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
queue = []
for index, (module, expected_axioms) in enumerate(MODULES, start=1):
    source = f"YangMills/RG/{module}.lean"
    audit = f"YangMills/RG/{module}Audit.lean"
    queue.extend([
        (
            f"eq337_covariant_derivative_{index:02d}_{module.lower()}_source",
            ["lake", "build", f"YangMills.RG.{module}"],
            None,
        ),
        (
            f"eq337_covariant_derivative_{index:02d}_{module.lower()}_audit",
            ["lake", "env", "lean", audit],
            expected_axioms,
        ),
    ])
queue.append((
    "eq337_covariant_derivative_root",
    ["lake", "build", "YangMillsCore"],
    None,
))
runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
