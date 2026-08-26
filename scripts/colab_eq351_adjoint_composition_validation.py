#!/usr/bin/env python3
"""Cold validation of the literal CMP99 (3.50) positive-bond gate.

The queue certifies the complex adjoint group law and the canonical
`exp(i eta A'(b)) U(b)` factorization.  It does not prove the full (3.51)
regional regrouping, move 20/41, attain window 15 or instantiate TermSource.
"""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.request


SOURCE_SHA = '0c88ed3c45626592367e2091a5f54c69cb624e3a'
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
    raise RuntimeError("EQ351_ADJOINT_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("eq351_adjoint_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("EQ351_ADJOINT_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

MODULES = [
    ('BalabanCMP99ComplexSpecialLinearAdjointComposition', 1),
    ('BalabanCMP99Eq351PhysicalComplexPositiveBondFactorization', 6),
]

runner.RUNNER_REV = 'eq351-adjoint-composition-cold-v1'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq351-adjoint-composition")
runner.EVIDENCE = Path("/content/hrpoly-eq351-adjoint-composition-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq351-adjoint-composition-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq351-adjoint-composition-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMillsCore.lean': 'eb460cec95fc88f8f751858b30f39c624d42e7bd266cc5942b8b56b7d6548e08',
    'YangMills/RG/BalabanCMP99ComplexSpecialLinearAdjointComposition.lean': '2e0b2711d43899d58a723aac2a55d0707d32b2ea67435f1cbac88f399bdee33f',
    'YangMills/RG/BalabanCMP99ComplexSpecialLinearAdjointCompositionAudit.lean': 'bb65505690baeefe1d0e9be0dfbfec4400f8c2080ce8523c8c2fe2cc0554543b',
    'YangMills/RG/BalabanCMP99Eq351PhysicalComplexPositiveBondFactorization.lean': '455d62543cf2add00dc18258cf0531961eab6c4451398cf0fbabeae594d24e0d',
    'YangMills/RG/BalabanCMP99Eq351PhysicalComplexPositiveBondFactorizationAudit.lean': 'a8dd09186034e5984876d908845c50fbe2f405b64b86a453bbc96b1f2ebaa4d1',
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
        "eq351_adjoint_materialize_dependencies",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99ComplexSpecialLinearAdjointAction",
            "YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice",
        ],
        None,
    ),
    (
        "eq351_adjoint_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
        None,
    ),
]

for index, (module, expected_axioms) in enumerate(MODULES, start=1):
    source = f"YangMills/RG/{module}.lean"
    audit = f"YangMills/RG/{module}Audit.lean"
    queue.extend([
        (
            f"eq351_adjoint_{index:02d}_{module.lower()}_source",
            [
                "lake", "env", "lean", source, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}.olean",
            ],
            None,
        ),
        (
            f"eq351_adjoint_{index:02d}_{module.lower()}_audit",
            [
                "lake", "env", "lean", audit, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean",
            ],
            expected_axioms,
        ),
    ])

queue.append(("eq351_adjoint_root", ["lake", "build", "YangMillsCore"], None))
runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
