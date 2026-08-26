#!/usr/bin/env python3
"""Cold Colab validation for the finite CMP99 (3.37)/(3.51) source gate.

The queue certifies the literal complex perturbation-domain package and the
internally constructed exponential-adjoint remainder with its quadratic
bound.  It does not accept a free nonlinear remainder, move 20/41, attain
window 15 or instantiate TermSource.
"""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.request


SOURCE_SHA = '1315643bad6c5176e1696d9e260cc9a43a5f0d3b'
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
    raise RuntimeError("EQ351_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("eq351_source_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("EQ351_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

MODULES = [
    ('BalabanCMP99Eq337PhysicalComplexPerturbationDomain', 1),
    ('BalabanCMP99Eq351PhysicalComplexOrientedPerturbation', 4),
    ('BalabanCMP99Eq351ExponentialAdjointRemainder', 4),
    ('BalabanCMP99Eq351ExponentialAdjointRemainderBound', 3),
]

runner.RUNNER_REV = 'eq351-exponential-adjoint-remainder-cold-v2'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq351-exponential-adjoint-remainder")
runner.EVIDENCE = Path("/content/hrpoly-eq351-exponential-adjoint-remainder-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq351-exponential-adjoint-remainder-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq351-exponential-adjoint-remainder-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMillsCore.lean': '37a0269d0fee02f1bfdd3d4c1c1e095239baba3218b97893ba0a8ca74c19474b',
    'YangMills/RG/BalabanCMP99Eq337PhysicalComplexPerturbationDomain.lean': '80c141368ce88667f863ca2d3633000fbf4a79f97c1a081487e6963ed52e0693',
    'YangMills/RG/BalabanCMP99Eq337PhysicalComplexPerturbationDomainAudit.lean': '6735053257486a5374108f20f3c695a77375efe213ff3f3e26a3c10caa7af507',
    'YangMills/RG/BalabanCMP99Eq351PhysicalComplexOrientedPerturbation.lean': 'bf9916731db27d98f59c47822f5461063e9fcca483c0ed359b0bf7b0c34beab4',
    'YangMills/RG/BalabanCMP99Eq351PhysicalComplexOrientedPerturbationAudit.lean': 'e45210b7698120b7768d46a8aa9d16a3b0f2c17ddaf82d75656f675bd3a35da4',
    'YangMills/RG/BalabanCMP99Eq351ExponentialAdjointRemainder.lean': '337663049a34327ea4151a363a6cf33582a8b32951740f4823283fc0e3fb0d78',
    'YangMills/RG/BalabanCMP99Eq351ExponentialAdjointRemainderAudit.lean': 'f63682f6e174d6cd7a4bc104de99836c18219f4d56d58da2da8f0afb698cea81',
    'YangMills/RG/BalabanCMP99Eq351ExponentialAdjointRemainderBound.lean': '11c36e862ad56e2e248afbdcdba9bb5f187ace460ed592d24026b4af5c436e0c',
    'YangMills/RG/BalabanCMP99Eq351ExponentialAdjointRemainderBoundAudit.lean': '3c01a91549cb76bd8b03b9bb081b2da14403892a420aa4fc39664f6edcf81cbe',
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
        "eq351_materialize_dependencies",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP98GAdConjugation",
            "YangMills.RG.BalabanCMP99Eq337PhysicalRealPerturbationDomain",
            "YangMills.RG.BalabanCMP99Eq337PhysicalComplexCovariantDerivative",
        ],
        None,
    ),
    (
        "eq351_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
        None,
    ),
]

for index, (module, expected_axioms) in enumerate(MODULES, start=1):
    source = f"YangMills/RG/{module}.lean"
    audit = f"YangMills/RG/{module}Audit.lean"
    queue.extend([
        (
            f"eq351_{index:02d}_{module.lower()}_source",
            [
                "lake", "env", "lean", source, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}.olean",
            ],
            None,
        ),
        (
            f"eq351_{index:02d}_{module.lower()}_audit",
            [
                "lake", "env", "lean", audit, "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean",
            ],
            expected_axioms,
        ),
    ])

queue.append(("eq351_root", ["lake", "build", "YangMillsCore"], None))
runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
