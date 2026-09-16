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


SOURCE_SHA = '77c0e4834ce69d8b174d37aeefac56fd5b06b5ad'
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
    ('BalabanCMP99Eq337PhysicalRealPerturbationDomain', 7),
    ('BalabanCMP99Eq337PhysicalComplexPerturbationDomain', 1),
    ('BalabanCMP99Eq351PhysicalComplexOrientedPerturbation', 4),
    ('BalabanCMP99Eq351ExponentialAdjointRemainder', 4),
    ('BalabanCMP99Eq351ExponentialAdjointRemainderBound', 3),
]

runner.RUNNER_REV = 'eq351-exponential-adjoint-remainder-cold-v4'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq351-exponential-adjoint-remainder")
runner.EVIDENCE = Path("/content/hrpoly-eq351-exponential-adjoint-remainder-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq351-exponential-adjoint-remainder-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq351-exponential-adjoint-remainder-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMillsCore.lean': '23a4b0caf8a0246a21eb0538720d555854e651d7cccd3a1aef0b3ab73b02698e',
    'YangMills/RG/BalabanCMP99Eq337PhysicalRealPerturbationDomain.lean': '1b9b84a5ef5b87d8af7fb25e6f11ae3a0f4be3045a37c311a23bc30dd92d1a06',
    'YangMills/RG/BalabanCMP99Eq337PhysicalRealPerturbationDomainAudit.lean': '10da77bf0cae99a37a2156a1704b8358f1af31eae3d3ecd54ebc0d2e15882014',
    'YangMills/RG/BalabanCMP99Eq337PhysicalComplexPerturbationDomain.lean': '80c141368ce88667f863ca2d3633000fbf4a79f97c1a081487e6963ed52e0693',
    'YangMills/RG/BalabanCMP99Eq337PhysicalComplexPerturbationDomainAudit.lean': '6735053257486a5374108f20f3c695a77375efe213ff3f3e26a3c10caa7af507',
    'YangMills/RG/BalabanCMP99Eq351PhysicalComplexOrientedPerturbation.lean': 'a612306b460abadaf841fdf9164e7191050d2788257985c9ac42bed4639a4b3b',
    'YangMills/RG/BalabanCMP99Eq351PhysicalComplexOrientedPerturbationAudit.lean': 'e45210b7698120b7768d46a8aa9d16a3b0f2c17ddaf82d75656f675bd3a35da4',
    'YangMills/RG/BalabanCMP99Eq351ExponentialAdjointRemainder.lean': '337663049a34327ea4151a363a6cf33582a8b32951740f4823283fc0e3fb0d78',
    'YangMills/RG/BalabanCMP99Eq351ExponentialAdjointRemainderAudit.lean': 'f63682f6e174d6cd7a4bc104de99836c18219f4d56d58da2da8f0afb698cea81',
    'YangMills/RG/BalabanCMP99Eq351ExponentialAdjointRemainderBound.lean': '44a28e943f490ae28631ac77bf4cb6d256deb77b8fe28c4ac674c200c8605e55',
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
