#!/usr/bin/env python3
"""Generate the Step 8b.24 C6c.1 D1--D4d Colab validation runner."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "bcc852cee5e709bff91fad7de26fa21cff754e1f/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)
BRICKS: tuple[tuple[str, int], ...] = (
    ("BalabanCMP89Eq249FineLatticeLeftDerivativeMassUniformHolomorphy", 2),
    ("BalabanCMP89Eq249FineLatticeLeftDerivativeOneCoordinateContourShift", 1),
    ("BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescope", 5),
    ("BalabanCMP89Eq249FineLatticeLeftDerivativeMassUniformBound", 6),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativeResidueShift", 7),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativePeriodization", 5),
    ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative", 7),
)


def git(*args: str, binary: bool = False) -> bytes | str:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if child.returncode != 0:
        raise SystemExit(
            "GIT_FAIL " + " ".join(args) + "\n"
            + child.stderr.decode("utf-8", errors="replace")
        )
    return child.stdout if binary else child.stdout.decode("utf-8").strip()


def blob(source_sha: str, path: str) -> bytes:
    return git("cat-file", "blob", f"{source_sha}:{path}", binary=True)  # type: ignore[return-value]


def pair_paths(module: str) -> tuple[str, str]:
    stem = f"YangMills/RG/{module}"
    return stem + ".lean", stem + "Audit.lean"


def source_paths() -> list[str]:
    paths = [path for module, _ in BRICKS for path in pair_paths(module)]
    if len(paths) != 14 or len(paths) != len(set(paths)):
        raise RuntimeError("D1--D4d validation scope mismatch")
    return paths


def q(value: str) -> str:
    return repr(value)


def generate(source_sha: str) -> str:
    resolved = git("rev-parse", f"{source_sha}^{{commit}}")
    if resolved != source_sha:
        raise SystemExit(f"SOURCE_SHA_NOT_FULL_OR_MISMATCH={resolved}")
    paths = source_paths()
    rows: list[tuple[str, str]] = []
    for path in paths:
        data = blob(source_sha, path)
        text = data.decode("utf-8")
        if "PRE-VALIDATION:" not in text:
            raise SystemExit(f"DERIVATIVE_MISSING_PRE_VALIDATION={path}")
        if any(token in text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"FORBIDDEN_PLACEHOLDER={path}")
        rows.append((path, hashlib.sha256(data).hexdigest()))
    if sum(count for _, count in BRICKS) != 33:
        raise SystemExit("DERIVATIVE_AXIOM_TOTAL_MISMATCH")

    blob_rows = "\n".join(f"    {q(path)}: {q(digest)}," for path, digest in rows)
    queue_rows: list[str] = []
    for index, (module, count) in enumerate(BRICKS, start=1):
        slug = module.removeprefix("Balaban").lower()
        queue_rows.append(
            "    (\n"
            f"        {q(f'{index:02d}_{slug}_focal')},\n"
            f"        ['lake', 'build', {q('YangMills.RG.' + module)}],\n"
            "        None,\n"
            "    ),\n"
            "    (\n"
            f"        {q(f'{index:02d}_{slug}_audit')},\n"
            "        ['lake', 'env', 'lean', "
            f"{q('YangMills/RG/' + module + 'Audit.lean')}],\n"
            f"        {count},\n"
            "    ),"
        )
    queue = "\n".join(queue_rows)

    return f'''#!/usr/bin/env python3
"""Colab gate for Step 8b.24 C6c.1 D1--D4d.

This validates the ambient complex zero-mass left-derivative source/owner
branch only.  The regional derivative field, H1--H5, window 15, terminal
fields and TermSource remain open.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request

HERE = Path("/content")
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
BASE_RUNNER_URL = {q(BASE_RUNNER_URL)}
BASE_RUNNER_SHA256 = {q(BASE_RUNNER_SHA256)}
with urllib.request.urlopen(BASE_RUNNER_URL) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location("step8b24_c6c1_derivative_base_runner", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {{BASE_RUNNER}}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "step8b24-c6c1-derivative-v1"
runner.SOURCE_SHA = {q(source_sha)}
runner.ROOT = Path("/content/hrpoly-step8b24-c6c1-derivative")
runner.EVIDENCE = Path("/content/hrpoly-step8b24-c6c1-derivative-evidence")
runner.ARCHIVE = Path("/content/hrpoly-step8b24-c6c1-derivative-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-step8b24-c6c1-derivative-paths.txt")
runner.SOURCE_BLOBS = {{
{blob_rows}
}}
runner.QUEUE = [
{queue}
]

if __name__ == "__main__":
    try:
        from google.colab import runtime
        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    raise SystemExit(runner.main())
'''


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "scripts" / "colab_step8b24_c6c1_derivative_validation.py",
    )
    args = parser.parse_args()
    content = generate(args.source_sha)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "STEP8B24_C6C1_DERIVATIVE_RUNNER_GENERATED "
        f"source_sha={args.source_sha} files=14 bricks=7 stages=14 "
        f"axiom_blocks=33 sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
