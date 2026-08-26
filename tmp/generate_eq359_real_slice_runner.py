#!/usr/bin/env python3
"""Generate a pinned cold Colab runner for the Eq. (3.59) real-slice gate."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "scripts" / "colab_eq359_real_slice_validation.py"
BASE_RUNNER = "scripts/colab_qprime_row_validation.py"
MODULES = (
    ("BalabanCMP99SpecialUnitaryToSpecialLinearRealSlice", 5),
    ("BalabanCMP99Eq359OneScaleRealSlice", 4),
    ("BalabanCMP99Eq359TowerRealSliceAgreement", 3),
    ("BalabanCMP99PhysicalBackgroundRealSlice", 5),
    ("BalabanCMP99ComplexUbarSuccessorRealSlice", 7),
)


def git(*args: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if child.returncode != 0:
        raise RuntimeError(
            "GIT_FAILED=" + " ".join(args) + ":"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def require_commit(sha: str, label: str) -> None:
    if re.fullmatch(r"[0-9a-f]{40}", sha) is None:
        raise RuntimeError(f"{label}_SHA_INVALID")
    if git("rev-parse", f"{sha}^{{commit}}").decode().strip() != sha:
        raise RuntimeError(f"{label}_COMMIT_MISMATCH")


def blob(sha: str, relative: str) -> bytes:
    return git("cat-file", "blob", f"{sha}:{relative}")


def digest(sha: str, relative: str) -> str:
    return hashlib.sha256(blob(sha, relative)).hexdigest()


def render(source_sha: str, runner_rev: str) -> str:
    base_hash = digest(source_sha, BASE_RUNNER)
    tracked = ["YangMillsCore.lean"]
    for module, _ in MODULES:
        tracked.extend(
            (
                f"YangMills/RG/{module}.lean",
                f"YangMills/RG/{module}Audit.lean",
            )
        )
    hashes = {relative: digest(source_sha, relative) for relative in tracked}
    source_blob_lines = "\n".join(
        f"    {relative!r}: {value!r}," for relative, value in hashes.items()
    )
    module_lines = "\n".join(
        f"    ({module!r}, {expected})," for module, expected in MODULES
    )
    return f'''#!/usr/bin/env python3
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


SOURCE_SHA = {source_sha!r}
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    f"{{SOURCE_SHA}}/{BASE_RUNNER}"
)
BASE_SHA256 = {base_hash!r}
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
{module_lines}
]

runner.RUNNER_REV = {runner_rev!r}
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq359-real-slice")
runner.EVIDENCE = Path("/content/hrpoly-eq359-real-slice-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq359-real-slice-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq359-real-slice-paths.txt")
runner.SOURCE_BLOBS = {{
{source_blob_lines}
}}


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
    (runner.EVIDENCE / f"{{stage}}.stdout").write_text(
        output, encoding="utf-8", newline="\\n"
    )
    runner.RECORDS.append(
        {{
            "stage": stage,
            "exit": child.returncode,
            "seconds": elapsed,
            "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
        }}
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
    source = f"YangMills/RG/{{module}}.lean"
    audit = f"YangMills/RG/{{module}}Audit.lean"
    queue.extend([
        (
            f"eq359_real_slice_{{index:02d}}_{{module.lower()}}_source",
            [
                "lake", "env", "lean", source, "-o",
                f".lake/build/lib/lean/YangMills/RG/{{module}}.olean",
            ],
            None,
        ),
        (
            f"eq359_real_slice_{{index:02d}}_{{module.lower()}}_audit",
            [
                "lake", "env", "lean", audit, "-o",
                f".lake/build/lib/lean/YangMills/RG/{{module}}Audit.olean",
            ],
            expected_axioms,
        ),
    ])

queue.append(("eq359_real_slice_root", ["lake", "build", "YangMillsCore"], None))
runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
'''


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    require_commit(args.source_sha, "SOURCE")
    content = render(args.source_sha, args.runner_rev)
    compile(content, str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "EQ359_REAL_SLICE_RUNNER_GENERATED "
        f"source_sha={args.source_sha} runner_rev={args.runner_rev} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
