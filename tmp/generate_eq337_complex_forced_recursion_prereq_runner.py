#!/usr/bin/env python3
"""Generate the pinned Colab gate for the complex-recursion prerequisites.

The gate is deliberately smaller than the final forced recursion.  It first
checks the Mathlib-facing inverse-radius reproduction, then materializes and
audits the project inverse-radius theorem and the all-orientation complex
small-field producer.  It stops at the first error and never removes
PRE-VALIDATION or changes the live ``20/41`` counter.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = (
    ROOT / "scripts" /
    "colab_eq337_complex_forced_recursion_prereq_validation.py"
)
BASE_PATH = "scripts/colab_qprime_row_validation.py"
EXPECTED_BASE_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)
PATHS = (
    "tmp/CMP99ComplexInverseRadius.repro.lean",
    "tmp/BalabanCMP99ComplexInverseRadius.draft.lean",
    "tmp/BalabanCMP99ComplexInverseRadiusAudit.draft.lean",
    "tmp/BalabanCMP99ComplexUbarSmallFieldPropagation.draft.lean",
    "tmp/BalabanCMP99ComplexUbarSmallFieldPropagationAudit.draft.lean",
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


def require_commit(sha: str) -> None:
    if re.fullmatch(r"[0-9a-f]{40}", sha) is None:
        raise SystemExit("SOURCE_SHA_FORMAT_INVALID")
    if git("rev-parse", f"{sha}^{{commit}}") != sha:
        raise SystemExit("SOURCE_SHA_RESOLUTION_MISMATCH")


def blob(sha: str, path: str) -> bytes:
    return git("cat-file", "blob", f"{sha}:{path}", binary=True)  # type: ignore[return-value]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require_prevalidation(sha: str, path: str) -> str:
    data = blob(sha, path)
    if b"PRE-VALIDATION" not in data:
        raise SystemExit("PREVALIDATION_MARKER_MISSING=" + path)
    return digest(data)


def render(source_sha: str, runner_rev: str) -> str:
    base_hash = digest(blob(source_sha, BASE_PATH))
    if base_hash != EXPECTED_BASE_SHA256:
        raise SystemExit(
            f"BASE_RUNNER_HASH_DRIFT={base_hash} WANT={EXPECTED_BASE_SHA256}"
        )
    source_blobs = {
        path: require_prevalidation(source_sha, path) for path in PATHS
    }
    blob_lines = "\n".join(
        f"    {path!r}: {sha!r}," for path, sha in source_blobs.items()
    )
    return f'''#!/usr/bin/env python3
"""Pinned Colab gate for the complex forced-recursion prerequisites.

This diagnostic compiles the inverse-radius repro, the source theorem and its
audit, then the all-orientation small-field producer and its audit.  It is
stop-on-first-error and does not promote source or move ``20/41``.
"""

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = {source_sha!r}
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    f"{{SOURCE_SHA}}/{BASE_PATH}"
)
BASE_SHA256 = {EXPECTED_BASE_SHA256!r}
BASE_FILE = Path("/content/colab_qprime_row_validation.py")

with urllib.request.urlopen(BASE_URL) as response:
    base_source = response.read()
measured = hashlib.sha256(base_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != BASE_SHA256:
    raise RuntimeError("COMPLEX_RECURSION_PREREQ_BASE_HASH_MISMATCH")
BASE_FILE.write_bytes(base_source)
spec = importlib.util.spec_from_file_location(
    "complex_recursion_prereq_base", BASE_FILE
)
if spec is None or spec.loader is None:
    raise RuntimeError("COMPLEX_RECURSION_PREREQ_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = {runner_rev!r}
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-complex-recursion-prereq")
runner.EVIDENCE = Path("/content/hrpoly-complex-recursion-prereq-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-complex-recursion-prereq-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-complex-recursion-prereq-paths.txt"
)
runner.SOURCE_BLOBS = {{
{blob_lines}
}}

runner.QUEUE = [
    (
        "complex_recursion_prereq_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG",
         ".lake/build/lib/lean/tmp"],
        None,
    ),
    (
        "complex_inverse_radius_repro",
        [
            "lake", "env", "lean",
            "tmp/CMP99ComplexInverseRadius.repro.lean", "-o",
            ".lake/build/lib/lean/tmp/CMP99ComplexInverseRadius.repro.olean",
        ],
        None,
    ),
    (
        "complex_recursion_prereq_materialize_dependencies",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius",
            "YangMills.RG.BalabanCMP99SourceUbarSmallFieldPropagation",
            "YangMills.RG.BalabanCMP99ComplexUbarSpecialLinear",
        ],
        None,
    ),
    (
        "complex_inverse_radius_source",
        [
            "lake", "env", "lean",
            "tmp/BalabanCMP99ComplexInverseRadius.draft.lean", "-o",
            ".lake/build/lib/lean/YangMills/RG/"
            "BalabanCMP99ComplexInverseRadius.olean",
        ],
        None,
    ),
    (
        "complex_inverse_radius_audit",
        [
            "lake", "env", "lean",
            "tmp/BalabanCMP99ComplexInverseRadiusAudit.draft.lean", "-o",
            ".lake/build/lib/lean/tmp/"
            "BalabanCMP99ComplexInverseRadiusAudit.draft.olean",
        ],
        1,
    ),
    (
        "complex_ubar_small_field_source",
        [
            "lake", "env", "lean",
            "tmp/BalabanCMP99ComplexUbarSmallFieldPropagation.draft.lean", "-o",
            ".lake/build/lib/lean/YangMills/RG/"
            "BalabanCMP99ComplexUbarSmallFieldPropagation.olean",
        ],
        None,
    ),
    (
        "complex_ubar_small_field_audit",
        [
            "lake", "env", "lean",
            "tmp/BalabanCMP99ComplexUbarSmallFieldPropagationAudit.draft.lean",
            "-o", ".lake/build/lib/lean/tmp/"
            "BalabanCMP99ComplexUbarSmallFieldPropagationAudit.draft.olean",
        ],
        13,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
'''


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    require_commit(args.source_sha)
    content = render(args.source_sha, args.runner_rev)
    compile(content, str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "EQ337_COMPLEX_RECURSION_PREREQ_RUNNER_GENERATED "
        f"source_sha={args.source_sha} runner_rev={args.runner_rev} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
