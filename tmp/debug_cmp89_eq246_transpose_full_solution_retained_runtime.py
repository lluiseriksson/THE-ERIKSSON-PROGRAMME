#!/usr/bin/env python3
"""Hot retained-runtime diagnostic for the arbitrary-source transposed Eq. (2.46) solution.

Diagnostic only. Exact Git blobs from one promoted PRE-VALIDATION source SHA
are overlaid on the already cold-validated Eq. (2.46) checkout. The checkout
HEAD is never moved. A later independent cold focal/audit gate remains
mandatory before either PRE-VALIDATION notice can be removed.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess
import time


MAIN = "YangMills/RG/BalabanCMP89Eq246StabilizedAliasTransposeFullSolution.lean"
AUDIT = "YangMills/RG/BalabanCMP89Eq246StabilizedAliasTransposeFullSolutionAudit.lean"
PATHS = (MAIN, AUDIT)
MODULE = "YangMills.RG.BalabanCMP89Eq246StabilizedAliasTransposeFullSolution"
EXPECTED_AXIOMS = 6
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
OUTPUT_RE = re.compile(
    r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]", re.MULTILINE
)
NO_AXIOM_RE = re.compile(
    r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms", re.MULTILINE
)


def run(repo: Path, *cmd: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        list(cmd), cwd=repo, check=False, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )


def checked(repo: Path, label: str, *cmd: str) -> bytes:
    child = run(repo, *cmd)
    text = child.stdout.decode(errors="replace")
    print(text, end="", flush=True)
    print(f"TRANSPOSE_DEBUG_STAGE={label} EXIT={child.returncode}", flush=True)
    if child.returncode != 0:
        raise RuntimeError(f"TRANSPOSE_DEBUG_STAGE_FAIL={label}")
    return child.stdout


def git(repo: Path, *args: str) -> bytes:
    child = run(repo, "git", "-c", "safe.directory=*", *args)
    if child.returncode != 0:
        raise RuntimeError(
            "TRANSPOSE_DEBUG_GIT_FAIL=" + " ".join(args) + ":" +
            child.stdout.decode(errors="replace")
        )
    print(f"TRANSPOSE_DEBUG_GIT_STAGE={args[0]} EXIT=0", flush=True)
    return child.stdout


def axiom_gate(text: str) -> None:
    compact = re.sub(r"\s+", " ", text)
    for forbidden in FORBIDDEN:
        if forbidden in compact:
            raise RuntimeError("TRANSPOSE_DEBUG_FORBIDDEN_AXIOM=" + forbidden)
    blocks = list(OUTPUT_RE.finditer(text))
    pure = list(NO_AXIOM_RE.finditer(text))
    actual = len(blocks) + len(pure)
    if actual != EXPECTED_AXIOMS:
        raise RuntimeError(
            f"TRANSPOSE_DEBUG_AXIOM_COUNT={actual} WANT={EXPECTED_AXIOMS}"
        )
    for block in blocks:
        names = {
            name.strip() for name in block.group(2).split(",") if name.strip()
        }
        unexpected = names - ALLOWED
        if unexpected:
            raise RuntimeError(
                "TRANSPOSE_DEBUG_AXIOM_UNEXPECTED=" + ",".join(sorted(unexpected))
            )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--source-sha", required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()

    original_head = git(repo, "rev-parse", "HEAD").decode().strip()
    git(repo, "fetch", "--no-tags", "origin", args.source_sha)
    resolved = git(repo, "rev-parse", f"{args.source_sha}^{{commit}}").decode().strip()
    if resolved != args.source_sha:
        raise RuntimeError("TRANSPOSE_DEBUG_SOURCE_SHA_MISMATCH")

    for relative in PATHS:
        data = git(repo, "cat-file", "blob", f"{args.source_sha}:{relative}")
        expected = git(repo, "rev-parse", f"{args.source_sha}:{relative}").decode().strip()
        actual = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        if actual != expected:
            raise RuntimeError("TRANSPOSE_DEBUG_BLOB_MISMATCH=" + relative)
        target = repo / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        print(f"TRANSPOSE_DEBUG_BLOB={relative} GIT_SHA1={actual}", flush=True)

    manifest = repo / "tmp" / "eq246-transpose-hot-paths.txt"
    manifest.write_text("\n".join(PATHS) + "\n", encoding="utf-8", newline="\n")
    checked(
        repo, "overlay_text_guard", "python3", "scripts/check_lean_overlay_text.py",
        "--paths-from", str(manifest),
    )
    checked(
        repo, "import_prefix_guard", "python3", "scripts/check_lean_import_prefix.py",
        *PATHS,
    )

    started = time.perf_counter()
    checked(repo, "focal", "lake", "build", MODULE)
    print(f"TRANSPOSE_DEBUG_FOCAL_SECONDS={time.perf_counter() - started:.3f}", flush=True)

    started = time.perf_counter()
    audit_output = checked(repo, "audit", "lake", "env", "lean", AUDIT)
    axiom_gate(audit_output.decode(errors="replace"))
    print(f"TRANSPOSE_DEBUG_AUDIT_SECONDS={time.perf_counter() - started:.3f}", flush=True)

    if git(repo, "rev-parse", "HEAD").decode().strip() != original_head:
        raise RuntimeError("TRANSPOSE_DEBUG_HEAD_MOVED")
    print(f"TRANSPOSE_DEBUG_ORIGINAL_HEAD={original_head}", flush=True)
    print(f"TRANSPOSE_DEBUG_SOURCE_SHA={args.source_sha}", flush=True)
    print(f"TRANSPOSE_DEBUG_AXIOM_HEADERS={EXPECTED_AXIOMS}", flush=True)
    print("TRANSPOSE_DEBUG_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print("TRANSPOSE_DEBUG_ERROR=" + repr(exc), flush=True)
        print("TRANSPOSE_DEBUG_FINAL_STATUS=FAIL", flush=True)
        raise
