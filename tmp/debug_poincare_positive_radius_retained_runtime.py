#!/usr/bin/env python3
"""Warm retained-runtime debug for positive-radius Poincare reachability.

Diagnostic only. Exact Git blobs from one source SHA are overlaid on a retained
checkout without moving HEAD. A later cold source/audit/root gate is mandatory
before PRE-VALIDATION can be removed.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess
import time


STAGES = (
    ("YangMills/RG/BalabanCMP99SourcePoincarePositiveRadiusReachability.lean", None),
    ("YangMills/RG/BalabanCMP99SourcePoincarePositiveRadiusReachabilityAudit.lean", 8),
)
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


def git(repo: Path, *args: str) -> bytes:
    child = run(repo, "git", "-c", "safe.directory=*", *args)
    if child.returncode != 0:
        raise RuntimeError(
            "POINCARE_RADIUS_DEBUG_GIT_FAIL=" + " ".join(args) + ":"
            + child.stdout.decode(errors="replace")
        )
    return child.stdout


def compile_one(repo: Path, relative: str) -> tuple[int, float, str]:
    output = (
        repo / ".lake" / "build" / "lib" / "lean" /
        Path(relative).with_suffix(".olean")
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    child = run(
        repo, "lake", "env", "lean", relative, "-o",
        str(output.relative_to(repo)),
    )
    return (
        child.returncode,
        time.perf_counter() - started,
        child.stdout.decode(errors="replace"),
    )


def axiom_gate(text: str, expected: int, stage: str) -> None:
    compact = re.sub(r"\s+", " ", text)
    for forbidden in FORBIDDEN:
        if forbidden in compact:
            raise RuntimeError(f"POINCARE_RADIUS_DEBUG_FORBIDDEN={stage}:{forbidden}")
    blocks = list(OUTPUT_RE.finditer(text))
    pure = list(NO_AXIOM_RE.finditer(text))
    actual = len(blocks) + len(pure)
    if actual != expected:
        raise RuntimeError(
            f"POINCARE_RADIUS_DEBUG_AXIOM_COUNT={stage}:{actual} WANT={expected}"
        )
    for block in blocks:
        names = {
            name.strip() for name in block.group(2).split(",") if name.strip()
        }
        unexpected = names - ALLOWED
        if unexpected:
            raise RuntimeError(
                f"POINCARE_RADIUS_DEBUG_AXIOM_UNEXPECTED={stage}:"
                + ",".join(sorted(unexpected))
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
        raise RuntimeError("POINCARE_RADIUS_DEBUG_SOURCE_SHA_MISMATCH")

    for relative, _ in STAGES:
        data = git(repo, "cat-file", "blob", f"{args.source_sha}:{relative}")
        expected = git(repo, "rev-parse", f"{args.source_sha}:{relative}").decode().strip()
        actual = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        if actual != expected:
            raise RuntimeError(f"POINCARE_RADIUS_DEBUG_BLOB_MISMATCH={relative}")
        target = repo / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        print(f"DEBUG_BLOB={relative} GIT_SHA1={actual}", flush=True)

    for index, (relative, expected_axioms) in enumerate(STAGES, start=1):
        code, seconds, output = compile_one(repo, relative)
        print(output, end="", flush=True)
        print(
            f"DEBUG_STAGE={index}_{Path(relative).stem} "
            f"EXIT={code} SECONDS={seconds:.3f}", flush=True,
        )
        if code != 0:
            print("DEBUG_FINAL_STATUS=FAIL", flush=True)
            return code
        if expected_axioms is not None:
            axiom_gate(output, expected_axioms, relative)

    if git(repo, "rev-parse", "HEAD").decode().strip() != original_head:
        raise RuntimeError("POINCARE_RADIUS_DEBUG_HEAD_MOVED")
    print(f"DEBUG_ORIGINAL_HEAD={original_head}", flush=True)
    print(f"DEBUG_SOURCE_SHA={args.source_sha}", flush=True)
    print("DEBUG_AXIOM_HEADERS=8", flush=True)
    print("DEBUG_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
