#!/usr/bin/env python3
"""Hot retained-runtime diagnostic for the next two physical Eq. (2.46) bricks.

Diagnostic only.  Exact Git blobs from one PRE-VALIDATION source checkpoint
are overlaid on the retained cold checkout without moving HEAD.  A later fresh
cold focal/audit gate remains mandatory before any PRE-VALIDATION notice may be
removed.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess
import time


TARGETS = (
    (
        "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolution.lean",
        "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolutionAudit.lean",
        "YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolution",
        4,
    ),
    (
        "YangMills/RG/BalabanCMP99FlatPhysicalFibrePointSourceDFT.lean",
        "YangMills/RG/BalabanCMP99FlatPhysicalFibrePointSourceDFTAudit.lean",
        "YangMills.RG.BalabanCMP99FlatPhysicalFibrePointSourceDFT",
        1,
    ),
)
PATHS = tuple(path for main, audit, _, _ in TARGETS for path in (main, audit))
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
    output = child.stdout.decode(errors="replace")
    print(output, end="", flush=True)
    print(f"PHYSICAL_EQ246_DEBUG_STAGE={label} EXIT={child.returncode}", flush=True)
    if child.returncode != 0:
        raise RuntimeError(f"PHYSICAL_EQ246_DEBUG_STAGE_FAIL={label}")
    return child.stdout


def git(repo: Path, *args: str) -> bytes:
    child = run(repo, "git", "-c", "safe.directory=*", *args)
    if child.returncode != 0:
        raise RuntimeError(
            "PHYSICAL_EQ246_DEBUG_GIT_FAIL=" + " ".join(args) + ":" +
            child.stdout.decode(errors="replace")
        )
    print(f"PHYSICAL_EQ246_DEBUG_GIT_STAGE={args[0]} EXIT=0", flush=True)
    return child.stdout


def axiom_gate(output: str, expected: int, label: str) -> None:
    compact = re.sub(r"\s+", " ", output)
    for forbidden in FORBIDDEN:
        if forbidden in compact:
            raise RuntimeError(
                f"PHYSICAL_EQ246_DEBUG_FORBIDDEN_AXIOM={label}:{forbidden}"
            )
    blocks = list(OUTPUT_RE.finditer(output))
    pure = list(NO_AXIOM_RE.finditer(output))
    actual = len(blocks) + len(pure)
    if actual != expected:
        raise RuntimeError(
            f"PHYSICAL_EQ246_DEBUG_AXIOM_COUNT={label}:{actual}:WANT={expected}"
        )
    for block in blocks:
        names = {
            name.strip() for name in block.group(2).split(",") if name.strip()
        }
        unexpected = names - ALLOWED
        if unexpected:
            raise RuntimeError(
                f"PHYSICAL_EQ246_DEBUG_AXIOM_UNEXPECTED={label}:" +
                ",".join(sorted(unexpected))
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
        raise RuntimeError("PHYSICAL_EQ246_DEBUG_SOURCE_SHA_MISMATCH")

    for relative in PATHS:
        data = git(repo, "cat-file", "blob", f"{args.source_sha}:{relative}")
        expected = git(repo, "rev-parse", f"{args.source_sha}:{relative}").decode().strip()
        actual = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        if actual != expected:
            raise RuntimeError("PHYSICAL_EQ246_DEBUG_BLOB_MISMATCH=" + relative)
        target = repo / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        print(f"PHYSICAL_EQ246_DEBUG_BLOB={relative} GIT_SHA1={actual}", flush=True)

    manifest = repo / "tmp" / "physical-eq246-hot-paths.txt"
    manifest.write_text("\n".join(PATHS) + "\n", encoding="utf-8", newline="\n")
    checked(
        repo, "overlay_text_guard", "python3", "scripts/check_lean_overlay_text.py",
        "--paths-from", str(manifest),
    )
    checked(
        repo, "import_prefix_guard", "python3", "scripts/check_lean_import_prefix.py",
        *PATHS,
    )

    for main, audit, module, expected_axioms in TARGETS:
        label = module.rsplit(".", 1)[-1]
        started = time.perf_counter()
        checked(repo, f"{label}_focal", "lake", "build", module)
        print(
            f"PHYSICAL_EQ246_DEBUG_FOCAL_SECONDS={label}:"
            f"{time.perf_counter() - started:.3f}", flush=True,
        )

        started = time.perf_counter()
        audit_output = checked(repo, f"{label}_audit", "lake", "env", "lean", audit)
        axiom_gate(audit_output.decode(errors="replace"), expected_axioms, label)
        print(
            f"PHYSICAL_EQ246_DEBUG_AUDIT_SECONDS={label}:"
            f"{time.perf_counter() - started:.3f}", flush=True,
        )

    if git(repo, "rev-parse", "HEAD").decode().strip() != original_head:
        raise RuntimeError("PHYSICAL_EQ246_DEBUG_HEAD_MOVED")
    print(f"PHYSICAL_EQ246_DEBUG_ORIGINAL_HEAD={original_head}", flush=True)
    print(f"PHYSICAL_EQ246_DEBUG_SOURCE_SHA={args.source_sha}", flush=True)
    print("PHYSICAL_EQ246_DEBUG_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print("PHYSICAL_EQ246_DEBUG_ERROR=" + repr(exc), flush=True)
        print("PHYSICAL_EQ246_DEBUG_FINAL_STATUS=FAIL", flush=True)
        raise
