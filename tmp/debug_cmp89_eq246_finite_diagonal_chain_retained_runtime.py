#!/usr/bin/env python3
"""Warm retained-runtime diagnostic for the finite Eq. (2.46) diagonal chain.

Diagnostic only.  Exact draft blobs from one immutable Git checkpoint are
copied into disposable module paths in the retained cold checkout.  HEAD is
never moved.  The queue is topological and stop-on-first-error.  No result of
this script is a seal; every promoted module still requires a fresh cold
focal/audit gate before PRE-VALIDATION can be removed.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import subprocess
import time


SOURCE_SHA = "791a6a58c34f051be9e2a2618200b51d66eadfe9"
ROOT = "YangMills/RG"
TARGETS = (
    (
        "BalabanCMP89Eq246FinePointSourceNoncentralCorrectionBound",
        "fba55143b1a700fa994c34912565b4d0874bc15b1014448d52298f357c4bb48f",
    ),
    (
        "BalabanCMP89Eq251HalfAliasTailIntegral",
        "26e715bb1dc2608f9948075ebdca17913695910cf94f9d33260d07fdda10095b",
    ),
    (
        "BalabanCMP89Eq251BareInverseLaplacianHalfWeight",
        "73029aeeee7e483f51bb62ad71d3af3f346be7acf0ae1126a428bdda40931964",
    ),
    (
        "BalabanCMP89Eq251CenteredHalfAliasSum",
        "27a5174436d888f7626e8c1c736474b986aed52e057c48d23f2b0fbdf020073b",
    ),
    (
        "BalabanCMP89Eq246FinePointSourceBareDiagonalBound",
        "da5ed62e3ca19b4a332f9f178c3eaca77cc0a6baabc1b43050e8aae9169682bc",
    ),
    (
        "BalabanCMP89Eq246FinePointSourceBareDiagonalSum",
        "551b34768439f97feea08997f57d01d9ee7e20a3f8d9a869c742ea09f90bf9c1",
    ),
    (
        "BalabanCMP89Eq246FinePointSourceNoncentralCorrectionSum",
        "da2ea2da260a94720c477019212d6989d017bde6cde23c3833ff0d715f38561c",
    ),
    (
        "BalabanCMP89Eq246FinePointSourceNoncentralSolutionSum",
        "e4e45738de97bcfeaff1f8a353bf38bedaef0a4ecf06bd42d9edd06c06d1bb4a",
    ),
    (
        "BalabanCMP89Eq246FinePointSourceCentralNumeratorIdentity",
        "3b54c58a2368e52e8457fdda97de13051ae898fc562307fe2163b8db3bbbdf0d",
    ),
    (
        "BalabanCMP89Eq246FinePointSourceCentralComponentBound",
        "0aca04426ed8a7c140988c6738e7d14f1a38e4cf537326d34879a3c6ac33790a",
    ),
    (
        "BalabanCMP89Eq246FinePointSourceFullSolutionSum",
        "eeaa988a90c2e59a118e3104af50454a3241fa98e391345eda61afdb4d9bd5e7",
    ),
)


def run(repo: Path, *cmd: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        list(cmd), cwd=repo, check=False, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )


def git(repo: Path, *args: str) -> bytes:
    child = run(repo, "git", "-c", "safe.directory=*", *args)
    output = child.stdout.decode(errors="replace")
    if child.returncode != 0:
        raise RuntimeError(
            "FINITE_DIAGONAL_DEBUG_GIT_FAIL=" + " ".join(args) + ":" + output
        )
    print(f"FINITE_DIAGONAL_DEBUG_GIT_STAGE={args[0]} EXIT=0", flush=True)
    return child.stdout


def checked(repo: Path, label: str, *cmd: str) -> bytes:
    child = run(repo, *cmd)
    output = child.stdout.decode(errors="replace")
    print(output, end="", flush=True)
    print(
        f"FINITE_DIAGONAL_DEBUG_STAGE={label} EXIT={child.returncode}",
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError(f"FINITE_DIAGONAL_DEBUG_STAGE_FAIL={label}")
    return child.stdout


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--source-sha", default=SOURCE_SHA)
    args = parser.parse_args()
    repo = args.repo.resolve()

    if args.source_sha != SOURCE_SHA:
        raise RuntimeError("FINITE_DIAGONAL_DEBUG_UNEXPECTED_SOURCE_SHA")
    original_head = git(repo, "rev-parse", "HEAD").decode().strip()
    git(repo, "fetch", "--no-tags", "origin", args.source_sha)
    resolved = git(repo, "rev-parse", f"{args.source_sha}^{{commit}}").decode().strip()
    if resolved != args.source_sha:
        raise RuntimeError("FINITE_DIAGONAL_DEBUG_SOURCE_SHA_MISMATCH")

    written: list[str] = []
    for stem, expected_sha256 in TARGETS:
        draft = f"tmp/{stem}.draft.lean"
        target_rel = f"{ROOT}/{stem}.lean"
        data = git(repo, "cat-file", "blob", f"{args.source_sha}:{draft}")
        actual_sha256 = hashlib.sha256(data).hexdigest()
        if actual_sha256 != expected_sha256:
            raise RuntimeError(
                f"FINITE_DIAGONAL_DEBUG_BLOB_MISMATCH={draft}:"
                f"{actual_sha256}:WANT={expected_sha256}"
            )
        target = repo / target_rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        written.append(target_rel)
        print(
            f"FINITE_DIAGONAL_DEBUG_BLOB={draft} TARGET={target_rel} "
            f"SHA256={actual_sha256}",
            flush=True,
        )

    manifest = repo / "tmp" / "eq246-finite-diagonal-hot-paths.txt"
    manifest.write_text("\n".join(written) + "\n", encoding="utf-8", newline="\n")
    checked(
        repo,
        "overlay_text_guard",
        "python3",
        "scripts/check_lean_overlay_text.py",
        "--paths-from",
        str(manifest),
    )
    checked(
        repo,
        "import_prefix_guard",
        "python3",
        "scripts/check_lean_import_prefix.py",
        *written,
    )

    for ordinal, (stem, _) in enumerate(TARGETS, start=1):
        module = f"YangMills.RG.{stem}"
        started = time.perf_counter()
        checked(repo, f"target_{ordinal:02d}_{stem}", "lake", "build", module)
        print(
            f"FINITE_DIAGONAL_DEBUG_SECONDS={ordinal:02d}:{stem}:"
            f"{time.perf_counter() - started:.3f}",
            flush=True,
        )

    if git(repo, "rev-parse", "HEAD").decode().strip() != original_head:
        raise RuntimeError("FINITE_DIAGONAL_DEBUG_HEAD_MOVED")
    print(f"FINITE_DIAGONAL_DEBUG_ORIGINAL_HEAD={original_head}", flush=True)
    print(f"FINITE_DIAGONAL_DEBUG_SOURCE_SHA={args.source_sha}", flush=True)
    print(f"FINITE_DIAGONAL_DEBUG_TARGETS={len(TARGETS)}", flush=True)
    print("FINITE_DIAGONAL_DEBUG_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print("FINITE_DIAGONAL_DEBUG_ERROR=" + repr(exc), flush=True)
        print("FINITE_DIAGONAL_DEBUG_FINAL_STATUS=FAIL", flush=True)
        raise
