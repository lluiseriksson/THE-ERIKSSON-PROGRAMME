#!/usr/bin/env python3
"""Fail-closed promotion of the C6d ambient/compression scratch boundary.

This helper may run only after the retained-runtime three-queue evidence has
passed the external verifier.  It promotes the three scratch source/audit
pairs under their intended module names, preserves an explicit
PRE-VALIDATION notice, and adds only their audits to ``YangMillsCore``.
Promotion is not cold certification and never changes the terminal counters.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
HOT_SOURCE_SHA = "1176948c6a511d017780a54f1cbc8a72b6dea972"
VERIFIER = ROOT / "tmp" / "verify_c6d_post_cold_hot_evidence.py"
CORE = "YangMillsCore.lean"
PAIRS = (
    "BalabanCMP99ActiveGaugeRegionReindex",
    "BalabanCMP99Eq360C6dSourceAmbientBaselinePrecision",
    "BalabanCMP99ActiveGaugeRegionReindexGreen",
)
NOTICE = (
    "PRE-VALIDATION: source present; `.olean` not yet materialized in a fresh "
    "cold checkout, and the result is not compiler-verified for sealing."
)


def git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", *args], cwd=ROOT, check=False,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )


def exact_commit(value: str, label: str) -> None:
    if re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise RuntimeError(f"{label}_SHA_INVALID")
    child = git("rev-parse", f"{value}^{{commit}}")
    if child.returncode != 0 or child.stdout.decode().strip() != value:
        raise RuntimeError(f"{label}_COMMIT_MISMATCH")


def git_blob(commit: str, relative: str) -> bytes:
    child = git("cat-file", "blob", f"{commit}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"C6D_AMBIENT_PROMOTION_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def require_clean(relative: str) -> None:
    child = git("status", "--porcelain=v1", "--", relative)
    if child.returncode != 0 or child.stdout:
        raise RuntimeError(f"C6D_AMBIENT_PROMOTION_DIRTY={relative}")


def require_absent(base_sha: str, relative: str) -> None:
    require_clean(relative)
    tracked = git("cat-file", "-e", f"{base_sha}:{relative}")
    if tracked.returncode == 0 or (ROOT / relative).exists():
        raise RuntimeError(f"C6D_AMBIENT_PROMOTION_DESTINATION_EXISTS={relative}")


def verify_hot_evidence(archive: Path) -> None:
    if not archive.is_file():
        raise RuntimeError("C6D_AMBIENT_PROMOTION_EVIDENCE_MISSING")
    child = subprocess.run(
        [sys.executable, str(VERIFIER), str(archive)], cwd=ROOT, check=False,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    )
    print(child.stdout, end="")
    if child.returncode != 0 or "C6D_POST_COLD_HOT_EVIDENCE_OK" not in child.stdout:
        raise RuntimeError("C6D_AMBIENT_PROMOTION_EVIDENCE_REJECTED")


def draft_path(module: str, audit: bool) -> str:
    suffix = "Audit" if audit else ""
    return f"tmp/{module}{suffix}.draft.lean"


def destination(module: str, audit: bool) -> str:
    suffix = "Audit" if audit else ""
    return f"YangMills/RG/{module}{suffix}.lean"


def promote_blob(data: bytes) -> bytes:
    text = data.decode("utf-8")
    if "SCRATCH / NOT SHIPPED." not in text:
        raise RuntimeError("C6D_AMBIENT_PROMOTION_SCRATCH_MARKER_MISSING")
    text = text.replace("SCRATCH / NOT SHIPPED.", NOTICE, 1)
    if text.count("PRE-VALIDATION:") != 1:
        raise RuntimeError("C6D_AMBIENT_PROMOTION_PREVALIDATION_COUNT")
    if "import tmp." in text:
        raise RuntimeError("C6D_AMBIENT_PROMOTION_TMP_IMPORT_REMAINS")
    if re.search(r"(?m)^\s*axiom\b|\b(?:sorry|admit|by\?|exact\?)\b", text):
        raise RuntimeError("C6D_AMBIENT_PROMOTION_FORBIDDEN_PLACEHOLDER")
    return text.encode("utf-8")


def core_with_audits(data: bytes) -> bytes:
    text = data.decode("utf-8")
    for module in PAIRS:
        line = f"import YangMills.RG.{module}Audit"
        if line not in text:
            if not text.endswith("\n"):
                text += "\n"
            text += line + "\n"
    return text.encode("utf-8")


def digest(rows: list[tuple[str, bytes]]) -> str:
    payload = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {path}\n".encode()
        for path, data in rows
    )
    return hashlib.sha256(payload).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base-sha", required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    exact_commit(args.base_sha, "C6D_AMBIENT_PROMOTION_BASE")
    exact_commit(HOT_SOURCE_SHA, "C6D_AMBIENT_PROMOTION_HOT_SOURCE")
    head = git("rev-parse", "HEAD")
    if head.returncode != 0 or head.stdout.decode().strip() != args.base_sha:
        raise RuntimeError("C6D_AMBIENT_PROMOTION_HEAD_MISMATCH")
    ancestor = git("merge-base", "--is-ancestor", HOT_SOURCE_SHA, args.base_sha)
    if ancestor.returncode != 0:
        raise RuntimeError("C6D_AMBIENT_PROMOTION_HOT_SOURCE_NOT_ANCESTOR")
    verify_hot_evidence(args.evidence.resolve())

    rows: list[tuple[str, bytes]] = []
    for module in PAIRS:
        for audit in (False, True):
            target = destination(module, audit)
            require_absent(args.base_sha, target)
            rows.append((target, promote_blob(git_blob(
                HOT_SOURCE_SHA, draft_path(module, audit)
            ))))

    require_clean(CORE)
    rows.append((CORE, core_with_audits(git_blob(args.base_sha, CORE))))
    manifest = digest(rows)
    mode = "APPLY" if args.apply else "PREVIEW"
    if not args.apply:
        print(
            f"C6D_AMBIENT_PROMOTION_{mode}_OK files={len(rows)} "
            f"base_sha={args.base_sha} hot_source_sha={HOT_SOURCE_SHA} "
            f"manifest_sha256={manifest}"
        )
        return 0

    originals = {
        path: (ROOT / path).read_bytes() if (ROOT / path).exists() else None
        for path, _ in rows
    }
    written: list[str] = []
    try:
        for path, data in rows:
            target = ROOT / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            written.append(path)
        actual = digest([(path, (ROOT / path).read_bytes()) for path, _ in rows])
        if actual != manifest:
            raise RuntimeError(
                f"C6D_AMBIENT_PROMOTION_POSTWRITE={actual} WANT={manifest}"
            )
    except Exception:
        for path in reversed(written):
            original = originals[path]
            if original is None:
                (ROOT / path).unlink(missing_ok=True)
            else:
                (ROOT / path).write_bytes(original)
        raise

    print(
        f"C6D_AMBIENT_PROMOTION_{mode}_OK files={len(rows)} "
        f"base_sha={args.base_sha} hot_source_sha={HOT_SOURCE_SHA} "
        f"manifest_sha256={manifest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
