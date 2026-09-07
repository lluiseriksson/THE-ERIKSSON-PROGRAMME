#!/usr/bin/env python3
"""Promote the source-carrier C6d Green drafts after the 11-pair cold seal.

Promotion is deliberately separate from compiler certification.  It copies
the exact guarded drafts under their intended module names, adds the audit to
``YangMillsCore`` and preserves one visible PRE-VALIDATION marker per module.
It refuses to run while any prerequisite in the ambient/compression boundary
still carries PRE-VALIDATION.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen",
    "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepth",
)
CORE = "YangMillsCore.lean"
BOUNDARY = "tmp/c6d-ambient-compression-cold-boundary.json"
FORBIDDEN = re.compile(
    rb"(?m)^\s*(?:sorry|admit|axiom)\b|\b(?:by\?|exact\?)\b"
)


def git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def git_blob(commit: str, relative: str) -> bytes:
    child = git("cat-file", "blob", f"{commit}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"C6D_SOURCE_GREEN_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def exact_head(value: str) -> None:
    if re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise RuntimeError("C6D_SOURCE_GREEN_BASE_SHA_INVALID")
    head = git("rev-parse", "HEAD")
    if head.returncode != 0 or head.stdout.decode().strip() != value:
        raise RuntimeError("C6D_SOURCE_GREEN_HEAD_MISMATCH")
    resolved = git("rev-parse", f"{value}^{{commit}}")
    if resolved.returncode != 0 or resolved.stdout.decode().strip() != value:
        raise RuntimeError("C6D_SOURCE_GREEN_BASE_COMMIT_MISMATCH")


def require_clean(relative: str) -> None:
    child = git("status", "--porcelain=v1", "--", relative)
    if child.returncode != 0 or child.stdout:
        raise RuntimeError(f"C6D_SOURCE_GREEN_DIRTY={relative}")


def require_prerequisite_seal(base_sha: str) -> None:
    manifest = json.loads(git_blob(base_sha, BOUNDARY))
    pairs = manifest.get("pairs")
    if not isinstance(pairs, list) or len(pairs) != 11:
        raise RuntimeError("C6D_SOURCE_GREEN_BOUNDARY_SCOPE_MISMATCH")
    for pair in pairs:
        if not isinstance(pair, dict):
            raise RuntimeError("C6D_SOURCE_GREEN_BOUNDARY_PAIR_INVALID")
        for key in ("source", "audit"):
            relative = pair.get(key)
            if not isinstance(relative, str):
                raise RuntimeError("C6D_SOURCE_GREEN_BOUNDARY_PATH_INVALID")
            if b"PRE-VALIDATION" in git_blob(base_sha, relative):
                raise RuntimeError(
                    f"C6D_SOURCE_GREEN_PREREQUISITE_NOT_SEALED={relative}"
                )


def guarded_draft(relative: str) -> bytes:
    path = ROOT / relative
    if not path.is_file():
        raise RuntimeError(f"C6D_SOURCE_GREEN_DRAFT_MISSING={relative}")
    data = path.read_bytes()
    text = data.decode("utf-8-sig")
    if text.count("PRE-VALIDATION:") != 1:
        raise RuntimeError(f"C6D_SOURCE_GREEN_PREVALIDATION_COUNT={relative}")
    if FORBIDDEN.search(data):
        raise RuntimeError(f"C6D_SOURCE_GREEN_FORBIDDEN_PLACEHOLDER={relative}")
    if re.search(r"(?m)^import\s+tmp\.", text):
        raise RuntimeError(f"C6D_SOURCE_GREEN_TMP_IMPORT={relative}")
    return data


def core_with_audit(data: bytes) -> bytes:
    text = data.decode("utf-8")
    for module in MODULES:
        line = f"import YangMills.RG.{module}Audit"
        if line in text:
            raise RuntimeError("C6D_SOURCE_GREEN_ROOT_IMPORT_ALREADY_PRESENT")
        if not text.endswith("\n"):
            text += "\n"
        text += line + "\n"
    return text.encode()


def digest(rows: list[tuple[str, bytes]]) -> str:
    payload = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {path}\n".encode()
        for path, data in rows
    )
    return hashlib.sha256(payload).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base-sha", required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    exact_head(args.base_sha)
    require_prerequisite_seal(args.base_sha)
    pairs: list[tuple[str, str, str, str]] = []
    for module in MODULES:
        source_draft = f"tmp/{module}.draft.lean"
        audit_draft = f"tmp/{module}Audit.draft.lean"
        source = f"YangMills/RG/{module}.lean"
        audit = f"YangMills/RG/{module}Audit.lean"
        for target in (source, audit):
            require_clean(target)
            if (ROOT / target).exists() or git(
                "cat-file", "-e", f"{args.base_sha}:{target}"
            ).returncode == 0:
                raise RuntimeError(f"C6D_SOURCE_GREEN_TARGET_EXISTS={target}")
        pairs.append((source_draft, audit_draft, source, audit))
    require_clean(CORE)

    rows: list[tuple[str, bytes]] = []
    for source_draft, audit_draft, source, audit in pairs:
        rows.extend((
            (source, guarded_draft(source_draft)),
            (audit, guarded_draft(audit_draft)),
        ))
    rows.append((CORE, core_with_audit(git_blob(args.base_sha, CORE))))
    manifest = digest(rows)
    mode = "APPLY" if args.apply else "PREVIEW"
    if not args.apply:
        print(
            f"C6D_SOURCE_GREEN_PROMOTION_{mode}_OK files={len(rows)} "
            f"base_sha={args.base_sha} manifest_sha256={manifest}"
        )
        return 0

    originals = {
        relative: (ROOT / relative).read_bytes()
        if (ROOT / relative).exists() else None
        for relative, _ in rows
    }
    written: list[str] = []
    try:
        for relative, data in rows:
            target = ROOT / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            written.append(relative)
        actual = digest([
            (relative, (ROOT / relative).read_bytes()) for relative, _ in rows
        ])
        if actual != manifest:
            raise RuntimeError(
                f"C6D_SOURCE_GREEN_POSTWRITE={actual} EXPECTED={manifest}"
            )
    except Exception:
        for relative in reversed(written):
            original = originals[relative]
            if original is None:
                (ROOT / relative).unlink(missing_ok=True)
            else:
                (ROOT / relative).write_bytes(original)
        raise

    print(
        f"C6D_SOURCE_GREEN_PROMOTION_{mode}_OK files={len(rows)} "
        f"base_sha={args.base_sha} manifest_sha256={manifest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
