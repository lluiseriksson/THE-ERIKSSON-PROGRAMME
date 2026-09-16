#!/usr/bin/env python3
"""Atomically promote exact C6d D2 plus owner-distance rescaling.

The selected source commit must already contain every sealed prerequisite.
The operation writes six PRE-VALIDATION modules and one exact root update; it
does not compile, seal, commit or publish anything.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
CORE = "YangMillsCore.lean"
DECAY_PROMOTER = ROOT / "tmp" / "promote_c6d_exact_green_decay.py"
OWNER_PROMOTER = ROOT / "tmp" / "promote_c6d_owner_decay_rescaling.py"


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"C6D_D2_OWNER_PROMOTION_IMPORT_FAILED={path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def blob(source_sha: str, relative: str) -> bytes:
    child = git("cat-file", "blob", f"{source_sha}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"C6D_D2_OWNER_PROMOTION_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def require_clean_source_blob(source_sha: str, relative: str) -> bytes:
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(f"C6D_D2_OWNER_PROMOTION_DIRTY={relative}")
    data = blob(source_sha, relative)
    if (ROOT / relative).read_bytes().replace(b"\r\n", b"\n") != data:
        raise RuntimeError(f"C6D_D2_OWNER_PROMOTION_DIVERGED={relative}")
    return data


def manifest_digest(rows: list[tuple[str, bytes]]) -> str:
    payload = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {relative}\n".encode()
        for relative, data in rows
    )
    return hashlib.sha256(payload).hexdigest().upper()


def collect_rows(source_sha: str, *, check_worktree: bool = True) -> list[tuple[str, bytes]]:
    decay = load("c6d_d2_owner_decay_promoter", DECAY_PROMOTER)
    owner = load("c6d_d2_owner_rescaling_promoter", OWNER_PROMOTER)
    promoters = (decay, owner)
    prerequisites = tuple(dict.fromkeys(
        relative for promoter in promoters for relative in promoter.PREREQUISITES
    ))
    for relative in prerequisites:
        if b"PRE-VALIDATION:" in blob(source_sha, relative):
            raise RuntimeError(f"C6D_D2_OWNER_PROMOTION_PREREQ_UNSEALED={relative}")

    rows: list[tuple[str, bytes]] = []
    imports: list[str] = []
    seen_targets: set[str] = set()
    for promoter in promoters:
        for relative in promoter.SOURCES:
            target = promoter.destination(relative)
            if target in seen_targets:
                raise RuntimeError(f"C6D_D2_OWNER_PROMOTION_DUPLICATE_TARGET={target}")
            seen_targets.add(target)
            if git("cat-file", "-e", f"{source_sha}:{target}").returncode == 0:
                raise RuntimeError(f"C6D_D2_OWNER_PROMOTION_TARGET_EXISTS={target}")
            if check_worktree and (
                (ROOT / target).exists()
                or git("status", "--porcelain=v1", "--", target).stdout
            ):
                raise RuntimeError(f"C6D_D2_OWNER_PROMOTION_TARGET_DIRTY={target}")
            data = (
                require_clean_source_blob(source_sha, relative)
                if check_worktree else blob(source_sha, relative)
            )
            rows.append((target, promoter.promote_text(data)))
            if target.endswith("Audit.lean"):
                imports.append("import YangMills.RG." + Path(target).stem)

    if check_worktree:
        core_status = git("status", "--porcelain=v1", "--", CORE)
        if core_status.returncode != 0 or core_status.stdout:
            raise RuntimeError("C6D_D2_OWNER_PROMOTION_CORE_DIRTY")
    core = blob(source_sha, CORE).decode("utf-8")
    for audit_import in imports:
        if audit_import in core:
            raise RuntimeError(f"C6D_D2_OWNER_PROMOTION_CORE_IMPORT_EXISTS={audit_import}")
    if not core.endswith("\n"):
        core += "\n"
    rows.append((CORE, (core + "\n".join(imports) + "\n").encode("utf-8")))
    if len(rows) != 7 or len(imports) != 3:
        raise RuntimeError(
            f"C6D_D2_OWNER_PROMOTION_SCOPE=rows:{len(rows)}/imports:{len(imports)}"
        )
    return rows


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    if re.fullmatch(r"[0-9a-f]{40}", args.source_sha) is None:
        raise RuntimeError("C6D_D2_OWNER_PROMOTION_SOURCE_SHA_INVALID")
    resolved = git("rev-parse", f"{args.source_sha}^{{commit}}")
    if resolved.returncode != 0 or resolved.stdout.decode().strip() != args.source_sha:
        raise RuntimeError("C6D_D2_OWNER_PROMOTION_SOURCE_COMMIT_MISMATCH")

    rows = collect_rows(args.source_sha)
    digest = manifest_digest(rows)
    if not args.apply:
        print(
            "C6D_D2_OWNER_PROMOTION_PREVIEW_OK "
            f"source_sha={args.source_sha} files=7 promoted=6 imports=3 "
            f"manifest_sha256={digest}"
        )
        return 0

    originals = {
        relative: (ROOT / relative).read_bytes() if (ROOT / relative).exists() else None
        for relative, _ in rows
    }
    written: list[str] = []
    try:
        for relative, data in rows:
            target = ROOT / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            written.append(relative)
        actual = manifest_digest(
            [(relative, (ROOT / relative).read_bytes()) for relative, _ in rows]
        )
        if actual != digest:
            raise RuntimeError(f"C6D_D2_OWNER_PROMOTION_POSTWRITE={actual} EXPECTED={digest}")
    except Exception:
        for relative in reversed(written):
            original = originals[relative]
            if original is None:
                (ROOT / relative).unlink(missing_ok=True)
            else:
                (ROOT / relative).write_bytes(original)
        raise
    print(
        "C6D_D2_OWNER_PROMOTION_APPLIED "
        f"source_sha={args.source_sha} files=7 promoted=6 imports=3 "
        f"manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
