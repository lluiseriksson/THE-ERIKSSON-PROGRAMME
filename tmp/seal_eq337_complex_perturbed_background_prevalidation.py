#!/usr/bin/env python3
"""Seal the tracked Eq. (3.37) complex perturbed-background prerequisite.

The Eq. (3.37) Ubar gate compiles and audits this tracked pair before the
seven scratch pairs.  This helper consumes that exact verifier JSON, removes
only the two PRE-VALIDATION notices, and imports the audit into
``YangMillsCore``.  It refuses source, evidence, worktree, or blob drift and
rolls every write back on failure.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
VERIFIER = ROOT / "tmp" / "verify_eq337_complex_ubar_radius_evidence.py"
CORE = "YangMillsCore.lean"
DOC_BLOCK = re.compile(r"/-![\s\S]*?-/")


def load_verifier():
    spec = importlib.util.spec_from_file_location("eq337_ubar_verifier", VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError("EQ337_BASE_VERIFIER_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def git_blob(source_sha: str, relative: str) -> bytes:
    child = run_git("cat-file", "blob", f"{source_sha}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"EQ337_BASE_SOURCE_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def boundary_paths(verifier) -> list[str]:
    module, _ = verifier.PREREQUISITE
    paths = [
        f"YangMills/RG/{module}.lean",
        f"YangMills/RG/{module}Audit.lean",
    ]
    if len(paths) != 2 or len(set(paths)) != 2:
        raise RuntimeError("EQ337_BASE_BOUNDARY_SCOPE_INVALID")
    return paths


def require_clean_exact(paths: list[str], source_sha: str) -> None:
    resolved = run_git("rev-parse", f"{source_sha}^{{commit}}")
    if resolved.returncode != 0 or resolved.stdout.decode().strip() != source_sha:
        raise RuntimeError("EQ337_BASE_SOURCE_COMMIT_MISMATCH")
    for relative in [*paths, CORE]:
        status = run_git("status", "--porcelain=v1", "--", relative)
        if status.returncode != 0 or status.stdout:
            raise RuntimeError(
                f"EQ337_BASE_WORKTREE_DIRTY={relative}:"
                + status.stdout.decode(errors="replace").strip()
            )
        child = run_git("diff", "--quiet", source_sha, "--", relative)
        if child.returncode != 0:
            raise RuntimeError(f"EQ337_BASE_BOUNDARY_DIVERGED={relative}")
        canonical = git_blob(source_sha, relative)
        worktree = (ROOT / relative).read_bytes().replace(b"\r\n", b"\n")
        if worktree != canonical:
            raise RuntimeError(f"EQ337_BASE_WORKTREE_BYTES_DIVERGED={relative}")


def require_evidence(path: Path, verifier, paths: list[str]) -> None:
    result = json.loads(path.read_text(encoding="utf-8"))
    if result.get("status") != "EQ337_COMPLEX_UBAR_RADIUS_EVIDENCE_OK":
        raise RuntimeError("EQ337_BASE_EVIDENCE_STATUS_MISMATCH")
    if result.get("source_sha") != verifier.SOURCE_SHA:
        raise RuntimeError("EQ337_BASE_EVIDENCE_SOURCE_MISMATCH")
    if result.get("runner_revision") != verifier.RUNNER_REV:
        raise RuntimeError("EQ337_BASE_EVIDENCE_RUNNER_MISMATCH")
    if result.get("expected_declarations") != 79:
        raise RuntimeError("EQ337_BASE_EVIDENCE_DECLARATION_COUNT_MISMATCH")
    measured = result.get("boundary_blob_sha256")
    wanted = {
        relative: hashlib.sha256(git_blob(verifier.SOURCE_SHA, relative)).hexdigest()
        for relative in paths
    }
    if not isinstance(measured, dict) or any(
        measured.get(relative) != digest for relative, digest in wanted.items()
    ):
        raise RuntimeError("EQ337_BASE_EVIDENCE_BOUNDARY_HASH_MISMATCH")


def remove_prevalidation_block(data: bytes, relative: str) -> bytes:
    text = data.decode("utf-8")
    blocks = [
        match for match in DOC_BLOCK.finditer(text)
        if "PRE-VALIDATION:" in match.group()
    ]
    if len(blocks) != 1:
        raise RuntimeError(
            f"EQ337_BASE_PREVALIDATION_BLOCK_COUNT={relative}:{len(blocks)}"
        )
    match = blocks[0]
    body = match.group()[3:-2]
    lines = body.splitlines(keepends=True)
    indices = [index for index, line in enumerate(lines) if "PRE-VALIDATION:" in line]
    if len(indices) != 1:
        raise RuntimeError(
            f"EQ337_BASE_PREVALIDATION_LINE_COUNT={relative}:{len(indices)}"
        )
    start = indices[0]
    end = start + 1
    while end < len(lines) and lines[end].strip():
        end += 1
    if end < len(lines) and not lines[end].strip():
        end += 1
    remainder = "".join(lines[:start] + lines[end:])
    replacement = "" if not remainder.strip() else "/-!" + remainder + "-/"
    sealed = text[: match.start()] + replacement + text[match.end() :]
    sealed = re.sub(r"\n{3,}(?=#print axioms)", "\n\n", sealed, count=1)
    if "PRE-VALIDATION:" in sealed:
        raise RuntimeError(f"EQ337_BASE_PREVALIDATION_REMAINS={relative}")
    return sealed.encode("utf-8")


def sealed_core(data: bytes, verifier) -> bytes:
    module, _ = verifier.PREREQUISITE
    audit_import = f"import YangMills.RG.{module}Audit"
    text = data.decode("utf-8")
    if audit_import in text:
        raise RuntimeError("EQ337_BASE_CORE_IMPORT_ALREADY_PRESENT")
    if not text.endswith("\n"):
        text += "\n"
    return (text + audit_import + "\n").encode("utf-8")


def digest(rows: list[tuple[str, bytes]]) -> str:
    payload = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {relative}\n".encode()
        for relative, data in rows
    )
    return hashlib.sha256(payload).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence-json", type=Path, required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    verifier = load_verifier()
    paths = boundary_paths(verifier)
    require_clean_exact(paths, verifier.SOURCE_SHA)
    require_evidence(args.evidence_json.resolve(), verifier, paths)
    rows = [
        (
            relative,
            remove_prevalidation_block(
                git_blob(verifier.SOURCE_SHA, relative), relative
            ),
        )
        for relative in paths
    ]
    rows.append((CORE, sealed_core(git_blob(verifier.SOURCE_SHA, CORE), verifier)))
    manifest_sha = digest(rows)
    if not args.apply:
        print(
            "EQ337_BASE_PREVALIDATION_SEAL_PREVIEW_OK "
            f"files={len(paths)} source_sha={verifier.SOURCE_SHA} "
            f"sealed_manifest_sha256={manifest_sha}"
        )
        return 0

    originals = {relative: (ROOT / relative).read_bytes() for relative, _ in rows}
    written: list[str] = []
    try:
        for relative, data in rows:
            (ROOT / relative).write_bytes(data)
            written.append(relative)
        if any(
            "PRE-VALIDATION:" in (ROOT / relative).read_text(encoding="utf-8-sig")
            for relative in paths
        ):
            raise RuntimeError("EQ337_BASE_POSTWRITE_PREVALIDATION_REMAINS")
        actual = digest(
            [(relative, (ROOT / relative).read_bytes()) for relative, _ in rows]
        )
        if actual != manifest_sha:
            raise RuntimeError(
                f"EQ337_BASE_POSTWRITE_MANIFEST_MISMATCH={actual} WANT={manifest_sha}"
            )
    except Exception:
        for relative in reversed(written):
            (ROOT / relative).write_bytes(originals[relative])
        raise

    print(
        "EQ337_BASE_PREVALIDATION_SEAL_APPLY_OK "
        f"files={len(paths)} source_sha={verifier.SOURCE_SHA} "
        f"sealed_manifest_sha256={manifest_sha}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
