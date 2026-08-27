#!/usr/bin/env python3
"""Mechanically seal the eight-file C6d Step3 boundary after verified evidence."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
VERIFIER = ROOT / "tmp" / "verify_c6d_step3_localized_precision_evidence.py"
CORE = "YangMillsCore.lean"
DOC_BLOCK = re.compile(r"/-![\s\S]*?-/")


def load_verifier():
    spec = importlib.util.spec_from_file_location("c6d_step3_evidence_verifier", VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_STEP3_VERIFIER_IMPORT_FAILED")
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
    child = run_git("show", f"{source_sha}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"C6D_STEP3_SOURCE_BLOB_READ_FAILED={relative}/"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def boundary_paths(verifier) -> list[str]:
    paths: list[str] = []
    for module, _count in verifier.BRICKS:
        paths.extend(
            (f"YangMills/RG/{module}.lean", f"YangMills/RG/{module}Audit.lean")
        )
    if len(paths) != 8 or len(set(paths)) != 8:
        raise RuntimeError(f"C6D_STEP3_BOUNDARY_SCOPE={len(paths)}/{len(set(paths))}")
    return paths


def require_evidence(path: Path, source_sha: str, paths: list[str], verifier) -> None:
    result = json.loads(path.read_text(encoding="utf-8"))
    if result.get("status") != "C6D_STEP3_LOCALIZED_PRECISION_EVIDENCE_OK":
        raise RuntimeError("C6D_STEP3_EVIDENCE_STATUS_MISMATCH")
    if result.get("source_sha") != source_sha:
        raise RuntimeError("C6D_STEP3_EVIDENCE_SOURCE_MISMATCH")
    if result.get("runner_revision") != verifier.RUNNER_REV:
        raise RuntimeError("C6D_STEP3_EVIDENCE_RUNNER_MISMATCH")
    if result.get("expected_declarations") != 15:
        raise RuntimeError("C6D_STEP3_EVIDENCE_DECLARATION_COUNT_MISMATCH")
    measured = result.get("boundary_blob_sha256")
    wanted = {relative: hashlib.sha256(git_blob(source_sha, relative)).hexdigest() for relative in paths}
    if measured != wanted:
        raise RuntimeError("C6D_STEP3_EVIDENCE_BOUNDARY_HASH_MISMATCH")


def require_clean_exact(paths: list[str], source_sha: str) -> None:
    resolved = run_git("rev-parse", f"{source_sha}^{{commit}}")
    if resolved.returncode != 0 or resolved.stdout.decode().strip() != source_sha:
        raise RuntimeError("C6D_STEP3_SOURCE_COMMIT_MISMATCH")
    for relative in [*paths, CORE]:
        status = run_git("status", "--porcelain=v1", "--", relative)
        if status.returncode != 0 or status.stdout:
            raise RuntimeError(
                f"C6D_STEP3_WORKTREE_DIRTY={relative}/"
                + status.stdout.decode(errors="replace").strip()
            )
        child = run_git("diff", "--quiet", source_sha, "--", relative)
        if child.returncode != 0:
            raise RuntimeError(f"C6D_STEP3_BOUNDARY_DIVERGED={relative}")
        worktree = (ROOT / relative).read_bytes().replace(b"\r\n", b"\n")
        if worktree != git_blob(source_sha, relative):
            raise RuntimeError(f"C6D_STEP3_WORKTREE_BYTES_DIVERGED={relative}")


def remove_prevalidation_block(data: bytes, relative: str) -> bytes:
    text = data.decode("utf-8")
    blocks = [match for match in DOC_BLOCK.finditer(text) if "PRE-VALIDATION:" in match.group()]
    if len(blocks) != 1:
        raise RuntimeError(f"C6D_STEP3_PREVALIDATION_BLOCK_COUNT={relative}:{len(blocks)}")
    match = blocks[0]
    body = match.group()[3:-2]
    lines = body.splitlines(keepends=True)
    indices = [index for index, line in enumerate(lines) if "PRE-VALIDATION:" in line]
    if len(indices) != 1:
        raise RuntimeError(f"C6D_STEP3_PREVALIDATION_LINE_COUNT={relative}:{len(indices)}")
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
        raise RuntimeError(f"C6D_STEP3_PREVALIDATION_REMAINS={relative}")
    return sealed.encode("utf-8")


def sealed_core(data: bytes, verifier) -> bytes:
    text = data.decode("utf-8")
    imports = [f"import YangMills.RG.{module}Audit" for module, _ in verifier.BRICKS]
    present = [line for line in imports if line in text]
    if present:
        raise RuntimeError(f"C6D_STEP3_CORE_IMPORT_ALREADY_PRESENT={present!r}")
    if not text.endswith("\n"):
        text += "\n"
    text += "".join(line + "\n" for line in imports)
    return text.encode("utf-8")


def digest(rows: list[tuple[str, bytes]]) -> str:
    payload = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {relative}\n".encode()
        for relative, data in rows
    )
    return hashlib.sha256(payload).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--evidence-json", type=Path, required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    verifier = load_verifier()
    paths = boundary_paths(verifier)
    require_clean_exact(paths, args.source_sha)
    require_evidence(args.evidence_json, args.source_sha, paths, verifier)
    rows = [
        (relative, remove_prevalidation_block(git_blob(args.source_sha, relative), relative))
        for relative in paths
    ]
    rows.append((CORE, sealed_core(git_blob(args.source_sha, CORE), verifier)))
    manifest_sha = digest(rows)
    if not args.apply:
        print(
            "C6D_STEP3_SEAL_PREVIEW_OK "
            f"files={len(rows)} source_sha={args.source_sha} "
            f"sealed_manifest_sha256={manifest_sha}"
        )
        return 0

    originals = {relative: (ROOT / relative).read_bytes() for relative, _ in rows}
    written: list[str] = []
    try:
        for relative, data in rows:
            (ROOT / relative).write_bytes(data)
            written.append(relative)
        actual = digest([(relative, (ROOT / relative).read_bytes()) for relative, _ in rows])
        if actual != manifest_sha:
            raise RuntimeError(f"C6D_STEP3_POSTWRITE_MANIFEST_MISMATCH={actual}")
    except Exception:
        for relative in reversed(written):
            (ROOT / relative).write_bytes(originals[relative])
        raise

    print(
        "C6D_STEP3_SEAL_APPLY_OK "
        f"files={len(rows)} source_sha={args.source_sha} "
        f"sealed_manifest_sha256={manifest_sha}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
