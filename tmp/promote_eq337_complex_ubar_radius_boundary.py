#!/usr/bin/env python3
"""Fail-closed promotion of the seven-pair Eq337 complex-Ubar boundary."""

from __future__ import annotations

import argparse
import ast
import hashlib
import importlib.util
import json
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PATHS_FILE = ROOT / "tmp" / "EQ337-COMPLEX-UBAR-RADIUS-DRAFT-PATHS.txt"
RUNNER = ROOT / "scripts" / "colab_eq337_complex_ubar_radius_validation.py"
HELPER = ROOT / "tmp" / "retarget_eq337_complex_ubar_radius_runner.py"
VERIFIER = ROOT / "tmp" / "verify_eq337_complex_ubar_radius_evidence.py"
PREREQUISITES = (
    ROOT / "YangMills" / "RG" / "BalabanCMP99Eq337PhysicalComplexPerturbedBackground.lean",
    ROOT / "YangMills" / "RG" / "BalabanCMP99Eq337PhysicalComplexPerturbedBackgroundAudit.lean",
)


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"MODULE_LOAD_FAILED={path}")
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


def git_blob(source_sha: str, relative: str) -> bytes:
    child = git("cat-file", "blob", f"{source_sha}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"UBAR_SOURCE_BLOB_FAILED={relative} "
            f"stderr={child.stderr.decode(errors='replace')}"
        )
    return child.stdout


def paths() -> list[str]:
    rows = [line.strip() for line in PATHS_FILE.read_text(encoding="utf-8").splitlines()]
    rows = [row for row in rows if row]
    if len(rows) != 14 or len(set(rows)) != 14:
        raise RuntimeError(f"UBAR_PROMOTION_SCOPE={len(rows)}/{len(set(rows))} WANT=14/14")
    return rows


def destination(relative: str) -> str:
    path = Path(relative)
    if path.parent.as_posix() != "tmp" or not path.name.endswith(".draft.lean"):
        raise RuntimeError(f"UBAR_PROMOTION_PATH_INVALID={relative}")
    return f"YangMills/RG/{path.name.removesuffix('.draft.lean')}.lean"


def boundary(source_sha: str) -> list[tuple[str, str, bytes]]:
    helper = load_module(HELPER, "eq337_ubar_retarget")
    expected = helper.source_blobs(ast.parse(RUNNER.read_text(encoding="utf-8")))
    selected = paths()
    if set(selected) != set(expected):
        raise RuntimeError("UBAR_PROMOTION_RUNNER_SCOPE_MISMATCH")
    rows: list[tuple[str, str, bytes]] = []
    for relative in selected:
        dirty = git("status", "--porcelain=v1", "--", relative)
        if dirty.returncode != 0 or dirty.stdout:
            raise RuntimeError(f"UBAR_PROMOTION_DIRTY={relative}")
        data = git_blob(source_sha, relative)
        measured = hashlib.sha256(data).hexdigest()
        if measured != expected[relative].lower():
            raise RuntimeError(
                f"UBAR_PROMOTION_HASH_MISMATCH={relative}:{measured}:{expected[relative]}"
            )
        rows.append((relative, destination(relative), data))
    return rows


def require_prerequisites() -> None:
    for path in PREREQUISITES:
        if not path.is_file():
            raise RuntimeError(f"UBAR_PREREQUISITE_MISSING={path.relative_to(ROOT)}")
        if "PRE-VALIDATION:" in path.read_text(encoding="utf-8-sig"):
            raise RuntimeError(f"UBAR_PREREQUISITE_NOT_SEALED={path.relative_to(ROOT)}")


def require_evidence(path: Path, verifier) -> None:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("status") != "EQ337_COMPLEX_UBAR_RADIUS_PACKAGE_OK":
        raise RuntimeError("UBAR_EVIDENCE_STATUS_MISMATCH")
    if payload.get("source_sha") != verifier.SOURCE_SHA:
        raise RuntimeError("UBAR_EVIDENCE_SOURCE_MISMATCH")
    if payload.get("runner_revision") != verifier.RUNNER_REV:
        raise RuntimeError("UBAR_EVIDENCE_RUNNER_MISMATCH")


def manifest_digest(rows: list[tuple[str, str, bytes]]) -> str:
    payload = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {dest}\n".encode()
        for _, dest, data in rows
    )
    return hashlib.sha256(payload).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--apply", action="store_true")
    parser.add_argument("--evidence-manifest", type=Path)
    args = parser.parse_args()

    verifier = load_module(VERIFIER, "eq337_ubar_verifier")
    rows = boundary(verifier.SOURCE_SHA)
    digest = manifest_digest(rows)
    if not args.apply:
        print(
            "EQ337_COMPLEX_UBAR_PROMOTION_PREVIEW_OK "
            f"files={len(rows)} source_sha={verifier.SOURCE_SHA} "
            f"manifest_sha256={digest}"
        )
        return 0
    if args.evidence_manifest is None:
        raise RuntimeError("UBAR_EVIDENCE_MANIFEST_REQUIRED")
    require_prerequisites()
    require_evidence(args.evidence_manifest.resolve(), verifier)

    created: list[Path] = []
    try:
        for _, relative, data in rows:
            target = ROOT / relative
            if target.exists():
                if target.read_bytes().replace(b"\r\n", b"\n") != data:
                    raise RuntimeError(f"UBAR_PROMOTION_DESTINATION_DIFFERS={relative}")
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            created.append(target)
    except Exception:
        for target in reversed(created):
            target.unlink(missing_ok=True)
        raise

    print(
        "EQ337_COMPLEX_UBAR_PROMOTION_APPLY_OK "
        f"files={len(rows)} created={len(created)} source_sha={verifier.SOURCE_SHA} "
        f"manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
