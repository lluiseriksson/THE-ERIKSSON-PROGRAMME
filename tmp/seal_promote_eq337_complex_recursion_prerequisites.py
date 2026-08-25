#!/usr/bin/env python3
"""Seal the complete compiler-verified Eq. (3.37) recursion prerequisites.

The first evidence package audits the seven promoted Ubar pairs; the second
audits the inverse-radius and all-orientation small-field pairs while
materializing those promoted dependencies.  This helper binds both pieces of
evidence to exact Git blobs, removes the fourteen promoted Ubar notices,
promotes the two later pairs directly into their sealed paths, and imports all
nine audits into ``YangMillsCore``.  It never promotes the Mathlib-only repro.
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
UBAR_VERIFIER = ROOT / "tmp" / "verify_eq337_complex_ubar_radius_evidence.py"
RECURSION_VERIFIER = (
    ROOT / "tmp" / "verify_eq337_complex_forced_recursion_prereq_evidence.py"
)
BASE_SEALER = ROOT / "tmp" / "seal_eq337_complex_perturbed_background_prevalidation.py"
UBAR_PATHS_FILE = ROOT / "tmp" / "EQ337-COMPLEX-UBAR-RADIUS-DRAFT-PATHS.txt"
CORE = "YangMillsCore.lean"


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"EQ337_PREREQ_MODULE_LOAD_FAILED={path}")
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
            f"EQ337_PREREQ_SOURCE_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def destination(relative: str) -> str:
    path = Path(relative)
    if path.parent.as_posix() != "tmp" or not path.name.endswith(".draft.lean"):
        raise RuntimeError(f"EQ337_PREREQ_PROMOTION_PATH_INVALID={relative}")
    return f"YangMills/RG/{path.name.removesuffix('.draft.lean')}.lean"


def ubar_paths() -> list[str]:
    paths = [
        line.strip()
        for line in UBAR_PATHS_FILE.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if len(paths) != 14 or len(set(paths)) != 14:
        raise RuntimeError(f"EQ337_PREREQ_UBAR_SCOPE={len(paths)}/{len(set(paths))}")
    return paths


def recursion_paths(verifier) -> list[str]:
    paths = [
        path
        for module, _ in verifier.MODULES
        for path in (
            f"tmp/{module}.draft.lean",
            f"tmp/{module}Audit.draft.lean",
        )
    ]
    if len(paths) != 4 or len(set(paths)) != 4:
        raise RuntimeError(
            f"EQ337_PREREQ_RECURSION_SCOPE={len(paths)}/{len(set(paths))}"
        )
    return paths


def read_evidence(path: Path, status: str, declarations: int) -> dict:
    result = json.loads(path.read_text(encoding="utf-8"))
    if result.get("status") != status:
        raise RuntimeError(f"EQ337_PREREQ_EVIDENCE_STATUS_MISMATCH={status}")
    if result.get("expected_declarations") != declarations:
        raise RuntimeError(
            f"EQ337_PREREQ_EVIDENCE_DECLARATION_COUNT_MISMATCH={declarations}"
        )
    source_sha = result.get("source_sha")
    if not isinstance(source_sha, str) or re.fullmatch(r"[0-9a-f]{40}", source_sha) is None:
        raise RuntimeError("EQ337_PREREQ_EVIDENCE_SOURCE_INVALID")
    if not isinstance(result.get("boundary_blob_sha256"), dict):
        raise RuntimeError("EQ337_PREREQ_EVIDENCE_HASHES_MISSING")
    return result


def require_clean_existing(relative: str, source_sha: str) -> None:
    status = run_git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(
            f"EQ337_PREREQ_WORKTREE_DIRTY={relative}:"
            + status.stdout.decode(errors="replace").strip()
        )
    child = run_git("diff", "--quiet", source_sha, "--", relative)
    if child.returncode != 0:
        raise RuntimeError(f"EQ337_PREREQ_BOUNDARY_DIVERGED={relative}")
    worktree = (ROOT / relative).read_bytes().replace(b"\r\n", b"\n")
    if worktree != git_blob(source_sha, relative):
        raise RuntimeError(f"EQ337_PREREQ_WORKTREE_BYTES_DIVERGED={relative}")


def require_clean_absent(relative: str, source_sha: str) -> None:
    status = run_git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(
            f"EQ337_PREREQ_DESTINATION_DIRTY={relative}:"
            + status.stdout.decode(errors="replace").strip()
        )
    probe = run_git("cat-file", "-e", f"{source_sha}:{relative}")
    if probe.returncode == 0 or (ROOT / relative).exists():
        raise RuntimeError(f"EQ337_PREREQ_DESTINATION_ALREADY_EXISTS={relative}")


def checked_hash(result: dict, relative: str, data: bytes) -> None:
    wanted = result["boundary_blob_sha256"].get(relative)
    measured = hashlib.sha256(data).hexdigest()
    if wanted != measured:
        raise RuntimeError(
            f"EQ337_PREREQ_EVIDENCE_HASH_MISMATCH={relative}:{measured}:{wanted}"
        )


def sealed_rows(ubar_result: dict, recursion_result: dict) -> list[tuple[str, bytes]]:
    recursion_verifier = load_module(
        RECURSION_VERIFIER, "eq337_recursion_prereq_verifier"
    )
    sealer = load_module(BASE_SEALER, "eq337_base_notice_remover")
    source_sha = recursion_result["source_sha"]
    rows: list[tuple[str, bytes]] = []

    for scratch in ubar_paths():
        target = destination(scratch)
        require_clean_existing(target, source_sha)
        data = git_blob(source_sha, target)
        checked_hash(ubar_result, scratch, data)
        rows.append((target, sealer.remove_prevalidation_block(data, target)))

    for scratch in recursion_paths(recursion_verifier):
        data = git_blob(source_sha, scratch)
        checked_hash(recursion_result, scratch, data)
        target = destination(scratch)
        require_clean_absent(target, source_sha)
        rows.append((target, sealer.remove_prevalidation_block(data, target)))

    return rows


def sealed_core(data: bytes, recursion_verifier) -> bytes:
    modules = [
        Path(path).name.removesuffix("Audit.draft.lean")
        for path in ubar_paths()
        if path.endswith("Audit.draft.lean")
    ]
    modules.extend(module for module, _ in recursion_verifier.MODULES)
    imports = [f"import YangMills.RG.{module}Audit" for module in modules]
    if len(imports) != 9 or len(set(imports)) != 9:
        raise RuntimeError(f"EQ337_PREREQ_CORE_IMPORT_SCOPE={len(imports)}")
    text = data.decode("utf-8")
    present = [line for line in imports if line in text]
    if present:
        raise RuntimeError(f"EQ337_PREREQ_CORE_IMPORT_ALREADY_PRESENT={present!r}")
    if not text.endswith("\n"):
        text += "\n"
    return (text + "".join(line + "\n" for line in imports)).encode("utf-8")


def digest(rows: list[tuple[str, bytes]]) -> str:
    payload = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {relative}\n".encode()
        for relative, data in rows
    )
    return hashlib.sha256(payload).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ubar-evidence-json", type=Path, required=True)
    parser.add_argument("--recursion-evidence-json", type=Path, required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    ubar_result = read_evidence(
        args.ubar_evidence_json.resolve(),
        "EQ337_COMPLEX_UBAR_RADIUS_EVIDENCE_OK",
        78,
    )
    recursion_result = read_evidence(
        args.recursion_evidence_json.resolve(),
        "EQ337_COMPLEX_RECURSION_PREREQ_EVIDENCE_OK",
        14,
    )
    source_sha = recursion_result["source_sha"]
    resolved = run_git("rev-parse", f"{source_sha}^{{commit}}")
    if resolved.returncode != 0 or resolved.stdout.decode().strip() != source_sha:
        raise RuntimeError("EQ337_PREREQ_SOURCE_COMMIT_MISMATCH")
    require_clean_existing(CORE, source_sha)

    recursion_verifier = load_module(
        RECURSION_VERIFIER, "eq337_recursion_prereq_verifier_for_core"
    )
    rows = sealed_rows(ubar_result, recursion_result)
    rows.append((CORE, sealed_core(git_blob(source_sha, CORE), recursion_verifier)))
    if len(rows) != 19 or len({relative for relative, _ in rows}) != 19:
        raise RuntimeError(f"EQ337_PREREQ_SEAL_SCOPE={len(rows)}")
    manifest_sha = digest(rows)
    if not args.apply:
        print(
            "EQ337_COMPLEX_RECURSION_PREREQ_SEAL_PREVIEW_OK "
            f"files={len(rows)} promoted=18 source_sha={source_sha} "
            f"sealed_manifest_sha256={manifest_sha}"
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
        for relative, _ in rows[:-1]:
            if "PRE-VALIDATION:" in (ROOT / relative).read_text(encoding="utf-8-sig"):
                raise RuntimeError(
                    f"EQ337_PREREQ_POSTWRITE_PREVALIDATION_REMAINS={relative}"
                )
        actual = digest(
            [(relative, (ROOT / relative).read_bytes()) for relative, _ in rows]
        )
        if actual != manifest_sha:
            raise RuntimeError(
                f"EQ337_PREREQ_POSTWRITE_MANIFEST_MISMATCH={actual} WANT={manifest_sha}"
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
        "EQ337_COMPLEX_RECURSION_PREREQ_SEAL_APPLY_OK "
        f"files={len(rows)} promoted=18 source_sha={source_sha} "
        f"sealed_manifest_sha256={manifest_sha}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
