#!/usr/bin/env python3
"""Fail-closed promotion of the C6d terminal coercivity source/audit pair.

Promotion preserves the PRE-VALIDATION notices and is not certification.  A
subsequent cold source/audit/root gate must pass before either notice is
removed or the result is used as evidence.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PATH_FILE = ROOT / "tmp" / "C6D-TERMINAL-COERCIVITY-DRAFT-PATHS.txt"
CORE = "YangMillsCore.lean"
EXPECTED_PATHS = 2
REQUIRED_SEALED_PREREQUISITES = (
    "YangMills/RG/BalabanCMP85SourcePrefixGreen.lean",
    "YangMills/RG/BalabanCMP99SourceGeneratedPoincareQprime.lean",
    "YangMills/RG/BalabanCMP99SourceMassWeights.lean",
)


def git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def require_commit(source_sha: str) -> None:
    if re.fullmatch(r"[0-9a-f]{40}", source_sha) is None:
        raise RuntimeError("C6D_TERMINAL_COERCIVITY_SOURCE_SHA_INVALID")
    child = git("rev-parse", f"{source_sha}^{{commit}}")
    if child.returncode != 0 or child.stdout.decode().strip() != source_sha:
        raise RuntimeError("C6D_TERMINAL_COERCIVITY_SOURCE_COMMIT_MISMATCH")


def git_blob(source_sha: str, relative: str) -> bytes:
    child = git("cat-file", "blob", f"{source_sha}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            f"C6D_TERMINAL_COERCIVITY_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def selected_paths() -> list[str]:
    rows = [
        line.strip()
        for line in PATH_FILE.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if len(rows) != EXPECTED_PATHS or len(set(rows)) != EXPECTED_PATHS:
        raise RuntimeError(
            f"C6D_TERMINAL_COERCIVITY_SCOPE={len(rows)}/{len(set(rows))}"
        )
    if not rows[0].endswith(".draft.lean") or "Audit" in rows[0]:
        raise RuntimeError("C6D_TERMINAL_COERCIVITY_SOURCE_ORDER_INVALID")
    if not rows[1].endswith("Audit.draft.lean"):
        raise RuntimeError("C6D_TERMINAL_COERCIVITY_AUDIT_ORDER_INVALID")
    return rows


def destination(relative: str) -> str:
    name = Path(relative).name.removesuffix(".draft.lean")
    return f"YangMills/RG/{name}.lean"


def require_clean_blob(source_sha: str, relative: str) -> bytes:
    status = git("status", "--porcelain=v1", "--", relative)
    if status.returncode != 0 or status.stdout:
        raise RuntimeError(f"C6D_TERMINAL_COERCIVITY_DIRTY={relative}")
    data = git_blob(source_sha, relative)
    if (ROOT / relative).read_bytes().replace(b"\r\n", b"\n") != data:
        raise RuntimeError(f"C6D_TERMINAL_COERCIVITY_DIVERGED={relative}")
    return data


def require_absent(source_sha: str, relative: str) -> None:
    status = git("status", "--porcelain=v1", "--", relative)
    probe = git("cat-file", "-e", f"{source_sha}:{relative}")
    if status.returncode != 0 or status.stdout or probe.returncode == 0:
        raise RuntimeError(f"C6D_TERMINAL_COERCIVITY_DESTINATION_EXISTS={relative}")
    if (ROOT / relative).exists():
        raise RuntimeError(f"C6D_TERMINAL_COERCIVITY_DESTINATION_EXISTS={relative}")


def require_sealed_prerequisites(source_sha: str) -> None:
    for relative in REQUIRED_SEALED_PREREQUISITES:
        if b"PRE-VALIDATION:" in git_blob(source_sha, relative):
            raise RuntimeError(
                f"C6D_TERMINAL_COERCIVITY_PREREQUISITE_UNSEALED={relative}"
            )


def retarget(data: bytes) -> bytes:
    text = re.sub(
        r"^import tmp\.([A-Za-z0-9_]+)\.draft$",
        r"import YangMills.RG.\1",
        data.decode("utf-8"),
        flags=re.MULTILINE,
    )
    if "import tmp." in text:
        raise RuntimeError("C6D_TERMINAL_COERCIVITY_TMP_IMPORT_REMAINS")
    if text.count("PRE-VALIDATION:") != 1:
        raise RuntimeError("C6D_TERMINAL_COERCIVITY_PREVALIDATION_COUNT")
    if re.search(r"(?m)^\s*axiom\b|\b(?:sorry|admit|by\?|exact\?)\b", text):
        raise RuntimeError("C6D_TERMINAL_COERCIVITY_FORBIDDEN_PLACEHOLDER")
    return text.encode()


def core_with_audit(data: bytes, audit_path: str) -> bytes:
    import_line = "import YangMills.RG." + Path(audit_path).name.removesuffix(
        ".draft.lean"
    )
    text = data.decode("utf-8")
    if import_line in text:
        raise RuntimeError("C6D_TERMINAL_COERCIVITY_CORE_IMPORT_EXISTS")
    if not text.endswith("\n"):
        text += "\n"
    return (text + import_line + "\n").encode()


def manifest_digest(rows: list[tuple[str, bytes]]) -> str:
    payload = b"".join(
        f"{hashlib.sha256(data).hexdigest().upper()}  {path}\n".encode()
        for path, data in rows
    )
    return hashlib.sha256(payload).hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    require_commit(args.source_sha)
    require_sealed_prerequisites(args.source_sha)
    selected = selected_paths()
    rows: list[tuple[str, bytes]] = []
    for scratch in selected:
        target = destination(scratch)
        require_absent(args.source_sha, target)
        rows.append((target, retarget(require_clean_blob(args.source_sha, scratch))))
    core_status = git("status", "--porcelain=v1", "--", CORE)
    if core_status.returncode != 0 or core_status.stdout:
        raise RuntimeError("C6D_TERMINAL_COERCIVITY_CORE_DIRTY")
    rows.append((CORE, core_with_audit(git_blob(args.source_sha, CORE), selected[1])))
    digest = manifest_digest(rows)

    if not args.apply:
        print(
            "C6D_TERMINAL_COERCIVITY_PROMOTION_PREVIEW_OK "
            f"files={len(rows)} source_sha={args.source_sha} "
            f"manifest_sha256={digest}"
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
        actual = manifest_digest(
            [(path, (ROOT / path).read_bytes()) for path, _ in rows]
        )
        if actual != digest:
            raise RuntimeError(
                f"C6D_TERMINAL_COERCIVITY_POSTWRITE={actual} WANT={digest}"
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
        "C6D_TERMINAL_COERCIVITY_PROMOTION_APPLY_OK "
        f"files={len(rows)} source_sha={args.source_sha} "
        f"manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
