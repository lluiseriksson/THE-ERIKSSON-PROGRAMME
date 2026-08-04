"""Fail closed on publishable placeholders and undeclared artifact toolchains.

This guard is intentionally light: it reads text/JSON and hashes files.  It
does not invoke Lean, Lake, an oracle, LaTeX, or the network.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Iterable


DEFAULT_TEX_PATHS = (
    "papers/spatial-reconstruction",
    "papers/parity-barriers",
    "papers/os-reconstruction-uniform",
)
DEFAULT_TOOLCHAIN_PATHS = ("papers/parity-barriers",)
OSLINE_RE = re.compile(r"\\osline\{[^{}]+\}\{(?P<line>[^{}]+)\}\{[^{}]+\}")
MARKED_ROW_RE = re.compile(
    r"&\s*(?P<cell>.*?)\s*\\\\\s*%\s*@@(?P<marker>[A-Z][A-Z0-9_]*)@@"
)
TOKEN_RE = re.compile(
    r"\b(?:JOBS?[A-Z0-9_]*|ORACLE[A-Z0-9_]*|DECLS[A-Z0-9_]*|"
    r"SORRYCOUNT|COREERRORS|[A-Z][A-Z0-9_]*(?:LINE|VEC))\b"
)
EXPLICIT_PLACEHOLDER_RE = re.compile(
    r"\b(?:TBD|TO_BE_FILLED|UNVERIFIED_VALUE|PUBLISHABLE_PLACEHOLDER|"
    r"pending independent count)\b",
    re.IGNORECASE,
)


def normalized_lf_bytes(path: Path) -> bytes:
    return path.read_bytes().replace(b"\r\n", b"\n").replace(b"\r", b"\n")


def sha256_lf(path: Path) -> str:
    return hashlib.sha256(normalized_lf_bytes(path)).hexdigest()


def iter_tex_files(repo: Path, relative_paths: Iterable[str]) -> Iterable[Path]:
    for relative in relative_paths:
        target = repo / relative
        if target.is_file() and target.suffix.lower() == ".tex":
            yield target
        elif target.is_dir():
            yield from sorted(target.rglob("*.tex"))


def placeholder_errors(repo: Path, relative_paths: Iterable[str]) -> list[str]:
    errors: list[str] = []
    for path in iter_tex_files(repo, relative_paths):
        relative = path.relative_to(repo).as_posix()
        text = normalized_lf_bytes(path).decode("utf-8", "replace")
        for number, line in enumerate(text.splitlines(), 1):
            for match in OSLINE_RE.finditer(line):
                value = match.group("line").strip()
                if not value.isdigit():
                    errors.append(
                        f"{relative}:{number}: non-numeric \\osline anchor {value!r}"
                    )
            row = MARKED_ROW_RE.search(line)
            if row and TOKEN_RE.search(row.group("cell")):
                errors.append(
                    f"{relative}:{number}: unresolved marked cell "
                    f"{row.group('marker')!r}: {row.group('cell').strip()!r}"
                )
            explicit = EXPLICIT_PLACEHOLDER_RE.search(line)
            if explicit:
                errors.append(
                    f"{relative}:{number}: explicit publishable placeholder "
                    f"{explicit.group(0)!r}"
                )
    return errors


def root_pins(repo: Path) -> tuple[str, str]:
    lean = (repo / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest = json.loads((repo / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(
        package["rev"] for package in manifest["packages"] if package["name"] == "mathlib"
    )
    return lean, mathlib


def toolchain_errors(repo: Path, relative_paths: Iterable[str]) -> list[str]:
    errors: list[str] = []
    actual_lean, actual_mathlib = root_pins(repo)
    for relative in relative_paths:
        directory = repo / relative
        if not directory.exists():
            continue
        lean_sources = sorted(directory.glob("*.lean"))
        if not lean_sources:
            continue
        declaration = directory / "ARTIFACT-TOOLCHAIN.json"
        if not declaration.is_file():
            errors.append(f"{relative}: Lean artifact has no ARTIFACT-TOOLCHAIN.json")
            continue
        try:
            data = json.loads(declaration.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as exc:
            errors.append(f"{relative}: invalid ARTIFACT-TOOLCHAIN.json: {exc}")
            continue
        try:
            verified = data["verified_environment"]
            main = data["main_tree_environment"]
            compatibility = data["compatibility"]
            declared_sources = {item["path"]: item for item in data["sources"]}
            evidence_path = repo / verified["evidence_path"]
            required_scalars = (
                verified["lean_toolchain"],
                verified["mathlib_commit"],
                verified["command"],
                compatibility["status"],
                compatibility["statement_change_requirement"],
            )
            if not all(isinstance(value, str) and value for value in required_scalars):
                raise KeyError("required non-empty string")
        except (KeyError, TypeError) as exc:
            errors.append(f"{relative}: incomplete toolchain declaration: {exc}")
            continue
        if main.get("lean_toolchain") != actual_lean:
            errors.append(f"{relative}: declared main Lean pin is stale")
        if main.get("mathlib_commit") != actual_mathlib:
            errors.append(f"{relative}: declared main Mathlib pin is stale")
        if not evidence_path.is_file():
            errors.append(f"{relative}: declared verification evidence is missing")
        elif verified.get("evidence_sha256_lf") != sha256_lf(evidence_path):
            errors.append(f"{relative}: verification evidence hash mismatch")
        for source in lean_sources:
            source_relative = source.relative_to(repo).as_posix()
            entry = declared_sources.get(source_relative)
            if entry is None:
                errors.append(f"{source_relative}: source missing from toolchain declaration")
            elif entry.get("sha256_lf") != sha256_lf(source):
                errors.append(f"{source_relative}: declared source hash mismatch")
        pins_differ = (
            verified["lean_toolchain"] != actual_lean
            or verified["mathlib_commit"] != actual_mathlib
        )
        if pins_differ and compatibility.get("migration_authorized") is True:
            reproduction = compatibility.get("main_tree_reproduction")
            if not isinstance(reproduction, dict):
                errors.append(
                    f"{relative}: authorized migration lacks main-tree reproduction evidence"
                )
                continue
            reproduction_evidence = repo / str(reproduction.get("evidence_path", ""))
            reproduction_source = repo / str(reproduction.get("source_path", ""))
            unchanged = (
                compatibility.get("status") == "reproduced_unchanged_on_main_tree"
                and compatibility.get("statement_change_requirement") == "none"
                and reproduction.get("lean_toolchain") == actual_lean
                and reproduction.get("mathlib_commit") == actual_mathlib
                and reproduction.get("exit_code") == 0
                and isinstance(reproduction.get("command"), str)
                and bool(reproduction["command"])
                and reproduction_source.is_file()
                and reproduction_source in lean_sources
                and reproduction.get("source_sha256_lf")
                == sha256_lf(reproduction_source)
            )
            if not unchanged:
                errors.append(
                    f"{relative}: authorized migration is not an unchanged main-tree reproduction"
                )
            if not reproduction_evidence.is_file():
                errors.append(f"{relative}: main-tree reproduction evidence is missing")
            elif reproduction.get("evidence_sha256_lf") != sha256_lf(
                reproduction_evidence
            ):
                errors.append(
                    f"{relative}: main-tree reproduction evidence hash mismatch"
                )
        elif pins_differ and compatibility.get("migration_authorized") is not False:
            errors.append(
                f"{relative}: differing pins require explicit migration decision"
            )
    return errors


def validate_repository(
    repo: Path,
    tex_paths: Iterable[str] = DEFAULT_TEX_PATHS,
    toolchain_paths: Iterable[str] = DEFAULT_TOOLCHAIN_PATHS,
) -> list[str]:
    return placeholder_errors(repo, tex_paths) + toolchain_errors(repo, toolchain_paths)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--tex-path", action="append", dest="tex_paths")
    parser.add_argument("--toolchain-path", action="append", dest="toolchain_paths")
    args = parser.parse_args(argv)
    errors = validate_repository(
        args.repo.resolve(),
        args.tex_paths or DEFAULT_TEX_PATHS,
        args.toolchain_paths or DEFAULT_TOOLCHAIN_PATHS,
    )
    if errors:
        for error in errors:
            print(f"FAIL: {error}")
        print(f"publication provenance guard: FAIL ({len(errors)} finding(s))")
        return 1
    print("publication provenance guard: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
