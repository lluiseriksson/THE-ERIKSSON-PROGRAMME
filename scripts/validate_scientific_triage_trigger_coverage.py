#!/usr/bin/env python3
"""Fail when a class-C direct dependency can bypass the triage workflow.

The dependency list is derived from the class-C nodeids in the triage
manifest and the imports/loaders in their test modules.  It is intentionally
not maintained as a second nominal list.
"""

from __future__ import annotations

import argparse
import ast
import json
from pathlib import Path, PurePosixPath
import re
from typing import Any


CLASS_C = "C_REPAIRABLE_DEBT"
EVENTS = ("push", "pull_request")


class CoverageError(RuntimeError):
    """The workflow trigger does not cover a derived class-C dependency."""


def load_manifest(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise CoverageError(f"classification unavailable or corrupt: {exc}") from exc
    failures = data.get("classified_failures")
    if not isinstance(failures, list):
        raise CoverageError("classification has no failure inventory")
    class_c = [item for item in failures if item.get("class") == CLASS_C]
    if len(class_c) != 5:
        raise CoverageError(f"expected five class-C nodeids, found {len(class_c)}")
    return data


def _module_path(repo: Path, module: str) -> str | None:
    candidates = []
    normalized = module.replace(".", "/") + ".py"
    candidates.append(normalized)
    if not module.startswith("scripts."):
        candidates.append("scripts/" + normalized)
    for candidate in candidates:
        if (repo / candidate).is_file():
            return PurePosixPath(candidate).as_posix()
    return None


def _literal_path_parts(node: ast.AST) -> list[str] | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return [node.value]
    if isinstance(node, ast.Name):
        return []
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
        left = _literal_path_parts(node.left)
        right = _literal_path_parts(node.right)
        if left is not None and right is not None:
            return left + right
    return None


def _direct_repo_dependencies(repo: Path, test_path: Path) -> list[str]:
    try:
        tree = ast.parse(test_path.read_text(encoding="utf-8"), filename=str(test_path))
    except (OSError, UnicodeError, SyntaxError) as exc:
        raise CoverageError(f"cannot parse class-C test {test_path}: {exc}") from exc
    dependencies: set[str] = set()
    for node in ast.walk(tree):
        modules: list[str] = []
        if isinstance(node, ast.ImportFrom) and node.module:
            modules.append(node.module)
        elif isinstance(node, ast.Import):
            modules.extend(alias.name for alias in node.names)
        for module in modules:
            resolved = _module_path(repo, module)
            if resolved is not None:
                dependencies.add(resolved)
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "spec_from_file_location"
            and len(node.args) >= 2
        ):
            parts = _literal_path_parts(node.args[1])
            if parts:
                candidate = PurePosixPath(*parts).as_posix()
                if (repo / candidate).is_file():
                    dependencies.add(candidate)
        if isinstance(node, ast.BinOp):
            parts = _literal_path_parts(node)
            if parts:
                candidate = PurePosixPath(*parts).as_posix()
                if (repo / candidate).is_file():
                    dependencies.add(candidate)
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "Path"
            and node.args
        ):
            parts = _literal_path_parts(node.args[0])
            if parts:
                candidate = PurePosixPath(*parts).as_posix()
                if (repo / candidate).is_file():
                    dependencies.add(candidate)
    if not dependencies:
        raise CoverageError(f"class-C test has no derived repository dependency: {test_path}")
    return sorted(dependencies)


def derive_dependencies(
    repo: Path, manifest: dict[str, Any]
) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    for item in manifest["classified_failures"]:
        if item.get("class") != CLASS_C:
            continue
        nodeid = item.get("nodeid")
        if not isinstance(nodeid, str) or "::" not in nodeid:
            raise CoverageError("class-C nodeid is absent or malformed")
        test_name = nodeid.split("::", 1)[0]
        test_rel = PurePosixPath(test_name).as_posix()
        test_path = repo / test_rel
        if not test_path.is_file():
            raise CoverageError(f"class-C test source is missing: {test_rel}")
        result[nodeid] = [test_rel, *_direct_repo_dependencies(repo, test_path)]
    if len(result) != 5:
        raise CoverageError(f"expected five derived class-C entries, found {len(result)}")
    return result


def _unquote(value: str) -> str:
    value = value.strip()
    if value[:1] in ("'", '"'):
        try:
            parsed = ast.literal_eval(value)
        except (SyntaxError, ValueError) as exc:
            raise CoverageError(f"invalid quoted workflow path: {value}") from exc
        if not isinstance(parsed, str):
            raise CoverageError(f"workflow path is not a string: {value}")
        return parsed
    return value


def workflow_patterns(path: Path) -> dict[str, tuple[str, list[str]]]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as exc:
        raise CoverageError(f"workflow unavailable: {exc}") from exc
    result: dict[str, tuple[str, list[str]]] = {}
    for event in EVENTS:
        event_line = f"  {event}:"
        try:
            start = lines.index(event_line)
        except ValueError as exc:
            raise CoverageError(f"workflow has no {event} trigger") from exc
        end = len(lines)
        for index in range(start + 1, len(lines)):
            line = lines[index]
            if line and not line.startswith("    "):
                end = index
                break
        modes = []
        for mode in ("paths", "paths-ignore"):
            marker = f"    {mode}:"
            if marker not in lines[start:end]:
                continue
            marker_index = lines.index(marker, start, end)
            patterns = []
            for line in lines[marker_index + 1 : end]:
                if line.startswith("      - "):
                    patterns.append(_unquote(line[len("      - ") :]))
                elif line.strip() and not line.startswith("      "):
                    break
            if not patterns:
                raise CoverageError(f"{event}.{mode} has no patterns")
            modes.append((mode, patterns))
        if len(modes) != 1:
            raise CoverageError(f"{event} must define exactly one paths mode")
        result[event] = modes[0]
    return result


def _pattern_regex(pattern: str) -> re.Pattern[str]:
    pieces = ["^"]
    index = 0
    while index < len(pattern):
        char = pattern[index]
        if char == "*":
            if index + 1 < len(pattern) and pattern[index + 1] == "*":
                index += 2
                if index < len(pattern) and pattern[index] == "/":
                    pieces.append("(?:.*/)?")
                    index += 1
                else:
                    pieces.append(".*")
                continue
            pieces.append("[^/]*")
        elif char == "?":
            pieces.append("[^/]")
        else:
            pieces.append(re.escape(char))
        index += 1
    pieces.append("$")
    return re.compile("".join(pieces))


def _matches(path: str, pattern: str) -> bool:
    return _pattern_regex(pattern).fullmatch(path) is not None


def trigger_match(path: str, mode: str, patterns: list[str]) -> tuple[bool, str]:
    if mode == "paths-ignore":
        ignored = next((pattern for pattern in patterns if _matches(path, pattern)), "")
        return not bool(ignored), ignored or "<not ignored>"
    included = False
    decisive = ""
    for pattern in patterns:
        negative = pattern.startswith("!")
        candidate = pattern[1:] if negative else pattern
        if _matches(path, candidate):
            included = not negative
            decisive = pattern
    return included, decisive


def verify_coverage(
    dependencies: dict[str, list[str]],
    triggers: dict[str, tuple[str, list[str]]],
) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    missing: list[str] = []
    for nodeid, paths in dependencies.items():
        for dependency in paths:
            row = {"nodeid": nodeid, "dependency": dependency}
            for event in EVENTS:
                mode, patterns = triggers[event]
                covered, decisive = trigger_match(dependency, mode, patterns)
                row[event] = decisive
                if not covered:
                    missing.append(f"{event}:{dependency}")
            rows.append(row)
    if missing:
        raise CoverageError("uncovered class-C trigger dependency: " + missing[0])
    return rows


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--manifest", type=Path, default=Path(".github/scientific-test-triage.json")
    )
    parser.add_argument(
        "--workflow", type=Path, default=Path(".github/workflows/control-plane.yml")
    )
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    args = parser.parse_args()
    try:
        repo = args.repo.resolve()
        manifest = load_manifest(args.manifest)
        dependencies = derive_dependencies(repo, manifest)
        triggers = workflow_patterns(args.workflow)
        rows = verify_coverage(dependencies, triggers)
    except CoverageError as exc:
        print(f"SCIENTIFIC_TRIAGE_TRIGGER_COVERAGE FAIL: {exc}")
        return 2
    for row in rows:
        print(
            "C_TRIGGER",
            row["nodeid"],
            "dependency=" + row["dependency"],
            "push=" + row["push"],
            "pull_request=" + row["pull_request"],
        )
    print(
        "SCIENTIFIC_TRIAGE_TRIGGER_COVERAGE PASS",
        f"class_c={len(dependencies)} dependencies={len(rows)} exit=0",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
