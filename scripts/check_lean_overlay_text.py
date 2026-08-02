#!/usr/bin/env python3
"""Lightweight textual gates for the exact Lean overlay being shipped.

The caller must identify the overlay explicitly, either as the tracked Lean
files changed between two Git objects or as a newline-delimited path list.
There is deliberately no whole-tree default: a green result must describe the
same files that the remote validation will compile.

This is not a Lean parser.  It removes comments and string literals, then
rejects ``sorry``/``admit`` tokens and checks the command-level balance of
``namespace``/``section`` (including ``noncomputable section``) against
``end``.  The latter catches the duplicated or missing ``end`` mistakes that
otherwise cost a cold remote elaboration cycle.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


FORBIDDEN = re.compile(r"\b(?:sorry|admit)\b")
OPEN = re.compile(r"^\s*(?:(?:noncomputable|private|protected)\s+)?(namespace|section)\b(?:\s+([^\s]+))?")
CLOSE = re.compile(r"^\s*end(?:\s+([^\s]+))?\s*$")


def git_changed_paths(root: Path, base: str, head: str) -> list[Path]:
    completed = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=ACMR", base, head, "--", "*.lean"],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    return [root / line for line in completed.stdout.splitlines() if line]


def listed_paths(root: Path, manifest: Path) -> list[Path]:
    paths: list[Path] = []
    for raw in manifest.read_text(encoding="utf-8-sig").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        path = Path(line)
        if not path.is_absolute():
            path = root / path
        if path.suffix == ".lean":
            paths.append(path)
    return paths


def visible_lines(text: str) -> list[str]:
    """Remove nested block comments, line comments, chars, and strings."""

    result: list[str] = []
    block_depth = 0
    in_string = False
    escaped = False
    line_chars: list[str] = []
    i = 0
    while i < len(text):
        ch = text[i]
        nxt = text[i : i + 2]

        if block_depth:
            if nxt == "/-":
                block_depth += 1
                i += 2
            elif nxt == "-/":
                block_depth -= 1
                i += 2
            else:
                if ch == "\n":
                    result.append("".join(line_chars))
                    line_chars = []
                i += 1
            continue

        if in_string:
            if ch == "\n":
                result.append("".join(line_chars))
                line_chars = []
                in_string = False
                escaped = False
            elif escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if nxt == "--":
            newline = text.find("\n", i + 2)
            if newline == -1:
                i = len(text)
            else:
                result.append("".join(line_chars))
                line_chars = []
                i = newline + 1
            continue
        if nxt == "/-":
            block_depth = 1
            i += 2
            continue
        if ch == '"':
            in_string = True
            i += 1
            continue
        if ch == "\n":
            result.append("".join(line_chars))
            line_chars = []
        else:
            line_chars.append(ch)
        i += 1

    result.append("".join(line_chars))
    return result


def check_file(root: Path, path: Path) -> list[str]:
    failures: list[str] = []
    try:
        label = path.resolve().relative_to(root.resolve())
    except ValueError:
        label = path
    if not path.is_file():
        return [f"{label}: overlay path is missing"]

    stack: list[tuple[str, str | None, int]] = []
    lines = visible_lines(path.read_text(encoding="utf-8-sig"))
    for line_number, line in enumerate(lines, start=1):
        forbidden = FORBIDDEN.search(line)
        if forbidden:
            failures.append(f"{label}:{line_number}: forbidden token: {forbidden.group(0)}")

        opened = OPEN.match(line)
        if opened:
            stack.append((opened.group(1), opened.group(2), line_number))
            continue

        closed = CLOSE.match(line)
        if not closed:
            continue
        if not stack:
            failures.append(f"{label}:{line_number}: unmatched end")
            continue
        kind, name, opened_at = stack.pop()
        close_name = closed.group(1)
        if close_name and name and close_name != name:
            failures.append(
                f"{label}:{line_number}: end {close_name} closes {kind} {name} opened at line {opened_at}"
            )

    for kind, name, opened_at in reversed(stack):
        suffix = f" {name}" if name else ""
        failures.append(f"{label}:{opened_at}: unclosed {kind}{suffix}")
    return failures


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--paths-from", type=Path)
    source.add_argument("--base", help="base Git object; requires --head")
    parser.add_argument("--head", help="head Git object for --base")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    root = Path(__file__).resolve().parents[1]
    if args.base:
        if not args.head:
            print("--base requires --head", file=sys.stderr)
            return 2
        paths = git_changed_paths(root, args.base, args.head)
        source = f"git:{args.base}..{args.head}"
    else:
        if args.head:
            print("--head is valid only with --base", file=sys.stderr)
            return 2
        manifest = args.paths_from.resolve()
        paths = listed_paths(root, manifest)
        source = f"paths:{manifest}"

    paths = sorted(set(paths))
    if not paths:
        print(f"overlay contains no Lean files: {source}", file=sys.stderr)
        return 2

    failures: list[str] = []
    for path in paths:
        failures.extend(check_file(root, path))
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"LEAN_OVERLAY_TEXT_OK files={len(paths)} source={source}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
