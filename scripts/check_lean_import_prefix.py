#!/usr/bin/env python3
"""Reject Lean imports that occur after a command or documentation comment.

Lean accepts ordinary comments before imports, but module/declaration docstrings are
commands for this purpose: a later ``import`` is rejected by the parser.  This guard is
deliberately textual and lightweight so it can run before a remote compiler session.
With no arguments it checks every tracked ``*.lean`` file; explicit paths narrow it.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


def tracked_lean_files(root: Path) -> list[Path]:
    completed = subprocess.run(
        ["git", "ls-files", "--", "*.lean"],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    return [root / line for line in completed.stdout.splitlines() if line]


def late_imports(path: Path) -> list[tuple[int, str]]:
    text = path.read_text(encoding="utf-8-sig")
    comment_stack: list[bool] = []  # True exactly for a doc-comment layer.
    command_seen = False
    failures: list[tuple[int, str]] = []

    for line_number, line in enumerate(text.splitlines(), start=1):
        visible: list[str] = []
        i = 0
        while i < len(line):
            if comment_stack:
                if line.startswith("/-", i):
                    comment_stack.append(line.startswith(("/-!", "/--"), i))
                    i += 2
                elif line.startswith("-/", i):
                    comment_stack.pop()
                    i += 2
                else:
                    i += 1
                continue

            if line.startswith("--", i):
                break
            if line.startswith("/-", i):
                is_doc = line.startswith(("/-!", "/--"), i)
                comment_stack.append(is_doc)
                if is_doc:
                    command_seen = True
                i += 2
                continue
            visible.append(line[i])
            i += 1

        code = "".join(visible).strip()
        if not code:
            continue
        if code == "prelude":
            continue
        if code == "import" or code.startswith("import "):
            if command_seen:
                failures.append((line_number, line.strip()))
        else:
            command_seen = True

    return failures


def main(argv: list[str]) -> int:
    root = Path(__file__).resolve().parents[1]
    paths = [Path(arg).resolve() for arg in argv] if argv else tracked_lean_files(root)
    failures: list[str] = []
    for path in paths:
        for line_number, line in late_imports(path):
            try:
                label = path.relative_to(root)
            except ValueError:
                label = path
            failures.append(f"{label}:{line_number}: late import: {line}")

    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"LEAN_IMPORT_PREFIX_OK files={len(paths)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
