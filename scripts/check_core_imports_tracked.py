#!/usr/bin/env python3
"""Require every local source in the YangMillsCore import closure to be tracked.

This catches the dangerous hot-worktree case where Lean can build against an
untracked source (or a stale ``.olean``) that a clean clone cannot reproduce.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
ENTRY = Path("YangMillsCore.lean")
IMPORT_RE = re.compile(r"^\s*import\s+(.+)$", re.MULTILINE)


def strip_comments(text: str) -> str:
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        if depth == 0 and text[i : i + 2] == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif depth and text[i : i + 2] == "/-":
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text[i : i + 2] == "-/":
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text[i : i + 2] == "--":
            end = text.find("\n", i)
            if end == -1:
                out.extend(" " * (len(text) - i))
                break
            out.extend(" " * (end - i))
            i = end
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def local_imports(source: Path) -> list[Path]:
    text = strip_comments((ROOT / source).read_text(encoding="utf-8"))
    modules = [
        token
        for match in IMPORT_RE.finditer(text)
        for token in match.group(1).split()
    ]
    result: list[Path] = []
    for module in modules:
        candidate = Path(*module.split(".")).with_suffix(".lean")
        if (ROOT / candidate).is_file():
            result.append(candidate)
        elif module.startswith(("YangMills.", "Lean.")):
            raise FileNotFoundError(
                f"{source.as_posix()} imports missing local source "
                f"{candidate.as_posix()}"
            )
    return result


def tracked_files() -> set[str]:
    command = [
        "git",
        "-C",
        str(ROOT),
        "-c",
        f"safe.directory={ROOT.as_posix()}",
        "ls-files",
        "-z",
    ]
    completed = subprocess.run(command, check=True, capture_output=True)
    return {
        item.decode("utf-8").replace("\\", "/")
        for item in completed.stdout.split(b"\0")
        if item
    }


def main() -> int:
    tracked = tracked_files()
    pending = [ENTRY]
    visited: set[Path] = set()
    missing: list[Path] = []

    while pending:
        source = pending.pop()
        if source in visited:
            continue
        visited.add(source)
        if source.as_posix() not in tracked:
            missing.append(source)
        pending.extend(local_imports(source))

    if missing:
        print("ERROR: untracked source(s) in YangMillsCore import closure:")
        for source in sorted(missing):
            print(f"  {source.as_posix()}")
        return 1

    print(
        "OK: all "
        f"{len(visited)} local sources in YangMillsCore import closure are tracked."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
