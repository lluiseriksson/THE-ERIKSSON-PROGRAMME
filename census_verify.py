#!/usr/bin/env python3
"""
census_verify.py  v0.17.0 — Authoritative axiom census for THE-ERIKSSON-PROGRAMME.

Changes from v0.16.0:
  • Strips /- block comments -/ (including nested) before scanning.
    This prevents false positives from axiom references inside comments.
  • Strips -- line comments (inline) before scanning.
  • Keeps prime-aware regex [\w']+ for Lean identifier apostrophes.

Run:
    python3 census_verify.py /path/to/THE-ERIKSSON-PROGRAMME
"""

import re
import sys
from pathlib import Path
from collections import defaultdict

AXIOM_RE = re.compile(r"\baxiom\s+([\w']+)")


def strip_lean_comments(text: str) -> str:
    """Remove -- and /- ... -/ comments, preserving line structure."""
    result = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        c = text[i]
        if depth == 0:
            if text[i:i+2] == "/-":
                depth += 1
                result.append("  ")
                i += 2
            elif text[i:i+2] == "--":
                while i < n and text[i] != "\n":
                    result.append(" ")
                    i += 1
            else:
                result.append(c)
                i += 1
        else:
            if text[i:i+2] == "/-":
                depth += 1
                result.append("  ")
                i += 2
            elif text[i:i+2] == "-/":
                depth -= 1
                result.append("  ")
                i += 2
            else:
                result.append("\n" if c == "\n" else " ")
                i += 1
    return "".join(result)


def census(repo: Path) -> dict:
    results: dict[str, list] = defaultdict(list)
    yang_mills = repo / "YangMills"
    if not yang_mills.is_dir():
        print(f"[ERROR] YangMills/ not found under {repo}", file=sys.stderr)
        return dict(results)
    for lean_file in sorted(yang_mills.rglob("*.lean")):
        try:
            raw = lean_file.read_text(encoding="utf-8")
        except OSError:
            continue
        cleaned = strip_lean_comments(raw)
        rel = str(lean_file.relative_to(repo))
        for i, line in enumerate(cleaned.splitlines(), 1):
            for m in AXIOM_RE.finditer(line):
                name = m.group(1)
                if len(name) < 2:
                    continue
                results[name].append((rel, i))
    return dict(results)


def main() -> None:
    if len(sys.argv) >= 2:
        repo = Path(sys.argv[1])
    else:
        candidates = [
            Path("/content/THE-ERIKSSON-PROGRAMME"),
            Path.cwd() / "THE-ERIKSSON-PROGRAMME",
            Path.cwd(),
        ]
        repo = next((c for c in candidates if (c / "YangMills").is_dir()), None)
        if repo is None:
            print("Usage: census_verify.py <repo_root>")
            sys.exit(1)

    print(f"Census of: {repo}")
    print("=" * 70)

    results = census(repo)
    unique = sorted(results.keys())
    duplicates = {n: locs for n, locs in results.items() if len(locs) > 1}

    print(f"Total unique axiom names : {len(unique)}")
    print(f"Names with >1 declaration: {len(duplicates)}")
    print()

    for name in unique:
        locs = results[name]
        tag = " *** DUPLICATE ***" if len(locs) > 1 else ""
        print(f"  {name}{tag}")
        for (path, lineno) in locs:
            print(f"      {path}:{lineno}")

    if duplicates:
        print()
        print("GENUINE DUPLICATES:")
        for name, locs in duplicates.items():
            print(f"  {name!r}:")
            for (path, lineno) in locs:
                print(f"      {path}:{lineno}")
        print()
        print("NOTE: primed names (e.g. generatorMatrix') are DISTINCT from")
        print("      unprimed (generatorMatrix). Never treat as duplicates.")

    print()
    print("Census complete.")


if __name__ == "__main__":
    main()
