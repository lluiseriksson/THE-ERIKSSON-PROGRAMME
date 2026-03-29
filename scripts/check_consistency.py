#!/usr/bin/env python3
"""
check_consistency.py — Lean source consistency checker.

ONLY bans:  sorry  (silent gap; always forbidden)
Does NOT ban:
  - axiom   (explicit named gap; this is the project's honesty mechanism;
              all axioms must be listed in AXIOM_FRONTIER.md)
  - rfl, exact ⟨, default  (standard Lean constructs; banning them
              produces hundreds of false positives on valid proofs)
  - placeholder  (too broad; valid identifier substring in many modules)

A line is flagged for 'sorry' only when 'sorry' appears outside a line comment.
Pattern: 'sorry' present in the line AND the portion before 'sorry'
does not contain '--' (i.e., sorry is not a comment token).
"""
import os
import re
import sys
from pathlib import Path

LEAN_DIRS = ["YangMills", "Lean"]

# Match the Lean keyword `sorry` as a whole word, not as a substring of
# identifiers like `sorrys`, `sorryMsg`, `not_sorry_at_all`, etc.
_SORRY_RE = re.compile(r'\bsorry\b')


def strip_block_comments(text: str) -> str:
    """
    Remove /- ... -/ block comments (including nested ones) from Lean source,
    replacing their contents with spaces while preserving newlines so that
    line numbers in error messages remain correct.
    """
    result: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        if depth == 0:
            if text[i:i+2] == '/-':
                depth += 1
                result.append('  ')
                i += 2
            else:
                result.append(text[i])
                i += 1
        else:
            if text[i:i+2] == '/-':
                depth += 1
                result.append('  ')
                i += 2
            elif text[i:i+2] == '-/':
                depth -= 1
                result.append('  ')
                i += 2
            elif text[i] == '\n':
                result.append('\n')   # preserve line structure
                i += 1
            else:
                result.append(' ')    # blank out comment content
                i += 1
    return ''.join(result)


def _repo_root() -> Path:
    """
    Locate the repository root.  Tries in order:

    1. __file__  — when running as `python scripts/check_consistency.py`
    2. ERIKSSON_REPO_ROOT env var  — explicit override
    3. Walk upward from cwd looking for lakefile.lean  — catches `%cd repo_root`
    4. Check cwd / 'THE-ERIKSSON-PROGRAMME'  — Colab default clone location
    5. Walk upward from cwd looking for YangMills/ directory  — last resort
    6. cwd  — fallback
    """
    # 1. Script mode (__file__ is defined)
    try:
        candidate = Path(__file__).resolve().parent.parent
        if (candidate / "lakefile.lean").exists():
            return candidate
    except NameError:
        pass

    # 2. Explicit env var
    env = os.environ.get("ERIKSSON_REPO_ROOT")
    if env:
        return Path(env).resolve()

    # 3. Walk up from cwd looking for lakefile.lean
    cwd = Path.cwd().resolve()
    for ancestor in [cwd, *cwd.parents]:
        if (ancestor / "lakefile.lean").exists():
            return ancestor

    # 4. Sibling: cwd / 'THE-ERIKSSON-PROGRAMME'  (Colab: clone into /content/...)
    sibling = cwd / "THE-ERIKSSON-PROGRAMME"
    if (sibling / "lakefile.lean").exists():
        return sibling

    # 5. Walk up looking for YangMills/ directory
    for ancestor in [cwd, *cwd.parents]:
        if (ancestor / "YangMills").is_dir():
            return ancestor

    # 6. Give up — return cwd
    return cwd


def line_has_sorry(line: str) -> bool:
    """
    Return True iff the Lean keyword `sorry` (whole word) appears in the
    non-comment portion of *line* (block comments already stripped by caller).

    Uses \\bsorry\\b so that `sorrys`, `not_sorry`, etc. are NOT flagged.
    Only the `--` line-comment prefix is handled here.
    """
    comment_start = line.find("--")
    code_part = line[:comment_start] if comment_start != -1 else line
    return bool(_SORRY_RE.search(code_part))


def scan() -> None:
    errors: list[str] = []
    root_dir = _repo_root()

    for ext in (".lean", ".Lean"):
        for d in LEAN_DIRS:
            dir_path = root_dir / d
            if not (dir_path.exists() and dir_path.is_dir()):
                continue
            for p in dir_path.rglob(f"*{ext}"):
                try:
                    text = p.read_text(encoding="utf-8")
                except OSError as exc:
                    errors.append(f"{p}: read error — {exc}")
                    continue
                # Strip /- ... -/ block comments first so that documentation
                # phrases like "0 sorrys" or "-- sorry" inside docblocks are
                # not mistaken for real sorry terms.
                cleaned = strip_block_comments(text)
                for line_no, line in enumerate(cleaned.splitlines(), 1):
                    if line_has_sorry(line):
                        errors.append(f"{p}:{line_no} → {text.splitlines()[line_no-1].strip()}")

    if errors:
        print(f"❌ SORRY DETECTED — {len(errors)} occurrence(s):")
        for e in errors[:20]:
            print(f"   {e}")
        if len(errors) > 20:
            print(f"   ... ({len(errors) - 20} more)")
        print()
        print("All gaps must use explicit named `axiom` declarations.")
        print("See AXIOM_FRONTIER.md for the registered frontier.")
        sys.exit(1)

    print("✅ Zero sorry in Lean source — all gaps are explicit named axioms")
    print("   (Verify the axiom frontier: AXIOM_FRONTIER.md)")


if __name__ == "__main__":
    scan()
