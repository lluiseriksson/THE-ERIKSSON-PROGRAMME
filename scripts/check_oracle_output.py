"""Check the output of `lake env lean oracle_check.lean` against the oracle contract.

Every `#print axioms` command in `oracle_check.lean` must produce exactly one
readout, in the same order, and every readout may depend only on Lean's three
standard axioms `[propext, Classical.choice, Quot.sound]` (a readout that
depends on no axioms at all is also accepted).  Anything else fails: `sorryAx`,
a project axiom, an error or warning line, a missing, extra or reordered
readout.  The output of each `#check` command in the file (a signature, not a
readout) is accepted once per command.

Lean wraps long readouts over several lines; continuation lines start with
whitespace and are joined back to the readout they belong to.

    python scripts/check_oracle_output.py --output oracle-output.txt
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ALLOWED = ("propext", "Classical.choice", "Quot.sound")
DEPENDS = re.compile(r"^'(?P<name>.+)' depends on axioms: \[(?P<axioms>[^\]]*)\]$")
AXIOM_FREE = re.compile(r"^'(?P<name>.+)' does not depend on any axioms$")
PRINT_AXIOMS = re.compile(r"#print\s+axioms\s+(\S+)")
CHECK = re.compile(r"^\s*#check\s+(\S+)", re.MULTILINE)


def strip_comments(source: str) -> str:
    """Remove Lean line comments and (nested) block comments, keeping newlines."""
    out: list[str] = []
    depth = 0
    i = 0
    n = len(source)
    while i < n:
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if source[i] == "\n":
                out.append("\n")
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = n if end < 0 else end
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


def requested_names(oracle_source: str) -> list[str]:
    return PRINT_AXIOMS.findall(strip_comments(oracle_source))


def checked_names(oracle_source: str) -> list[str]:
    return CHECK.findall(strip_comments(oracle_source))


def _is_check_output(record: str, names: list[str]) -> bool:
    return any(
        record.startswith(name) and record[len(name) : len(name) + 1] in (" ", ".", ":")
        for name in names
    )


def readouts(output: str) -> list[str]:
    records: list[str] = []
    for line in output.splitlines():
        if not line.strip():
            continue
        if line[:1].isspace() and records:
            records[-1] += " " + line.strip()
        else:
            records.append(line.rstrip())
    return records


def _same_name(requested: str, printed: str) -> bool:
    requested = requested.removeprefix("_root_.")
    return printed == requested or printed.endswith("." + requested)


def check(oracle_source: str, output: str) -> tuple[list[str], dict[str, int]]:
    errors: list[str] = []
    requested = requested_names(oracle_source)
    checks = checked_names(oracle_source)
    check_outputs = 0
    parsed: list[tuple[str, list[str]]] = []
    for record in readouts(output):
        match = DEPENDS.match(record)
        if match:
            axioms = [a.strip() for a in match["axioms"].split(",") if a.strip()]
            parsed.append((match["name"], axioms))
            continue
        match = AXIOM_FREE.match(record)
        if match:
            parsed.append((match["name"], []))
            continue
        if not record.startswith("'") and _is_check_output(record, checks):
            check_outputs += 1
            continue
        errors.append(f"unexpected output line: {record[:300]}")

    if not requested:
        errors.append("oracle_check.lean: no `#print axioms` commands found")
    if len(parsed) != len(requested):
        errors.append(
            f"readout count {len(parsed)} != `#print axioms` count {len(requested)}"
        )
    if check_outputs != len(checks):
        errors.append(f"`#check` output count {check_outputs} != `#check` count {len(checks)}")
    for index, (want, (got, _)) in enumerate(zip(requested, parsed), start=1):
        if not _same_name(want, got):
            errors.append(f"readout {index}: expected {want}, got {got}")
            break

    axiom_free = 0
    nonstandard = 0
    for name, axioms in parsed:
        if not axioms:
            axiom_free += 1
        extra = [a for a in axioms if a not in ALLOWED]
        if extra:
            nonstandard += 1
            errors.append(f"{name}: non-standard axioms {extra}")

    stats = {
        "requested": len(requested),
        "readouts": len(parsed),
        "standard_axioms_only": len(parsed) - axiom_free - nonstandard,
        "axiom_free": axiom_free,
        "nonstandard": nonstandard,
    }
    return errors, stats


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--oracle", type=Path, default=ROOT / "oracle_check.lean")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--json", type=Path, help="write the readout statistics here")
    args = parser.parse_args(argv)
    # Lean names are Unicode; keep a Windows console from crashing on them.
    sys.stdout.reconfigure(errors="backslashreplace")

    errors, stats = check(
        args.oracle.read_text(encoding="utf-8"),
        args.output.read_text(encoding="utf-8", errors="replace"),
    )
    if args.json:
        args.json.write_text(json.dumps({**stats, "errors": len(errors)}) + "\n")
    for error in errors[:50]:
        print(f"ERROR: {error}")
    if len(errors) > 50:
        print(f"... and {len(errors) - 50} more")
    print(
        f"{stats['readouts']}/{stats['requested']} readouts; "
        f"{stats['standard_axioms_only']} on [propext, Classical.choice, Quot.sound] "
        f"or a subset, {stats['axiom_free']} axiom-free, "
        f"{stats['nonstandard']} non-standard"
    )
    if errors:
        print(f"oracle check FAILED: {len(errors)} problem(s)")
        return 1
    print("oracle check OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
