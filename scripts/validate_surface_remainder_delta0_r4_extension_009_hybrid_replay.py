"""Validate a distinct replay namespace against the hybrid009 K2 transcripts.

The production launcher writes to ``scripts/`` and has no output-directory
option.  This validator deliberately accepts an explicit replay directory and
compares the deterministic transcript fields, ignoring only the wall-clock
``elapsed_seconds`` suffix on the terminal line.
"""

import argparse
import json
import re
from pathlib import Path

from flint import arb

import certify_surface_remainder_delta0_r4_extension_009_hybrid as cert
import surface_remainder_delta0_r4_extension_009_hybrid_contract as hybrid


ROOT = Path(__file__).resolve().parents[1]
PREFIX = "certify_surface_remainder_delta0_r4_extension_009_hybrid_"
ELAPSED = re.compile(r"(elapsed_seconds\s+)[^\s]+$")


def transcript(path):
    return path.read_text(encoding="utf-8").splitlines()


def normalized(lines):
    out = []
    for line in lines:
        if line.startswith("CERTIFIED UNIT "):
            line = ELAPSED.sub(r"\1<wall-clock>", line)
        out.append(line)
    return out


def validate(production_dir, replay_dir):
    units = hybrid.regular_units()
    expected = {u.slug for u in units}
    seen = set()
    for unit in units:
        prod = production_dir / f"{PREFIX}{unit.slug}.txt"
        replay = replay_dir / f"{PREFIX}{unit.slug}.txt"
        if not prod.is_file() or not replay.is_file():
            raise AssertionError(f"missing production/replay: {unit.slug}")
        p_lines, r_lines = transcript(prod), transcript(replay)
        if any("CERTIFICATE FAIL" in x for x in r_lines):
            raise AssertionError(f"replay failure marker: {unit.slug}")
        if normalized(p_lines) != normalized(r_lines):
            raise AssertionError(f"deterministic transcript mismatch: {unit.slug}")
        row_lines = [x for x in r_lines if x.startswith("ROW ")]
        if len(row_lines) != 1:
            raise AssertionError(f"replay row count: {unit.slug}")
        row = json.loads(row_lines[0][4:])
        if row.get("slug") != unit.slug or not arb(row["margin_lower"]) > 0:
            raise AssertionError(f"replay row contract or margin: {unit.slug}")
        seen.add(unit.slug)
    if seen != expected:
        raise AssertionError("replay cover mismatch")
    print(
        "K2 hybrid009 independent replay VALID: 158 units; "
        "deterministic fields identical, wall-clock elapsed ignored; "
        "all replay margins strictly positive"
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--production", type=Path, default=ROOT / "scripts")
    parser.add_argument("--replay", type=Path, required=True)
    args = parser.parse_args()
    validate(args.production, args.replay)


if __name__ == "__main__":
    main()
