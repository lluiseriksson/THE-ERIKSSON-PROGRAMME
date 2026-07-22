"""Read-only beta-domain inventory for the finite scaled bridge candidates.

This parser intentionally requires a production/replay pair before admitting
an interval to the coverage union.  It reports topology only; it does not
convert sign rows into `(H_tail)` or promote G2.
"""

from fractions import Fraction
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET_LO = Fraction(20)
TARGET_HI = Fraction(1000, 9)
DOMAIN = re.compile(r"^beta_domain\s+(\S+)\s+(\S+)")
BOX = re.compile(r"^beta-box\s+\[([^,]+),\s*([^\]]+)\]")
CONFIG = re.compile(r"^config\s+beta_lo\s+(\S+)\s+beta_hi\s+(\S+)")
UNIT = re.compile(r"^beta_unit\s+\S+\s+lo\s+(\S+)\s+hi\s+(\S+)")
TITLE = re.compile(r".*\[([^,\]]+),\s*([^\]]+)\].*$")


def parse_interval(path: Path):
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    match = next((DOMAIN.match(line) for line in lines if DOMAIN.match(line)), None)
    if match:
        return Fraction(match.group(1)), Fraction(match.group(2))
    match = next((CONFIG.match(line) for line in lines if CONFIG.match(line)), None)
    if match:
        return Fraction(match.group(1)), Fraction(match.group(2))
    units = [UNIT.match(line) for line in lines if UNIT.match(line)]
    if units:
        return Fraction(units[0].group(1)), Fraction(units[-1].group(2))
    match = TITLE.match(lines[0]) if lines else None
    if match:
        try:
            return Fraction(match.group(1)), Fraction(match.group(2))
        except ValueError:
            pass
    boxes = [BOX.match(line) for line in lines if BOX.match(line)]
    if not boxes:
        return None
    return Fraction(boxes[0].group(1)), Fraction(boxes[-1].group(2))


def main():
    admitted = []
    unpaired = []
    for path in ROOT.joinpath("scripts").glob("surface_scaled_bulk_*.txt"):
        name = path.name
        # `_run` files are short stdout/error scratch captures, not the
        # canonical production transcript.  They must not create a spurious
        # unpaired interval when the corresponding `.txt` + `_rerun.txt`
        # pair is already present.
        if ("_rerun" in name or "_run" in name or "design" in name or ".failed" in name
                or name.startswith("surface_scaled_bulk_u")):
            continue
        replay = path.with_name(path.stem + "_rerun.txt")
        interval = parse_interval(path)
        if interval is None:
            continue
        lo, hi = interval
        if hi <= TARGET_LO or lo >= TARGET_HI:
            continue
        if not replay.is_file():
            unpaired.append((lo, hi, name))
            continue
        admitted.append((max(lo, TARGET_LO), min(hi, TARGET_HI), name))
    admitted.sort()
    components = []
    for lo, hi, name in admitted:
        if not components or lo > components[-1][1]:
            components.append([lo, hi, [name]])
        else:
            components[-1][1] = max(components[-1][1], hi)
            components[-1][2].append(name)
    gaps = []
    cursor = TARGET_LO
    for lo, hi, _ in components:
        if lo > cursor:
            gaps.append((cursor, lo))
        cursor = max(cursor, hi)
    if cursor < TARGET_HI:
        gaps.append((cursor, TARGET_HI))
    print("FINITE-BETA CANDIDATE COVERAGE AUDIT")
    print("paired_intervals", len(admitted))
    for lo, hi, names in components:
        print("component", lo, hi, "sources", len(names))
    print("gaps", len(gaps), *[f"[{lo},{hi}]" for lo, hi in gaps])
    print("unpaired_overlapping", len(unpaired))
    for lo, hi, name in sorted(unpaired):
        print("unpaired", lo, hi, name)
    print("SCOPE topology only; no G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
