"""Audit current CWIN=3/2 high-order production/replay components.

The audit is intentionally non-authoritative: it verifies each paired file's
local t coverage and reports beta gaps instead of treating disconnected
components as a theorem union.
"""

from fractions import Fraction
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
HEADER = "SCALED BULK SIGN ROW UNIT CWIN3P2 HIGH"
PI_UP = Fraction(31415927, 10_000_000)


def parse(path):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == HEADER
    config = next(x for x in lines if x.startswith("config "))
    standard = all(token in config for token in
                   ("CWIN 3/2", "beta_order 30", "t_order 37",
                    "min_dt 1/100000", "prec 180"))
    rescue = all(token in config for token in
                 ("CWIN 3/2", "beta_order 40", "t_order 45",
                  "min_dt 1/200000", "prec 220"))
    assert standard or rescue
    beta = next(x for x in lines if x.startswith("beta_domain ")).split()
    tdomain = next(x for x in lines if x.startswith("t_domain ")).split()
    lo, hi = Fraction(beta[1]), Fraction(beta[2])
    tlo, thi = Fraction(tdomain[1]), Fraction(tdomain[2])
    expected_hi = PI_UP - Fraction(3, 2) / hi
    assert (tlo, thi) == (Fraction(3, 5), expected_hi)
    rows = []
    cursor = tlo
    for line in lines:
        if not line.startswith("trow "):
            continue
        head = line.split(" upper ", 1)[0].split()
        _, index, x1, x2 = head
        x1, x2 = Fraction(x1), Fraction(x2)
        assert int(index) == len(rows) and x1 == cursor and x2 > x1
        upper = arb(line.split(" upper ", 1)[1])
        assert upper < 0
        rows.append((x1, x2))
        cursor = x2
    assert rows and cursor == thi
    return lo, hi, len(rows)


def main():
    ctx.prec = 180
    units = []
    for path in sorted((ROOT / "scripts").glob("surface_scaled_bulk*.txt")):
        if path.name.endswith("_rerun.txt") or path.name.endswith(".failed.txt"):
            continue
        try:
            lo, hi, rows = parse(path)
        # Failed/timeout probes may leave an empty scratch transcript.  Such
        # a file is not evidence and must be skipped rather than aborting the
        # aggregate audit before the admissible pairs are inspected.
        except (AssertionError, IndexError, StopIteration, ValueError, OSError):
            continue
        replay = path.with_name(path.stem + "_rerun.txt")
        if not replay.exists() or replay.read_bytes() != path.read_bytes():
            continue
        units.append((lo, hi, path.name, rows))
    assert units, "no paired high-order production/replay units"
    units.sort()
    components = []
    start = prev = units[0][0]
    rows_total = 0
    for lo, hi, name, rows in units:
        if lo > prev:
            components.append((start, prev))
            start = lo
        if hi > prev:
            prev = hi
        rows_total += rows
    components.append((start, prev))
    print("CWIN3P2 HIGH LOCAL UNION AUDIT")
    print("paired_units", len(units), "rows", rows_total)
    for lo, hi in components:
        print("component", lo, hi)
    for (left, right) in zip(components, components[1:]):
        print("gap", left[1], right[0])
    print("AUDIT PASS local t coverage and replay equality")
    print("SCOPE disconnected-component audit only; no G2/G6 promotion")


if __name__ == "__main__":
    main()
