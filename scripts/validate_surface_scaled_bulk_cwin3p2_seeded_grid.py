"""Replay validator for the diagnostic seeded-grid sign-row pair."""

from fractions import Fraction
import argparse
import hashlib
from pathlib import Path
from flint import arb

ROOT = Path(__file__).resolve().parents[1]
DEPS = (
    "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_seeded_grid.py",
    "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high.py",
    "scripts/certify_bulk_beta_taylor_scaled_design.py",
    "scripts/certify_bulk_beta_taylor_arb.py",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path, unit, lo, hi):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED BULK SIGN ROW UNIT CWIN3P2 SEEDED GRID"
    assert f"unit {unit}" in lines
    assert "SCALED BULK SIGN ROW SEEDED GRID PASS" in lines
    assert any("no G2/G6 promotion" in line for line in lines)
    beta = next(x for x in lines if x.startswith("beta_domain ")).split()
    assert Fraction(beta[1]) == lo and Fraction(beta[2]) == hi
    deps = {x.split()[1]: x.split()[3] for x in lines
            if x.startswith("dependency ")}
    assert deps == {x: sha256(ROOT / x) for x in DEPS}
    parts = []
    for line in lines:
        if line.startswith("t_partition "):
            _, index, a, b = line.split()
            parts.append((int(index), Fraction(a), Fraction(b)))
    assert parts and [x[0] for x in parts] == list(range(len(parts)))
    domain = next(x for x in lines if x.startswith("t_domain ")).split()
    cursor = Fraction(domain[1]); rows = []
    for line in lines:
        if not line.startswith("trow "):
            continue
        head, upper_text = line.split(" upper ", 1)
        _, index, _, partition, x1, x2 = head.split()
        rows.append((int(index), int(partition), Fraction(x1), Fraction(x2), arb(upper_text)))
    assert rows
    for expected, (index, partition, x1, x2, upper) in enumerate(rows):
        assert index == expected and 0 <= partition < len(parts)
        assert x1 == cursor and x2 > x1 and upper < 0
        cursor = x2
    assert cursor == Fraction(domain[2])
    declared = int(next(x.split()[1] for x in lines if x.startswith("t_rows ")))
    assert declared == len(rows)
    return lines, len(rows)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    lo, hi = Fraction(args.lo), Fraction(args.hi)
    first = ROOT / "scripts" / f"surface_scaled_bulk_{args.unit}.txt"
    second = ROOT / "scripts" / f"surface_scaled_bulk_{args.unit}_rerun.txt"
    a, count = parse(first, args.unit, lo, hi)
    b, count2 = parse(second, args.unit, lo, hi)
    assert a == b and count == count2
    print("SEEDED GRID VALIDATION PASS", args.unit, "t_rows", count)
