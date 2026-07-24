"""Independent validator for paired 300-bit rescue transcripts."""
from fractions import Fraction
import hashlib
from pathlib import Path
from flint import arb

ROOT = Path(__file__).resolve().parents[1]
DEPS = (
    "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_rescue300.py",
    "scripts/certify_bulk_beta_taylor_scaled_design.py",
    "scripts/certify_bulk_beta_taylor_arb.py",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path, unit, lo, hi):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED BULK SIGN ROW UNIT CWIN3P2 RESCUE300"
    assert f"unit {unit}" in lines
    assert "SCALED BULK SIGN ROW PASS" in lines
    assert "SCOPE candidate rescue unit only; no G2/G6 promotion" in lines
    beta = next(x for x in lines if x.startswith("beta_domain ")).split()
    assert Fraction(beta[1]) == lo and Fraction(beta[2]) == hi
    config = next(x for x in lines if x.startswith("config "))
    assert "CWIN 3/2 beta_order 40 t_order 50 min_dt 1/100000 prec 300" in config
    deps = {x.split()[1]: x.split()[3] for x in lines if x.startswith("dependency ")}
    assert deps == {x: sha256(ROOT / x) for x in DEPS}
    domain = next(x for x in lines if x.startswith("t_domain ")).split()
    cursor = Fraction(domain[1]); rows = []
    for row in lines:
        if not row.startswith("trow "):
            continue
        head, upper_text = row.split(" upper ", 1)
        _, index, x1, x2 = head.split()
        rows.append((int(index), Fraction(x1), Fraction(x2), arb(upper_text)))
    assert rows
    for expected, (index, x1, x2, upper) in enumerate(rows):
        assert index == expected and x1 == cursor and x2 > x1 and upper < 0
        cursor = x2
    assert cursor == Fraction(domain[2])
    assert int(next(x.split()[1] for x in lines if x.startswith("t_rows "))) == len(rows)
    return lines


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    lo, hi = Fraction(args.lo), Fraction(args.hi)
    a = parse(ROOT / "scripts" / f"surface_scaled_bulk_{args.unit}.txt", args.unit, lo, hi)
    b = parse(ROOT / "scripts" / f"surface_scaled_bulk_{args.unit}_rerun.txt", args.unit, lo, hi)
    assert a == b
    print("CWIN3P2 RESCUE300 VALIDATION PASS", args.unit,
          "t_rows", sum(x.startswith("trow ") for x in a))


if __name__ == "__main__":
    main()
