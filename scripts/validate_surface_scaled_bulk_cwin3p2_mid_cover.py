"""Validator for the frozen 42-unit mid-order cover."""

from fractions import Fraction
import hashlib
from pathlib import Path

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
START, END, WIDTH = Fraction(193, 4), Fraction(69), Fraction(1, 4)
DEPS = (
    "scripts/run_surface_scaled_bulk_cwin3p2_mid_cover.py",
    "scripts/certify_bulk_beta_taylor_scaled_design.py",
    "scripts/certify_bulk_beta_taylor_arb.py",
    "docs/SURFACE-G2-CWIN3P2-MID-COVER-48P25-69-PREREG-20260722.md",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def units():
    lo, index = START, 0
    while lo < END:
        hi = min(lo + WIDTH, END)
        yield index, lo, hi
        lo, index = hi, index + 1


def parse(path: Path, expected_lo: Fraction, expected_hi: Fraction):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER"
    assert "SCALED BULK SIGN ROW PASS" in lines
    assert "SCOPE quarantined mid-order cover unit only; no G2/G6 promotion" in lines
    config = next(line for line in lines if line.startswith("config "))
    assert all(token in config for token in (
        "CWIN 3/2", "beta_order 20", "t_order 25", "min_dt 1/100000", "prec 180"
    ))
    beta = next(line for line in lines if line.startswith("beta_domain ")).split()
    assert Fraction(beta[1]) == expected_lo and Fraction(beta[2]) == expected_hi
    deps = {line.split()[1]: line.split()[3]
            for line in lines if line.startswith("dependency ")}
    assert deps == {relative: sha256(ROOT / relative) for relative in DEPS}
    domain = next(line for line in lines if line.startswith("t_domain ")).split()
    cursor = Fraction(domain[1]); rows = []
    for line in lines:
        if not line.startswith("trow "):
            continue
        head, upper_text = line.split(" upper ", 1)
        _, index, x1, x2 = head.split()
        rows.append((int(index), Fraction(x1), Fraction(x2), arb(upper_text)))
    assert rows
    for expected, (index, x1, x2, upper) in enumerate(rows):
        assert index == expected and x1 == cursor and x2 > x1 and upper < 0
        cursor = x2
    assert cursor == Fraction(domain[2])
    count = int(next(line.split()[1] for line in lines
                     if line.startswith("t_rows ")))
    assert count == len(rows)
    return lines, count


def main() -> int:
    total_rows = 0
    for index, lo, hi in units():
        label = f"mid_cover_{index:02d}_{lo}_{hi}".replace("/", "_")
        production, count = parse(
            ROOT / "scripts" / f"surface_scaled_bulk_{label}.txt", lo, hi
        )
        replay, replay_count = parse(
            ROOT / "scripts" / f"surface_scaled_bulk_{label}_rerun.txt", lo, hi
        )
        assert production == replay and count == replay_count
        total_rows += count
    print("CWIN3P2 MID COVER VALIDATION PASS", "units", 83,
          "t_rows", total_rows)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
