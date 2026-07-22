"""Independent validator for the preregistered mid-order unit pair."""

from fractions import Fraction
import hashlib
from pathlib import Path

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
UNIT = "gap_765_16_193_4"
LO, HI = Fraction(765, 16), Fraction(193, 4)
DEPS = (
    "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_mid.py",
    "scripts/run_surface_scaled_bulk_cwin3p2_mid_unit.py",
    "scripts/certify_bulk_beta_taylor_scaled_design.py",
    "scripts/certify_bulk_beta_taylor_arb.py",
    "docs/SURFACE-G2-CWIN3P2-MID-PREREG-20260722.md",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path: Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED BULK SIGN ROW UNIT CWIN3P2 MID"
    assert f"unit {UNIT}" in lines
    assert "SCALED BULK SIGN ROW PASS" in lines
    assert "SCOPE candidate mid-order unit only; no G2/G6 promotion" in lines
    config = next(line for line in lines if line.startswith("config "))
    assert "CWIN 3/2" in config and "beta_order 20" in config
    assert "t_order 25" in config and "min_dt 1/100000" in config
    beta = next(line for line in lines if line.startswith("beta_domain ")).split()
    assert Fraction(beta[1]) == LO and Fraction(beta[2]) == HI
    deps = {
        line.split()[1]: line.split()[3]
        for line in lines if line.startswith("dependency ")
    }
    assert deps == {relative: sha256(ROOT / relative) for relative in DEPS}
    domain = next(line for line in lines if line.startswith("t_domain ")).split()
    cursor = Fraction(domain[1])
    rows = []
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
    return lines, len(rows)


def main() -> int:
    production, count = parse(ROOT / "scripts" / f"surface_scaled_bulk_{UNIT}.txt")
    replay, replay_count = parse(
        ROOT / "scripts" / f"surface_scaled_bulk_{UNIT}_rerun.txt"
    )
    assert production == replay and count == replay_count
    print("CWIN3P2 MID VALIDATION PASS", UNIT, "t_rows", count)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
