"""Independent validator for the beta-frontier lambda-2 candidate pair."""

from __future__ import annotations

import hashlib
import re
from fractions import Fraction
from pathlib import Path

from flint import arb

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "surface_right_edge_five_family_beta106_lambda2_"
RANGES = ((75, 80), (80, 85), (85, 90), (90, 95), (95, 100))
DEPENDENCIES = (
    "scripts/surface_right_edge_five_family_beta106_lambda2.py",
    "scripts/surface_right_edge_five_family_central_design.py",
    "scripts/surface_right_edge_five_family_finite_tail_design.py",
    "scripts/surface_right_edge_five_family_beta20_design.py",
    "scripts/surface_right_edge_five_family_tail_design.py",
    "scripts/surface_bessel_integral_remainder.py",
    "scripts/surface_right_edge_scaled_paired_design.py",
    "scripts/surface_remainder_arb_jet2.py",
    "docs/SURFACE-G5-BETA106-LAMBDA2-PREREG-20260726.md",
)
ROW = re.compile(
    r"^ROW lambda_index (\d+) lambda (\S+):(\S+) resolution (\S+) "
    r"B0_lower (.*?) P0_lower (.*?) H_lower (.*)$"
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path: Path, start: int, stop: int):
    text = path.read_text(encoding="utf-8").replace("\r\n", "\n")
    lines = text.splitlines()
    assert lines[0] == "G5 BETA106 LAMBDA2 CANDIDATE"
    assert "delta_domain 9/1000 32/3409" in lines
    assert f"lambda_domain {start}/50 {stop}/50" in lines
    assert any(line.startswith("config lambda_max 2 near_exp exp(2)")
               for line in lines)
    assert "G5 BETA106 LAMBDA2 CANDIDATE PASS" in lines
    assert "SCOPE candidate only; no G2/G6 promotion" in lines
    dependencies = {
        line.split(" sha256 ", 1)[0].split("dependency ", 1)[1]:
        line.split(" sha256 ", 1)[1]
        for line in lines if line.startswith("dependency ")
    }
    assert dependencies == {name: digest(ROOT / name) for name in DEPENDENCIES}
    rows = []
    for line in lines:
        match = ROW.match(line)
        if match:
            index, lo, hi, resolution, b, p0, h = match.groups()
            assert resolution in {"coarse", "mixed"}
            assert arb(b).lower() > 0
            assert arb(p0).lower() > 0
            assert arb(h).lower() > 0
            rows.append((int(index), Fraction(lo), Fraction(hi)))
    assert [row[0] for row in rows] == list(range(start, stop))
    assert [(row[1], row[2]) for row in rows] == [
        (Fraction(i, 50), Fraction(i + 1, 50))
        for i in range(start, stop)
    ]
    assert int(next(line.split()[1] for line in lines if line.startswith("rows "))) == len(rows)
    return rows


def main() -> int:
    # Recheck the frozen geometry contract independently of the producer.
    # The finite-tail chart requires delta<1/20 and eta_max=delta*lambda/2
    # below both 1/100 and the chart's angular-shift allowance 3/80.
    delta_hi = Fraction(32, 3409)
    lambda_hi = Fraction(2)
    assert Fraction(9, 1000) < delta_hi < Fraction(1, 20)
    eta_max = delta_hi * lambda_hi / 2
    assert eta_max < Fraction(1, 100)
    assert eta_max < Fraction(3, 80)
    all_rows = []
    for start, stop in RANGES:
        production = ROOT / "scripts" / f"{PREFIX}{start}_{stop}.txt"
        replay = ROOT / "scripts" / f"{PREFIX}{start}_{stop}_rerun.txt"
        assert production.read_bytes() == replay.read_bytes()
        rows = parse(production, start, stop)
        assert parse(replay, start, stop) == rows
        all_rows.extend(rows)
    assert len(all_rows) == 25
    assert all_rows[0][1] == Fraction(3, 2)
    assert all_rows[-1][2] == Fraction(2)
    assert all(a[2] == b[1] for a, b in zip(all_rows, all_rows[1:]))
    print("G5 BETA106 LAMBDA2 VALIDATION PASS rows", len(all_rows))
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("GEOMETRY AND EXP(2) LEDGER HEADERS PASS")
    print("CANDIDATE ONLY; NO G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
