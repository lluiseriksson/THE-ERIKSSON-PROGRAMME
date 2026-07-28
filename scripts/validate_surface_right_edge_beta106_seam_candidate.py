"""Audit the arithmetic seam between the terminal G5 bridge and beta106 candidate.

This is a coverage audit only.  It deliberately does not write a G2 manifest:
the interior bulk sign and the analytic sign-to-H_tail relay remain separate
obligations.
"""

from fractions import Fraction
from pathlib import Path
import json

from validate_surface_right_edge_five_family_beta106_lambda2 import (
    RANGES, parse,
)

ROOT = Path(__file__).resolve().parents[1]
FINITE_DELTAS = (
    (Fraction(1, 125), Fraction(7, 500)),
    (Fraction(7, 500), Fraction(1, 50)),
    (Fraction(1, 50), Fraction(1, 40)),
    (Fraction(1, 40), Fraction(3, 100)),
    (Fraction(3, 100), Fraction(1, 30)),
)


def main() -> int:
    beta_lo, beta_hi = Fraction(3409, 32), Fraction(1000, 9)
    delta_lo, delta_hi = 1 / beta_hi, 1 / beta_lo
    assert delta_lo == Fraction(9, 1000)
    assert delta_hi == Fraction(32, 3409)
    # The exact beta frontier is contained in the first terminal finite-G5
    # delta band, so its lambda<=3/2 rows are already covered there.
    assert FINITE_DELTAS[0][0] <= delta_lo < delta_hi <= FINITE_DELTAS[0][1]
    assert delta_hi < FINITE_DELTAS[1][0]

    finite = set()
    for path in sorted((ROOT / "scripts").glob(
            "certify_surface_right_edge_five_family_finite_lambda_*_transcript.txt")):
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.startswith("ROW "):
                row = json.loads(line[4:])
                if row["delta_index"] == 0:
                    finite.add(int(row["lambda_index"]))
    assert len(finite) == 75  # first delta band, all lambda cells
    assert finite == set(range(75))

    candidate = []
    for start, stop in RANGES:
        path = ROOT / "scripts" / (
            f"surface_right_edge_five_family_beta106_lambda2_{start}_{stop}.txt")
        candidate.extend(parse(path, start, stop))
    assert [row[0] for row in candidate] == list(range(75, 100))
    assert candidate[0][1] == Fraction(3, 2)
    assert candidate[-1][2] == Fraction(2)
    assert finite and max(finite) == 74
    print("BETA106 G5 SEAM ARITHMETIC PASS lambda 0..2")
    print("DELTA FRONTIER", delta_lo, delta_hi, "inside terminal band 0")
    print("CANDIDATE ONLY; NO G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
