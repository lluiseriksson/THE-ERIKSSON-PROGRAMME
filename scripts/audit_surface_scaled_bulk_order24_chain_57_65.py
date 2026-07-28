"""Audit the quarantined order-24 repair chain through unit 65.

This is a geometric/provenance audit only.  It deliberately cannot promote
the analytic tail, G2, or G6.
"""
from fractions import Fraction
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
LABELS = [
    (57, "125_2_251_4"), (58, "251_4_63"), (59, "63_253_4"),
    (60, "253_4_127_2"), (61, "127_2_255_4"),
    (62, "255_4_64"), (63, "64_257_4"),
    (64, "257_4_129_2"), (65, "129_2_259_4"),
]


def main() -> int:
    expected_beta = Fraction(125, 2)
    total = 0
    for index, label in LABELS:
        path = ROOT / "scripts" / f"surface_scaled_bulk_mid_cover_{index}_{label}.txt"
        text = path.read_text(encoding="utf-8").replace("\r\n", "\n")
        assert text.startswith("SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER24 REPAIR\n")
        assert "SCOPE quarantined" in text
        beta = re.search(r"^beta_domain (\S+) (\S+)$", text, re.M)
        assert beta, path
        lo, hi = map(Fraction, beta.groups())
        assert lo == expected_beta, (index, lo, expected_beta)
        expected_beta = hi
        td = re.search(r"^t_domain (\S+) (\S+)$", text, re.M)
        assert td, path
        t_lo, t_hi = map(Fraction, td.groups())
        rows = []
        for m in re.finditer(r"^trow \d+ (\S+) (\S+) upper (.+)$", text, re.M):
            x1, x2, upper = m.groups()
            rows.append((Fraction(x1), Fraction(x2)))
            assert Fraction(x1) < Fraction(x2)
            assert upper.startswith("[-") or upper.startswith("-")
        n = int(re.search(r"^t_rows (\d+)$", text, re.M).group(1))
        assert n == len(rows) and rows[0][0] == t_lo and rows[-1][1] == t_hi
        for prev, cur in zip(rows, rows[1:]):
            assert prev[1] == cur[0], (index, prev, cur)
        total += n
    assert expected_beta == Fraction(259, 4)
    print("ORDER24 CHAIN 57-65 GEOMETRY AUDIT PASS")
    print("UNITS", len(LABELS), "ROWS", total)
    print("BETA ADJACENCY PASS")
    print("T ADJACENCY PASS")
    print("SIGN-ROW FIELDS PASS")
    print("NO H_TAIL/G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
