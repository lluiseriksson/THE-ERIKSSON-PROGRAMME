"""Audit the geometric chain of the quarantined order-22 sign rows.

This checker validates beta/t adjacency and row sign fields only.  It is
deliberately unable to promote G2, G6, or H_tail: those require separate
analytic relay and tail lemmas.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
LABELS = [
    (32, "225_4_113_2"), (33, "113_2_227_4"), (34, "227_4_57"),
    (35, "57_229_4"), (36, "229_4_115_2"), (37, "115_2_231_4"),
    (38, "231_4_58"), (39, "58_233_4"), (40, "233_4_117_2"),
    (41, "117_2_235_4"), (42, "235_4_59"),
    (43, "59_237_4"), (44, "237_4_119_2"),
    (45, "119_2_239_4"), (46, "239_4_60"),
    (47, "60_241_4"), (48, "241_4_121_2"),
    (49, "121_2_243_4"), (50, "243_4_61"),
    (51, "61_245_4"), (52, "245_4_123_2"),
    (53, "123_2_247_4"), (54, "247_4_62"),
    (55, "62_249_4"), (56, "249_4_125_2"),
]

def parse_fraction(value: str) -> Fraction:
    return Fraction(value)

def main() -> int:
    expected_beta = Fraction(225, 4)
    total = 0
    for index, label in LABELS:
        path = ROOT / "scripts" / f"surface_scaled_bulk_mid_cover_{index:02d}_{label}.txt"
        text = path.read_text(encoding="utf-8").replace("\r\n", "\n")
        assert "ORDER22 REPAIR" in text and "SCOPE quarantined" in text
        beta = re.search(r"^beta_domain (\S+) (\S+)$", text, re.M)
        assert beta, path
        lo, hi = map(parse_fraction, beta.groups())
        assert lo == expected_beta, (index, lo, expected_beta)
        expected_beta = hi
        td = re.search(r"^t_domain (\S+) (\S+)$", text, re.M)
        assert td, path
        t_lo, t_hi = map(parse_fraction, td.groups())
        rows = []
        for m in re.finditer(r"^trow \d+ (\S+) (\S+) upper (.+)$", text, re.M):
            x1, x2, upper = m.groups()
            rows.append((parse_fraction(x1), parse_fraction(x2), upper))
            assert x1 != x2 and parse_fraction(x1) < parse_fraction(x2)
            assert upper.startswith("[-") or upper.startswith("-")
        n = int(re.search(r"^t_rows (\d+)$", text, re.M).group(1))
        assert n == len(rows) and rows[0][0] == t_lo and rows[-1][1] == t_hi
        for prev, cur in zip(rows, rows[1:]):
            assert prev[1] == cur[0], (index, prev, cur)
        total += n
    assert expected_beta == Fraction(125, 2)
    print("ORDER22 CHAIN GEOMETRY AUDIT PASS")
    print("UNITS", len(LABELS), "ROWS", total)
    print("BETA ADJACENCY PASS")
    print("T ADJACENCY PASS")
    print("SIGN-ROW FIELDS PASS")
    print("NO H_TAIL/G2/G6 PROMOTION")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
