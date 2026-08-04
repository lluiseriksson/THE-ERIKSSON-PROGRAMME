"""Validate order-24 extension-3 production/replay."""
from pathlib import Path
import hashlib
import re

ROOT = Path(__file__).resolve().parents[1]
BASES = [
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_62_255_4_64",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_63_64_257_4",
]

def main() -> int:
    total = 0
    for base in BASES:
        a = base.with_suffix(".txt").read_bytes()
        b = base.with_name(base.name + "_rerun").with_suffix(".txt").read_bytes()
        assert a == b
        text = a.decode().replace("\r\n", "\n")
        assert text.startswith("SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER24 REPAIR\n")
        assert "config CWIN 3/2 beta_order 24 t_order 25 min_dt 1/100000 prec 180" in text
        n = int(re.search(r"^t_rows (\d+)$", text, re.M).group(1))
        assert n == len(re.findall(r"^trow ", text, re.M))
        total += n
        print(base.name, "ROWS", n, "SHA256", hashlib.sha256(a).hexdigest())
    print("ORDER24 EXTENSION3 VALIDATION PASS", "UNITS", len(BASES), "ROWS", total)
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("QUARANTINED; NO G2/G6 PROMOTION")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
