"""Validate the production/replay transcript for order-24 unit 57."""
from pathlib import Path
import hashlib
import re

ROOT = Path(__file__).resolve().parents[1]
BASES = [
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_57_125_2_251_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_58_251_4_63",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_59_63_253_4",
]

def main() -> int:
    total = 0
    for base in BASES:
        prod = base.with_suffix(".txt")
        replay = base.with_name(base.name + "_rerun").with_suffix(".txt")
        a, b = prod.read_bytes(), replay.read_bytes()
        assert a == b
        text = a.decode().replace("\r\n", "\n")
        assert text.startswith("SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER24 REPAIR\n")
        assert "config CWIN 3/2 beta_order 24 t_order 25 min_dt 1/100000 prec 180" in text
        rows = int(re.search(r"^t_rows (\d+)$", text, re.M).group(1))
        assert rows == len(re.findall(r"^trow ", text, re.M))
        total += rows
    print("ORDER24 REPAIR VALIDATION PASS")
    print("UNITS 57-59 ROWS", total)
    for base in BASES:
        print("SHA256", base.name, hashlib.sha256(base.with_suffix(".txt").read_bytes()).hexdigest())
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("QUARANTINED; NO G2/G6 PROMOTION")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
