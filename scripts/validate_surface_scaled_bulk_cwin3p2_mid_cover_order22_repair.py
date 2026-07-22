"""Validate production/replay equality for the order-22 repair transcript."""
from __future__ import annotations
import hashlib
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "scripts" / "surface_scaled_bulk_mid_cover_32_225_4_113_2"

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> int:
    prod, replay = BASE.with_suffix(".txt"), BASE.with_name(BASE.name + "_rerun").with_suffix(".txt")
    a, b = prod.read_bytes(), replay.read_bytes()
    assert a == b, "production/replay byte mismatch"
    text = a.decode("utf-8").replace("\r\n", "\n")
    assert text.startswith("SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER22 REPAIR\n")
    assert "config CWIN 3/2 beta_order 22 t_order 25 min_dt 1/100000 prec 180" in text
    rows = int(re.search(r"^t_rows (\d+)$", text, re.M).group(1))
    assert rows == len(re.findall(r"^trow ", text, re.M)) == 168
    print("ORDER22 REPAIR VALIDATION PASS")
    print("UNIT 32 ROWS", rows)
    print("SHA256", sha(prod))
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("QUARANTINED; NO G2/G6 PROMOTION")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
