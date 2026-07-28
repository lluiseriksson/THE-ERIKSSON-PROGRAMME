"""Validate production/replay equality for the order-22 repair transcript."""
from __future__ import annotations
import hashlib
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BASES = [
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_32_225_4_113_2",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_33_113_2_227_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_34_227_4_57",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_35_57_229_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_36_229_4_115_2",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_37_115_2_231_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_38_231_4_58",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_39_58_233_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_40_233_4_117_2",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_41_117_2_235_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_42_235_4_59",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_43_59_237_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_44_237_4_119_2",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_45_119_2_239_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_46_239_4_60",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_47_60_241_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_48_241_4_121_2",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_49_121_2_243_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_50_243_4_61",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_51_61_245_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_52_245_4_123_2",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_53_123_2_247_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_54_247_4_62",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_55_62_249_4",
    ROOT / "scripts" / "surface_scaled_bulk_mid_cover_56_249_4_125_2",
]

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> int:
    total = 0
    for base in BASES:
        prod, replay = base.with_suffix(".txt"), base.with_name(base.name + "_rerun").with_suffix(".txt")
        a, b = prod.read_bytes(), replay.read_bytes()
        assert a == b, f"production/replay byte mismatch: {base.name}"
        text = a.decode("utf-8").replace("\r\n", "\n")
        assert text.startswith("SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER22 REPAIR\n")
        assert "config CWIN 3/2 beta_order 22 t_order 25 min_dt 1/100000 prec 180" in text
        rows = int(re.search(r"^t_rows (\d+)$", text, re.M).group(1))
        assert rows == len(re.findall(r"^trow ", text, re.M))
        total += rows
    print("ORDER22 REPAIR VALIDATION PASS")
    print("UNITS 32-56 ROWS", total)
    for i, base in enumerate(BASES, start=32):
        print(f"SHA256_{i}", sha(base.with_suffix(".txt")))
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("QUARANTINED; NO G2/G6 PROMOTION")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
