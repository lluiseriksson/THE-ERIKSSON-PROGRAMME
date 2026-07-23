"""Validate production/replay for the isolated [765/16,193/4] unit."""
from pathlib import Path
import hashlib
import re
from fractions import Fraction

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "scripts" / "surface_scaled_bulk_mid_cover_00_765_16_193_4"


def main() -> int:
    production = BASE.with_suffix(".txt").read_bytes()
    replay = BASE.with_name(BASE.name + "_rerun").with_suffix(".txt").read_bytes()
    assert production == replay
    text = production.decode().replace("\r\n", "\n")
    assert text.startswith("SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER\n")
    assert "config CWIN 3/2 beta_order 20 t_order 25 min_dt 1/100000 prec 180" in text
    beta = re.search(r"^beta_domain (\S+) (\S+)$", text, re.M)
    assert beta and tuple(map(Fraction, beta.groups())) == (Fraction(765, 16), Fraction(193, 4))
    rows = re.findall(r"^trow \d+ (\S+) (\S+) upper (.+)$", text, re.M)
    count = int(re.search(r"^t_rows (\d+)$", text, re.M).group(1))
    assert count == len(rows) and count > 0
    assert all(upper.startswith("[-") or upper.startswith("-") for _, _, upper in rows)
    assert "SCOPE quarantined" in text
    print("MID GAP [765/16,193/4] VALIDATION PASS")
    print("ROWS", count, "SHA256", hashlib.sha256(production).hexdigest())
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("QUARANTINED; NO G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
