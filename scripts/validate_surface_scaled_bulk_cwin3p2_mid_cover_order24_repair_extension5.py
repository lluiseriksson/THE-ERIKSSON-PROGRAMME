"""Validate the order-24 extension-5 production/replay pair."""
from fractions import Fraction
from pathlib import Path
import hashlib
import re

ROOT = Path(__file__).resolve().parents[1]
LABELS = []
lo = Fraction(259, 4)
for index in range(66, 82):
    hi = lo + Fraction(1, 4)
    LABELS.append((index, lo, hi))
    lo = hi


def main() -> int:
    total = 0
    expected = Fraction(259, 4)
    for index, lo, hi in LABELS:
        label = f"{lo}_{hi}".replace("/", "_")
        base = ROOT / "scripts" / f"surface_scaled_bulk_mid_cover_{index}_{label}"
        a = base.with_suffix(".txt").read_bytes()
        b = base.with_name(base.name + "_rerun").with_suffix(".txt").read_bytes()
        assert a == b, base
        text = a.decode().replace("\r\n", "\n")
        assert text.startswith("SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER24 REPAIR EXTENSION5\n")
        assert "config CWIN 3/2 beta_order 24 t_order 25 min_dt 1/100000 prec 180" in text
        deps = dict(re.findall(r"^dependency (\S+) sha256 ([0-9a-f]+)$", text, re.M))
        driver = "scripts/run_surface_scaled_bulk_cwin3p2_mid_cover_order24_repair_extension5.py"
        prereg = "docs/SURFACE-G2-CWIN3P2-MID-COVER-ORDER24-REPAIR-EXTENSION5-PREREG-20260723.md"
        assert deps.get(driver) == hashlib.sha256((ROOT / driver).read_bytes()).hexdigest()
        assert deps.get("scripts/certify_bulk_beta_taylor_arb.py") == hashlib.sha256(
            (ROOT / "scripts/certify_bulk_beta_taylor_arb.py").read_bytes()
        ).hexdigest()
        assert deps.get(prereg) == hashlib.sha256((ROOT / prereg).read_bytes()).hexdigest()
        beta = re.search(r"^beta_domain (\S+) (\S+)$", text, re.M)
        assert beta
        got_lo, got_hi = map(Fraction, beta.groups())
        assert (got_lo, got_hi) == (lo, hi), (index, got_lo, got_hi)
        rows = []
        for match in re.finditer(r"^trow \d+ (\S+) (\S+) upper (.+)$", text, re.M):
            x1, x2, upper = match.groups()
            rows.append((Fraction(x1), Fraction(x2)))
            assert upper.startswith("[-") or upper.startswith("-")
        tdom = re.search(r"^t_domain (\S+) (\S+)$", text, re.M)
        count = int(re.search(r"^t_rows (\d+)$", text, re.M).group(1))
        assert tdom and count == len(rows) and rows
        assert rows[0][0] == Fraction(3, 5)
        assert rows[-1][1] == Fraction(31415927, 10000000) - Fraction(3, 2) / hi
        for prev, cur in zip(rows, rows[1:]):
            assert prev[1] == cur[0]
        total += count
        print(base.name, "ROWS", count, "SHA256", hashlib.sha256(a).hexdigest())
        expected = hi
    assert expected == Fraction(275, 4)
    print("ORDER24 EXTENSION5 PARTIAL VALIDATION PASS", "UNITS", len(LABELS), "ROWS", total)
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("QUARANTINED; NO G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
