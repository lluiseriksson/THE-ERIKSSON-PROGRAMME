"""Preregistered order-22 repair driver for the mid-order sign cover.

This is deliberately separate from the frozen order-20 driver.  It writes the
same unit labels, but its transcript header and dependency hash identify the
repair contract.  Rows remain quarantined and never promote G2/G6.
"""
from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
import hashlib
from pathlib import Path
import subprocess
import sys

from flint import ctx
import certify_bulk_beta_taylor_scaled_design as scaled

ROOT = Path(__file__).resolve().parents[1]
START = Fraction(193, 4)
END = Fraction(69)
WIDTH = Fraction(1, 4)
ORDER = 22
T_ORDER = 25
PREC = 180
MIN_DT = Fraction(1, 100_000)
CWIN = Fraction(3, 2)
PREREG = "docs/SURFACE-G2-CWIN3P2-MID-COVER-ORDER22-REPAIR-PREREG-20260722.md"

def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def units():
    lo, index = START, 0
    while lo < END:
        hi = min(lo + WIDTH, END)
        yield index, lo, hi
        lo, index = hi, index + 1

def install_cached_backend():
    original = scaled.scaled_bessel_value
    @lru_cache(maxsize=None)
    def cached(mode, beta):
        return original(mode, beta)
    scaled.scaled_bessel_value = cached
    scaled.install_design_backend()
    scaled.bulk.CWIN = CWIN
    return cached

def cover_rows(box, t_lo: Fraction, t_hi: Fraction):
    stack, rows = [(t_lo, t_hi)], []
    while stack:
        x1, x2 = stack.pop()
        upper = box.W(x1, x2).upper()
        if upper < 0:
            rows.append((x1, x2, upper))
            continue
        if x2 - x1 <= MIN_DT:
            raise RuntimeError(f"order22 repair cover failure near t={float(x1)}")
        mid = (x1 + x2) / 2
        stack.extend(((mid, x2), (x1, mid)))
    return sorted(rows, key=lambda row: row[0])

def transcript(index, lo, hi, rows, cache_entries):
    head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT, text=True).strip()
    label = f"mid_cover_{index:02d}_{lo}_{hi}".replace("/", "_")
    t_lo, t_hi = Fraction(3, 5), scaled.bulk.PI_UP - CWIN / hi
    lines = [
        "SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER22 REPAIR",
        f"python {sys.version.split()[0]}",
        f"python_flint {__import__('flint').__version__}",
        f"arb_bits {ctx.prec}", f"git_head {head}", f"unit {label}",
        (f"config CWIN {CWIN} beta_order {ORDER} t_order {T_ORDER} "
         f"min_dt {MIN_DT} prec {PREC}"),
        f"beta_domain {lo} {hi}", f"t_domain {t_lo} {t_hi}",
        f"cache_entries {cache_entries}",
    ]
    for relative in (
        "scripts/run_surface_scaled_bulk_cwin3p2_mid_cover_order22_repair.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py", PREREG,
    ):
        lines.append(f"dependency {relative} sha256 {sha256(ROOT / relative)}")
    for row_index, (x1, x2, upper) in enumerate(rows):
        lines.append(f"trow {row_index} {x1} {x2} upper {upper.str(80)}")
    lines += [f"t_rows {len(rows)}", "SCALED BULK SIGN ROW PASS",
              "SCOPE quarantined order22 repair; no G2/G6 promotion"]
    return label, "\n".join(lines) + "\n"

def main() -> int:
    replay = "--replay" in sys.argv[1:]
    start = int(sys.argv[sys.argv.index("--start") + 1]) if "--start" in sys.argv else 32
    end = int(sys.argv[sys.argv.index("--end") + 1]) if "--end" in sys.argv else 83
    ctx.prec = PREC
    cache = install_cached_backend()
    for index, lo, hi in units():
        if index < start or index >= end:
            continue
        label = f"mid_cover_{index:02d}_{lo}_{hi}".replace("/", "_")
        print("START", label, flush=True)
        box = scaled.bulk.BetaTaylorBox(lo, hi, prec=PREC, order=ORDER, t_order=T_ORDER)
        rows = cover_rows(box, Fraction(3, 5), scaled.bulk.PI_UP - CWIN / hi)
        name, text = transcript(index, lo, hi, rows, cache.cache_info().currsize)
        suffix = "_rerun" if replay else ""
        (ROOT / "scripts" / f"surface_scaled_bulk_{name}{suffix}.txt").write_text(text, encoding="utf-8")
        print("PASS", name, "rows", len(rows), flush=True)
    print("CWIN3P2 MID COVER ORDER22 REPAIR", "REPLAY" if replay else "PRODUCTION", "PASS")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
