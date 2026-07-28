"""Generic isolated mid-order CWIN=3/2 sign-row candidate evaluator."""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
import hashlib
import platform
import subprocess
from pathlib import Path

import flint
from flint import ctx
import certify_bulk_beta_taylor_scaled_design as scaled

ROOT = Path(__file__).resolve().parents[1]
CWIN = Fraction(3, 2)
ORDER, T_ORDER, PREC = 20, 25, 180
MIN_DT = Fraction(1, 100_000)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(lo: Fraction, hi: Fraction, unit: str, order: int = 20, t_order: int = 25) -> str:
    if not lo < hi:
        raise ValueError("invalid beta interval")
    ctx.prec = PREC
    original = scaled.scaled_bessel_value

    @lru_cache(maxsize=None)
    def cached(mode, beta):
        return original(mode, beta)

    scaled.scaled_bessel_value = cached
    scaled.install_design_backend()
    scaled.bulk.CWIN = CWIN
    box = scaled.bulk.BetaTaylorBox(lo, hi, prec=PREC, order=order, t_order=t_order)
    t_lo = Fraction(3, 5)
    t_hi = scaled.bulk.PI_UP - CWIN / hi
    stack, rows = [(t_lo, t_hi)], []
    while stack:
        x1, x2 = stack.pop()
        upper = box.W(x1, x2).upper()
        if upper < 0:
            rows.append((x1, x2, upper))
            continue
        if x2 - x1 <= MIN_DT:
            raise RuntimeError(f"mid-order bulk failure near t={float(x1)}")
        mid = (x1 + x2) / 2
        stack.extend(((mid, x2), (x1, mid)))
    rows.sort(key=lambda row: row[0])
    head = subprocess.check_output(["git", "-c", "safe.directory=*", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    lines = [
        "SCALED BULK SIGN ROW UNIT CWIN3P2 MID GENERIC",
        f"python {platform.python_version()}", f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}", f"git_head {head}", f"unit {unit}",
        f"config CWIN {CWIN} beta_order {order} t_order {t_order} min_dt {MIN_DT} prec {PREC}",
        f"beta_domain {lo} {hi}", f"t_domain {t_lo} {t_hi}",
        f"cache_entries {cached.cache_info().currsize}",
    ]
    for relative in (
        "scripts/certify_surface_scaled_bulk_cwin3p2_mid_generic.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py",
        "docs/SURFACE-G2-CWIN3P2-MID-PREREG-20260722.md",
    ):
        lines.append(f"dependency {relative} sha256 {sha256(ROOT / relative)}")
    lines.extend(f"trow {i} {x1} {x2} upper {upper.str(80)}" for i, (x1, x2, upper) in enumerate(rows))
    lines.extend([f"t_rows {len(rows)}", "SCALED BULK SIGN ROW PASS", "SCOPE candidate mid-order generic unit only; no G2/G6 promotion"])
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    parser.add_argument("--unit", required=True)
    parser.add_argument("--order", type=int, default=20)
    parser.add_argument("--t-order", type=int, default=25)
    args = parser.parse_args()
    print(run(Fraction(args.lo), Fraction(args.hi), args.unit, args.order, args.t_order), end="")
