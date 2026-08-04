"""Candidate high-order sign-row driver for one CWIN=3/2 beta unit."""

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
ORDER = 30
T_ORDER = 37
PREC = 180
MIN_DT = Fraction(1, 100_000)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def install_cached_backend():
    original = scaled.scaled_bessel_value

    @lru_cache(maxsize=None)
    def cached(mode, beta):
        return original(mode, beta)

    scaled.scaled_bessel_value = cached
    scaled.install_design_backend()
    scaled.bulk.CWIN = CWIN
    return cached


def cover_rows(box, t_lo, t_hi):
    stack = [(t_lo, t_hi)]
    rows = []
    while stack:
        x1, x2 = stack.pop()
        upper = box.W(x1, x2).upper()
        if upper < 0:
            rows.append((x1, x2, upper))
            continue
        if x2 - x1 <= MIN_DT:
            raise RuntimeError(f"bulk failure near t={float(x1)}")
        mid = (x1 + x2) / 2
        stack.extend(((mid, x2), (x1, mid)))
    return sorted(rows, key=lambda row: row[0])


def run(unit, lo, hi):
    ctx.prec = PREC
    cache = install_cached_backend()
    box = scaled.bulk.BetaTaylorBox(lo, hi, prec=PREC,
                                    order=ORDER, t_order=T_ORDER)
    t_hi = scaled.bulk.PI_UP - CWIN / hi
    rows = cover_rows(box, Fraction(3, 5), t_hi)
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    lines = [
        "SCALED BULK SIGN ROW UNIT CWIN3P2 HIGH",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}",
        f"git_head {head}",
        f"unit {unit}",
        f"config CWIN {CWIN} beta_order {ORDER} t_order {T_ORDER} min_dt {MIN_DT} prec {PREC}",
        f"beta_domain {lo} {hi}",
        f"t_domain {Fraction(3,5)} {t_hi}",
        f"cache_entries {cache.cache_info().currsize}",
    ]
    for relative in (
        "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py",
    ):
        lines.append(f"dependency {relative} sha256 {sha256(ROOT / relative)}")
    for index, (x1, x2, upper) in enumerate(rows):
        lines.append(f"trow {index} {x1} {x2} upper {upper.str(80)}")
    lines.append(f"t_rows {len(rows)}")
    lines.append("SCALED BULK SIGN ROW PASS")
    lines.append("SCOPE candidate high-order CWIN=3/2 unit only; no G2/G6 promotion")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    print(run(args.unit, Fraction(args.lo), Fraction(args.hi)), end="")
