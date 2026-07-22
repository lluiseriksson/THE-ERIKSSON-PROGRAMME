"""Candidate-only mid-order CWIN=3/2 sign-row evaluator.

This is a frozen replacement lane for the preregistered unit
[765/16,193/4].  It uses the same scaled Bessel derivative-tail contract as
the high-order driver, with beta/t Taylor orders 20/25.  It emits no theorem
claim and is intentionally separate from the historical high-order script.
"""

from __future__ import annotations

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
ORDER = 20
T_ORDER = 25
PREC = 180
MIN_DT = Fraction(1, 100_000)
BETA_LO = Fraction(765, 16)
BETA_HI = Fraction(193, 4)


def sha256(path: Path) -> str:
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


def cover_rows(box, t_lo: Fraction, t_hi: Fraction):
    stack = [(t_lo, t_hi)]
    rows = []
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
    return sorted(rows, key=lambda row: row[0])


def run() -> str:
    if not BETA_LO < BETA_HI:
        raise ValueError("invalid registered beta interval")
    ctx.prec = PREC
    cache = install_cached_backend()
    box = scaled.bulk.BetaTaylorBox(
        BETA_LO, BETA_HI, prec=PREC, order=ORDER, t_order=T_ORDER
    )
    t_lo = Fraction(3, 5)
    t_hi = scaled.bulk.PI_UP - CWIN / BETA_HI
    rows = cover_rows(box, t_lo, t_hi)
    head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT, text=True,
    ).strip()
    lines = [
        "SCALED BULK SIGN ROW UNIT CWIN3P2 MID",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}",
        f"git_head {head}",
        "unit gap_765_16_193_4",
        (f"config CWIN {CWIN} beta_order {ORDER} t_order {T_ORDER} "
         f"min_dt {MIN_DT} prec {PREC}"),
        f"beta_domain {BETA_LO} {BETA_HI}",
        f"t_domain {t_lo} {t_hi}",
        f"cache_entries {cache.cache_info().currsize}",
    ]
    for relative in (
        "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_mid.py",
        "scripts/run_surface_scaled_bulk_cwin3p2_mid_unit.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py",
        "docs/SURFACE-G2-CWIN3P2-MID-PREREG-20260722.md",
    ):
        lines.append(f"dependency {relative} sha256 {sha256(ROOT / relative)}")
    for index, (x1, x2, upper) in enumerate(rows):
        lines.append(f"trow {index} {x1} {x2} upper {upper.str(80)}")
    lines.extend([
        f"t_rows {len(rows)}",
        "SCALED BULK SIGN ROW PASS",
        "SCOPE candidate mid-order unit only; no G2/G6 promotion",
    ])
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    print(run(), end="")
