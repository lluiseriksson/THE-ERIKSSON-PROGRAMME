"""Worker for one quarantined order-30 unit-82 rescue beta slice."""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
import argparse
import hashlib
from pathlib import Path
import subprocess
import sys

from flint import ctx
import certify_bulk_beta_taylor_scaled_design as scaled

ROOT = Path(__file__).resolve().parents[1]
ORDER, T_ORDER, PREC = 30, 35, 220
MIN_DT, CWIN = Fraction(1, 100_000), Fraction(3, 2)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def install() -> None:
    original = scaled.scaled_bessel_value

    @lru_cache(maxsize=None)
    def cached(mode, beta):
        return original(mode, beta)

    scaled.scaled_bessel_value = cached
    scaled.install_design_backend()
    scaled.bulk.CWIN = CWIN


def cover_rows(box, beta_hi):
    stack = [(Fraction(3, 5), scaled.bulk.PI_UP - CWIN / beta_hi)]
    rows = []
    while stack:
        x1, x2 = stack.pop()
        upper = box.W(x1, x2).upper()
        if upper < 0:
            rows.append((x1, x2, upper))
            continue
        if x2 - x1 <= MIN_DT:
            raise RuntimeError(f"rescue failure near t={float(x1)}")
        mid = (x1 + x2) / 2
        stack.extend(((mid, x2), (x1, mid)))
    return sorted(rows, key=lambda row: row[0])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--beta-lo", required=True)
    parser.add_argument("--beta-hi", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    lo, hi = Fraction(args.beta_lo), Fraction(args.beta_hi)
    ctx.prec = PREC
    install()
    box = scaled.bulk.BetaTaylorBox(lo, hi, prec=PREC, order=ORDER,
                                    t_order=T_ORDER)
    rows = cover_rows(box, hi)
    head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT, text=True).strip()
    lines = [
        "SCALED BULK SIGN ROW UNIT82 RESCUE ORDER30 SLICE",
        f"python {sys.version.split()[0]}",
        f"python_flint {__import__('flint').__version__}",
        f"arb_bits {ctx.prec}", f"git_head {head}",
        f"config CWIN {CWIN} beta_order {ORDER} t_order {T_ORDER} min_dt {MIN_DT} prec {PREC}",
        f"beta_domain {lo} {hi}",
        f"t_domain {Fraction(3,5)} {scaled.bulk.PI_UP - CWIN / hi}",
    ]
    for relative in (
        "scripts/run_surface_scaled_bulk_cwin3p2_unit82_rescue_order30_continuation.py",
        "scripts/run_surface_scaled_bulk_cwin3p2_unit82_rescue_order30_slice.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py",
    ):
        lines.append(f"dependency {relative} sha256 {sha(ROOT / relative)}")
    lines.extend(f"trow {i} {x1} {x2} upper {upper.str(80)}"
                 for i, (x1, x2, upper) in enumerate(rows))
    lines.extend([f"t_rows {len(rows)}", "SCALED BULK SIGN ROW PASS",
                  "SCOPE quarantined unit82 rescue continuation; no G2/G6 promotion"])
    (ROOT / args.output).write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("SLICE PASS", lo, hi, "rows", len(rows))


if __name__ == "__main__":
    main()
