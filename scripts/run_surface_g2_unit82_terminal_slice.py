"""Fresh terminal-contract runner for final beta-gap slices 2 and 3."""

from __future__ import annotations

import argparse
import hashlib
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

from flint import ctx

import run_surface_scaled_bulk_cwin3p2_unit82_rescue_order30_slice as base

ROOT = Path(__file__).resolve().parents[1]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--beta-lo", required=True)
    parser.add_argument("--beta-hi", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    lo, hi = Fraction(args.beta_lo), Fraction(args.beta_hi)
    ctx.prec = base.PREC
    base.install()
    box = base.scaled.bulk.BetaTaylorBox(
        lo, hi, prec=base.PREC, order=base.ORDER, t_order=base.T_ORDER
    )
    rows = base.cover_rows(box, hi)
    head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT, text=True,
    ).strip()
    label = "slice2" if lo == Fraction(1101, 16) else "slice3"
    lines = [
        "SCALED BULK SIGN ROW UNIT82 TERMINAL ORDER30 SLICE",
        f"python {sys.version.split()[0]}",
        f"python_flint {__import__('flint').__version__}",
        f"arb_bits {ctx.prec}", f"git_head {head}", f"unit {label}",
        (f"config CWIN {base.CWIN} beta_order {base.ORDER} "
         f"t_order {base.T_ORDER} min_dt {base.MIN_DT} prec {base.PREC}"),
        f"beta_domain {lo} {hi}",
        f"t_domain {Fraction(3,5)} {base.scaled.bulk.PI_UP - base.CWIN / hi}",
    ]
    for relative in (
        "scripts/run_surface_g2_unit82_terminal_slice.py",
        "scripts/run_surface_scaled_bulk_cwin3p2_unit82_rescue_order30_slice.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py",
    ):
        lines.append(f"dependency {relative} sha256 {sha(ROOT / relative)}")
    lines.extend(
        f"trow {i} {x1} {x2} upper {upper.str(80)}"
        for i, (x1, x2, upper) in enumerate(rows)
    )
    lines.extend([
        f"t_rows {len(rows)}",
        "SCALED BULK SIGN ROW PASS",
        f"SCOPE terminal direct-sign unit82 {label}; no H_tail promotion",
    ])
    (ROOT / args.output).write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("TERMINAL SLICE PASS", label, lo, hi, "rows", len(rows))


if __name__ == "__main__":
    main()
