"""Candidate-only local micro-rescue for the post-1635/16 G2 obstruction."""

from fractions import Fraction
import hashlib
import platform
import subprocess
from pathlib import Path

import flint
from flint import ctx
import certify_bulk_beta_taylor_scaled_design as scaled
import certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high as high

ROOT = Path(__file__).resolve().parents[1]
BETA_LO = Fraction(1635, 16)
BETA_HI = Fraction(3271, 32)
T_LO = Fraction(3123099, 1_000_000)
T_HI = Fraction(31231, 10_000)
PREC = 180
MIN_DT = Fraction(1, 100_000_000)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run() -> str:
    ctx.prec = PREC
    high.install_cached_backend()
    high.MIN_DT = MIN_DT
    scaled.bulk.CWIN = Fraction(3, 2)
    box = scaled.bulk.BetaTaylorBox(BETA_LO, BETA_HI, prec=PREC,
                                    order=30, t_order=37)
    rows = high.cover_rows(box, T_LO, T_HI)
    if not rows or rows[0][0] != T_LO or rows[-1][1] != T_HI:
        raise RuntimeError("micro-rescue rows are not contiguous")
    if any(upper >= 0 for _, _, upper in rows):
        raise RuntimeError("micro-rescue contains a nonnegative row")
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "rev-parse", "HEAD"],
        cwd=ROOT, text=True).strip()
    lines = [
        "SCALED BULK G2 POST1635 MICRO RESCUE",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}", f"git_head {head}",
        "config CWIN 3/2 beta_order 30 t_order 37 min_dt 1/100000000 prec 180",
        f"beta_domain {BETA_LO} {BETA_HI}",
        f"t_domain {T_LO} {T_HI}",
    ]
    for relative in (
        "scripts/probe_surface_g2_post1635_micro_rescue.py",
        "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py",
        "docs/SURFACE-G2-POST1635-MICRO-RESCUE-PREREG-20260725.md",
    ):
        lines.append(f"dependency {relative} sha256 {sha256(ROOT / relative)}")
    for index, (x1, x2, upper) in enumerate(rows):
        lines.append(f"trow {index} {x1} {x2} upper {upper.str(80)}")
    lines += [f"t_rows {len(rows)}", "G2 POST1635 MICRO RESCUE PASS",
              "SCOPE candidate-only local row rescue; no G2/G6 promotion"]
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    print(run(), end="")

