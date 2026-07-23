"""Record one pre-registered sine-normalized stress box."""

from fractions import Fraction
import argparse
import hashlib
import platform
import subprocess
from pathlib import Path

import flint
from flint import ctx

import certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high as high
from probe_surface_scaled_bulk_sin_normalized_stress import SinNormalizedBox
from certify_surface_scaled_bulk_common_scale_design import install

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run():
    lo, hi = Fraction(3258, 32), Fraction(3259, 32)
    t_lo, t_hi = Fraction(31268, 10000), Fraction(312686, 100000)
    ctx.prec = 220
    install()
    high.ORDER, high.T_ORDER, high.PREC = 40, 45, 220
    high.CWIN = Fraction(3, 2)
    high.install_cached_backend()
    high.scaled.bulk.BetaTaylorBox = SinNormalizedBox
    box = SinNormalizedBox(lo, hi, prec=220, order=40, t_order=45)
    value = box.W(t_lo, t_hi)
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    lines = [
        "SIN-NORMALIZED STRESS TRANSCRIPT",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}",
        f"git_head {head}",
        "config CWIN 3/2 beta_order 40 t_order 45 prec 220 common_scale J1^4 t_scale sin(t)",
        f"beta_domain {lo} {hi}",
        f"t_domain {t_lo} {t_hi}",
        f"W_upper {value.upper().str(100)}",
        f"W_lower {value.lower().str(100)}",
    ]
    for relative in (
        "scripts/record_surface_scaled_bulk_sin_normalized_stress.py",
        "scripts/probe_surface_scaled_bulk_sin_normalized_stress.py",
        "scripts/certify_surface_scaled_bulk_common_scale_design.py",
        "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py",
    ):
        lines.append(f"dependency {relative} sha256 {digest(ROOT / relative)}")
    lines.extend([
        "STRICT_UPPER_NEGATIVE PASS" if value.upper() < 0 else "STRICT_UPPER_NEGATIVE FAIL",
        "SCOPE candidate single stress box only; no G2/G6 promotion",
    ])
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = (ROOT / args.output).resolve()
    out.relative_to(ROOT)
    out.write_text(run(), encoding="utf-8")
    print("SIN-NORMALIZED STRESS RECORD PASS", out.relative_to(ROOT))


if __name__ == "__main__":
    main()
