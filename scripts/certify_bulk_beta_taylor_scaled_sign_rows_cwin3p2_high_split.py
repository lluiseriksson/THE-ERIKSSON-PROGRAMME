"""Candidate high-order sign-row driver with explicit t partitions.

The split is an engineering workaround for the monolithic recursive cover's
timeout behaviour.  It is deliberately candidate-only: it certifies one
registered beta box and does not assert the global H_tail relay.
"""

from fractions import Fraction
from functools import lru_cache
import hashlib
import platform
import subprocess
from pathlib import Path

import flint
from flint import ctx
import certify_bulk_beta_taylor_scaled_design as scaled
import certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high as high

ROOT = Path(__file__).resolve().parents[1]
CWIN = Fraction(3, 2)
ORDER = 30
T_ORDER = 37
PREC = 180
MIN_DT = Fraction(1, 100_000)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(unit, lo, hi):
    ctx.prec = PREC
    high.install_cached_backend()
    scaled.bulk.CWIN = CWIN
    box = scaled.bulk.BetaTaylorBox(lo, hi, prec=PREC,
                                    order=ORDER, t_order=T_ORDER)
    # The admissibility contract requires the conservative endpoint for the
    # whole beta box.  Since beta -> pi - CWIN/beta is increasing, this is
    # the endpoint at beta_lo, not beta_hi.
    t_hi = scaled.bulk.PI_UP - CWIN / lo
    # These boundaries are part of the transcript contract.  The final
    # boundary is the conservative beta-box endpoint required by the relay
    # audit, so every beta in the box is covered.
    boundaries = [
        (Fraction(3, 5), Fraction(3, 2)),
        (Fraction(3, 2), Fraction(9, 4)),
        (Fraction(9, 4), Fraction(3)),
        (Fraction(3), Fraction(61, 20)),
        (Fraction(61, 20), t_hi),
    ]
    rows = []
    for partition, (t_lo, t_end) in enumerate(boundaries):
        if t_end <= t_lo:
            raise RuntimeError(f"empty partition {partition}: {t_lo} {t_end}")
        local = high.cover_rows(box, t_lo, t_end)
        rows.extend((partition, x1, x2, upper) for x1, x2, upper in local)
    cursor = boundaries[0][0]
    for partition, x1, x2, upper in rows:
        if x1 != cursor or x2 <= x1 or upper >= 0:
            raise RuntimeError("non-contiguous or nonnegative split row")
        cursor = x2
    if cursor != t_hi:
        raise RuntimeError("split rows do not reach moving endpoint")
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    lines = [
        "SCALED BULK SIGN ROW UNIT CWIN3P2 HIGH SPLIT",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}",
        f"git_head {head}",
        f"unit {unit}",
        f"config CWIN {CWIN} beta_order {ORDER} t_order {T_ORDER} min_dt {MIN_DT} prec {PREC}",
        f"beta_domain {lo} {hi}",
        f"t_domain {Fraction(3,5)} {t_hi}",
        f"t_partitions {len(boundaries)}",
    ]
    for partition, (t_lo, t_end) in enumerate(boundaries):
        lines.append(f"t_partition {partition} {t_lo} {t_end}")
    for relative in (
        "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high_split.py",
        "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py",
    ):
        lines.append(f"dependency {relative} sha256 {sha256(ROOT / relative)}")
    for index, (partition, x1, x2, upper) in enumerate(rows):
        lines.append(f"trow {index} partition {partition} {x1} {x2} upper {upper.str(80)}")
    lines.append(f"t_rows {len(rows)}")
    lines.append("SCALED BULK SIGN ROW SPLIT PASS")
    lines.append("SCOPE candidate split high-order CWIN=3/2 unit only; no G2/G6 promotion")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    print(run(args.unit, Fraction(args.lo), Fraction(args.hi)), end="")
