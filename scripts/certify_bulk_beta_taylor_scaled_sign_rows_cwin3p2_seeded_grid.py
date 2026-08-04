"""Seeded-grid variant of the CWIN=3/2 scaled sign-row certificate.

The ordinary dyadic cover can spend its entire budget descending a bad
root box.  This driver first lays down a fixed rational t-grid, then applies
the audited Arb enclosure to each cell.  It is intentionally diagnostic:
the transcript carries a distinct header and cannot be consumed by the
authoritative G2 audit until a dedicated manifest and replay have been
reviewed.
"""

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
CWIN = Fraction(3, 2)
ORDER = 30
T_ORDER = 37
PREC = 180


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cover_seeded(box, t_lo: Fraction, t_hi: Fraction,
                 step: Fraction):
    """Certify a fixed grid, refining only cells that fail."""
    rows = []
    cursor = t_lo
    while cursor < t_hi:
        end = min(cursor + step, t_hi)
        # Reuse the audited recursive routine only below the fixed seed
        # scale; this prevents a broad, cancellation-dominated root from
        # creating an unbounded binary tree.
        local = high.cover_rows(box, cursor, end)
        rows.extend(local)
        cursor = end
    return sorted(rows, key=lambda row: row[0])


def run(unit: str, lo: Fraction, hi: Fraction, step: Fraction) -> str:
    if step <= 0:
        raise ValueError("step must be positive")
    ctx.prec = PREC
    high.install_cached_backend()
    scaled.bulk.CWIN = CWIN
    box = scaled.bulk.BetaTaylorBox(lo, hi, prec=PREC,
                                    order=ORDER, t_order=T_ORDER)
    t_hi = scaled.bulk.PI_UP - CWIN / lo
    boundaries = [
        (Fraction(3, 5), Fraction(3, 2)),
        (Fraction(3, 2), Fraction(9, 4)),
        (Fraction(9, 4), Fraction(3)),
        (Fraction(3), Fraction(61, 20)),
        (Fraction(61, 20), t_hi),
    ]
    rows = []
    for partition, (a, b) in enumerate(boundaries):
        for x1, x2, upper in cover_seeded(box, a, b, step):
            rows.append((partition, x1, x2, upper))
    cursor = boundaries[0][0]
    for partition, x1, x2, upper in rows:
        if x1 != cursor or x2 <= x1 or upper >= 0:
            raise RuntimeError("non-contiguous or nonnegative seeded row")
        cursor = x2
    if cursor != t_hi:
        raise RuntimeError("seeded rows do not reach moving endpoint")
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    lines = [
        "SCALED BULK SIGN ROW UNIT CWIN3P2 SEEDED GRID",
        f"python {platform.python_version()}",
        f"python_flint {flint.__version__}",
        f"arb_bits {ctx.prec}",
        f"git_head {head}",
        f"unit {unit}",
        f"config CWIN {CWIN} beta_order {ORDER} t_order {T_ORDER} seed_step {step} prec {PREC}",
        f"beta_domain {lo} {hi}",
        f"t_domain {Fraction(3,5)} {t_hi}",
        f"t_partitions {len(boundaries)}",
    ]
    for partition, (a, b) in enumerate(boundaries):
        lines.append(f"t_partition {partition} {a} {b}")
    for relative in (
        "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_seeded_grid.py",
        "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high.py",
        "scripts/certify_bulk_beta_taylor_scaled_design.py",
        "scripts/certify_bulk_beta_taylor_arb.py",
    ):
        lines.append(f"dependency {relative} sha256 {sha256(ROOT / relative)}")
    for index, (partition, x1, x2, upper) in enumerate(rows):
        lines.append(f"trow {index} partition {partition} {x1} {x2} upper {upper.str(80)}")
    lines.append(f"t_rows {len(rows)}")
    lines.append("SCALED BULK SIGN ROW SEEDED GRID PASS")
    lines.append("SCOPE diagnostic seeded-grid CWIN=3/2 unit only; no G2/G6 promotion")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    parser.add_argument("--step", default="1/256")
    args = parser.parse_args()
    print(run(args.unit, Fraction(args.lo), Fraction(args.hi),
               Fraction(args.step)), end="")
