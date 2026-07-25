"""Run the preregistered post-1635/16 MIN_DT=1e-8 diagnostic.

This wrapper changes exactly one numerical knob of the audited seeded-grid
driver: the recursive minimum time-cell width.  The result remains
candidate-only and is never consumed by the authoritative G2 audit directly.
"""

from fractions import Fraction
import hashlib
import sys
from pathlib import Path

import certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high as high
import certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_seeded_grid as seeded

ROOT = Path(__file__).resolve().parents[1]
MIN_DT = Fraction(1, 100_000_000)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(unit: str, lo: Fraction, hi: Fraction, step: Fraction) -> str:
    high.MIN_DT = MIN_DT
    raw = seeded.run(unit, lo, hi, step)
    lines = raw.splitlines()
    lines[0] = "SCALED BULK SIGN ROW UNIT CWIN3P2 SEEDED GRID MIN8"
    lines[6] = lines[6] + f" min_dt {MIN_DT}"
    insert_at = next(i for i, line in enumerate(lines) if line.startswith("trow "))
    lines.insert(insert_at, f"dependency scripts/run_surface_g2_post1635_min8_cell.py sha256 {sha256(Path(__file__))}")
    for i, line in enumerate(lines):
        if line.startswith("SCOPE "):
            lines[i] = "SCOPE quarantined min8 full-cell candidate only; no G2/G6 promotion"
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    parser.add_argument("--step", default="1/64")
    args = parser.parse_args()
    print(run(args.unit, Fraction(args.lo), Fraction(args.hi), Fraction(args.step)), end="")
