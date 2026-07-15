"""Authoritative unit driver for the paired scaled left-edge bridge."""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
from time import perf_counter

import flint
from flint import arb, ctx

import certify_bulk_beta_taylor_arb as bulk
import certify_bulk_beta_taylor_scaled_design as scaled
import certify_left_edge_beta_taylor_arb as left
import certify_left_edge_beta_taylor_scaled_paired_design as paired
import surface_finite_beta_scaled_partition as partition


ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = (
    "scripts/certify_surface_finite_beta_scaled_left.py",
    "scripts/surface_finite_beta_scaled_partition.py",
    "scripts/certify_left_edge_beta_taylor_scaled_paired_design.py",
    "scripts/certify_bulk_beta_taylor_scaled_design.py",
    "scripts/certify_left_edge_beta_taylor_arb.py",
    "scripts/certify_bulk_beta_taylor_arb.py",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current_head():
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def upper_string(value):
    return arb(value.upper()).str(80)


def cover_rows(evaluator, lo, hi, min_width=paired.Fraction(1, 1_000_000)):
    rows = []
    stack = [(lo, hi)]
    while stack:
        a, b = stack.pop()
        value = evaluator(a, b)
        if value < 0:
            rows.append((a, b, upper_string(value)))
        elif b-a <= min_width:
            raise RuntimeError("left production failure near t=%s" % float(a))
        else:
            mid = (a+b)/2
            stack.append((mid, b)); stack.append((a, mid))
    return rows


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--unit", choices=tuple(partition.unit_map()))
    group.add_argument("--beta-index", type=int,
                       choices=range(len(partition.BETA_INTERVALS)))
    args = parser.parse_args()
    if args.unit is not None:
        unit = partition.unit_map()[args.unit]
        label = args.unit
    else:
        unit = (args.beta_index, args.beta_index+1)
        label = f"beta_index_{args.beta_index:04d}"
    ctx.prec = 180
    scaled.install_design_backend()
    started = perf_counter()
    print("PROVENANCE git_head", current_head(), flush=True)
    print("PROVENANCE python", platform.python_version(), flush=True)
    print("PROVENANCE python_flint", flint.__version__, flush=True)
    print("PROVENANCE arb_bits", ctx.prec, flush=True)
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(ROOT/relative), flush=True)
    print("CONFIG beta_start 20 beta_stop 1000/9 beta_step 1/10 "
          "beta_order 20 t_order 20 splice 19/100", flush=True)

    row_count = 0
    worst = None
    for beta_index in range(unit[0], unit[1]):
        beta_lo, beta_hi = partition.BETA_INTERVALS[beta_index]
        box = left.LeftEdgeBox(
            beta_lo, beta_hi, order=paired.BETA_ORDER,
            t_order=paired.T_ORDER, prec=180)
        fourier = paired.endpoint_fourier(box)
        paired.identity_regression(box, fourier)
        hi_abs = box._absolute_sums_at_hi(
            paired.BETA_ORDER+1, paired.T_ORDER+2)
        coefficients = [
            paired.coefficient_beta_enclosure(box, fourier, hi_abs, k)
            for k in range(1, paired.T_ORDER//2)
        ]
        normalized = cover_rows(
            lambda a, b: paired.paired_normalized(
                box, coefficients, hi_abs, a, b),
            paired.Fraction(0), paired.SPLICE)
        regular = cover_rows(
            box.box.W, paired.SPLICE, paired.Fraction(3, 5))
        for lane, lane_rows in (("normalized", normalized),
                                ("regular", regular)):
            for t_lo, t_hi, upper in lane_rows:
                record = {
                    "beta_index": beta_index,
                    "beta_lo": partition.fraction_string(beta_lo),
                    "beta_hi": partition.fraction_string(beta_hi),
                    "lane": lane,
                    "t_lo": partition.fraction_string(t_lo),
                    "t_hi": partition.fraction_string(t_hi),
                    "W_upper": upper,
                }
                print("ROW "+json.dumps(record, sort_keys=True), flush=True)
                row_count += 1
                bound = arb(upper)
                if not bound < 0:
                    print("CERTIFICATE FAIL", beta_index, lane, flush=True)
                    return 1
                if worst is None or bound > worst:
                    worst = bound
    print("CERTIFIED FINITE-BETA SCALED LEFT UNIT", label,
          unit[1]-unit[0], "beta_intervals", row_count, "rows",
          "worst_upper", worst.str(80),
          "elapsed_seconds", perf_counter()-started, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
