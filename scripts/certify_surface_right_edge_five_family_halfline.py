"""Authoritative Arb production for the scaled five-family half-line.

The certificate covers delta in [0,1/125] and lambda in [0,3/2].  It is
deliberately separate from the finite-beta design lane.
"""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
from time import perf_counter

import flint
from flint import arb, ctx

import surface_right_edge_five_family_cover_design as cover


ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = (
    "scripts/certify_surface_right_edge_five_family_halfline.py",
    *cover.DEPENDENCIES,
)
UNITS = tuple((start, min(start+5, 75)) for start in range(0, 75, 5))


def unit_slug(unit):
    return f"lambda_{unit[0]:02d}_{unit[1]:02d}"


def unit_map():
    return {unit_slug(unit): unit for unit in UNITS}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current_head():
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def endpoint(value, lower):
    bound = value.lower() if lower else value.upper()
    return arb(bound).str(80)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--unit", choices=tuple(unit_map()), required=True)
    args = parser.parse_args()
    unit = unit_map()[args.unit]
    ctx.prec = 140
    started = perf_counter()
    print("PROVENANCE git_head", current_head(), flush=True)
    print("PROVENANCE python", platform.python_version(), flush=True)
    print("PROVENANCE python_flint", flint.__version__, flush=True)
    print("PROVENANCE arb_bits", ctx.prec, flush=True)
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(ROOT/relative), flush=True)
    print(
        "CONFIG delta_partition 0:1/125:1/1000 "
        "lambda_partition 0:3/2:1/50 "
        "coarse side 4 qgrid 80 rgrid 16 thetagrid 4 phigrid 4 "
        "mixed U0/U2=coarse U1 qgrid160 rgrid32 thetagrid8 phigrid1 "
        "B0 qgrid160 rgrid32 thetagrid1 "
        "B1 qgrid160 rgrid32 thetagrid8",
        flush=True,
    )
    budgets = cover.family_tail_budgets()
    print("TAILS", *(item.str(80) for item in budgets), flush=True)
    worst = None
    for delta_index in range(8):
        for index in range(unit[0], unit[1]):
            resolution, families, p0, h = cover.judge(
                index, budgets, delta_index)
            row = {
                "delta_index": delta_index,
                "delta_lo": f"{delta_index}/1000",
                "delta_hi": f"{delta_index+1}/1000",
                "lambda_index": index,
                "lambda_lo": f"{index}/50",
                "lambda_hi": f"{index+1}/50",
                "resolution": resolution,
                "families_lower": [
                    endpoint(value, True) for value in families],
                "families_upper": [
                    endpoint(value, False) for value in families],
                "P0_lower": endpoint(p0, True),
                "P0_upper": endpoint(p0, False),
                "H_lower": endpoint(h, True),
                "H_upper": endpoint(h, False),
            }
            print("ROW " + json.dumps(row, sort_keys=True), flush=True)
            lower = arb(row["H_lower"])
            if not arb(row["families_lower"][3]) > 0:
                print("CERTIFICATE FAIL B0", delta_index, index, flush=True)
                return 1
            if not arb(row["P0_lower"]) > 0:
                print("CERTIFICATE FAIL P0", delta_index, index, flush=True)
                return 1
            if not lower > 0:
                print("CERTIFICATE FAIL H", delta_index, index, flush=True)
                return 1
            if worst is None or lower < worst[0]:
                worst = (lower, delta_index, index)
    print(
        "CERTIFIED RIGHT-EDGE FIVE-FAMILY HALFLINE UNIT", args.unit,
        "40 rows "
        "worst_delta_index", worst[1], "worst_lambda_index", worst[2],
        "worst_H_lower", worst[0].str(80),
        "elapsed_seconds", perf_counter()-started,
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
