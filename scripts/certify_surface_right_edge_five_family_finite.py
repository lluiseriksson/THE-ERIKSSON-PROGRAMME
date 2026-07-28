"""Authoritative unit driver for the finite five-family G5 bridge.

Execution is valid only from a frozen commit.  The design partition and
numerical judge are imported byte-for-byte from the validated design cover.
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

import surface_right_edge_five_family_finite_cover_design as cover


ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = (
    "scripts/certify_surface_right_edge_five_family_finite.py",
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


def main(cover_module=cover, dependencies=DEPENDENCIES):
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
    for relative in dependencies:
        print("DEPENDENCY", relative, sha256(ROOT/relative), flush=True)
    print("CONFIG delta_bands", ",".join(
        cover_module.fraction_string(lo)+":"+cover_module.fraction_string(hi)
        for lo, hi in cover_module.DELTA_BANDS),
        "lambda_partition 0:3/2:1/50 side 5/2 "
        "coarse qgrid80 rgrid16 thetagrid4 phigrid4 "
        "mixed qgrid160 rgrid32", flush=True)
    worst = None
    for delta_index, (dlo, dhi) in enumerate(cover_module.DELTA_BANDS):
        for index in range(unit[0], unit[1]):
            resolution, budgets, families, p0, h = cover_module.judge(
                delta_index, index)
            row = {
                "delta_index": delta_index,
                "delta_lo": cover_module.fraction_string(dlo),
                "delta_hi": cover_module.fraction_string(dhi),
                "lambda_index": index,
                "lambda_lo": f"{index}/50",
                "lambda_hi": f"{index+1}/50",
                "resolution": resolution,
                "tail_budgets": [endpoint(value, False)
                                 for value in budgets],
                "families_lower": [endpoint(value, True)
                                   for value in families],
                "families_upper": [endpoint(value, False)
                                   for value in families],
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
    print("CERTIFIED RIGHT-EDGE FIVE-FAMILY FINITE UNIT", args.unit,
          len(cover_module.DELTA_BANDS)*(unit[1]-unit[0]), "rows",
          "worst_delta_index", worst[1], "worst_lambda_index", worst[2],
          "worst_H_lower", worst[0].str(80),
          "elapsed_seconds", perf_counter()-started, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
