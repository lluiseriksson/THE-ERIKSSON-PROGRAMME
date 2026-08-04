"""Corrected scoped G5 lambda-extension driver.

The historical driver is intentionally left untouched.  This successor
rebinds the finite-tail budget to the proven endpoint lambda_max=8/5 and
records that choice in its provenance/configuration lines.
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
import surface_right_edge_five_family_finite_tail_lambda16_candidate as tail


ROOT = Path(__file__).resolve().parents[1]
UNITS = {"lambda_75_80": (75, 80)}
DEPENDENCIES = (
    "scripts/certify_surface_right_edge_five_family_finite_lambda16_corrected.py",
    "scripts/surface_right_edge_five_family_finite_tail_lambda16_candidate.py",
    "scripts/surface_right_edge_five_family_finite_cover_design.py",
    *cover.DEPENDENCIES,
)


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
    parser.add_argument("--unit", choices=tuple(UNITS), required=True)
    parser.add_argument("--delta-index", type=int, default=0)
    args = parser.parse_args()
    start, stop = UNITS[args.unit]
    if not 0 <= args.delta_index < len(cover.DELTA_BANDS):
        parser.error("invalid delta index")

    # The cover's judge reads its module-global tail; this is the sole
    # successor-specific substitution and is recorded in DEPENDENCIES.
    cover.tail = tail
    ctx.prec = 140
    started = perf_counter()
    print("PROVENANCE git_head", current_head(), flush=True)
    print("PROVENANCE python", platform.python_version(), flush=True)
    print("PROVENANCE python_flint", flint.__version__, flush=True)
    print("PROVENANCE arb_bits", ctx.prec, flush=True)
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(ROOT / relative), flush=True)
    dlo, dhi = cover.DELTA_BANDS[args.delta_index]
    print(
        "CONFIG delta_band", cover.fraction_string(dlo) + ":" +
        cover.fraction_string(dhi),
        "delta_index", args.delta_index,
        "lambda_partition 0:8/5:1/50",
        "lambda_unit", args.unit,
        "tail_lambda_max 8/5",
        "side 5/2 coarse qgrid80 rgrid16 thetagrid4 phigrid4 "
        "mixed qgrid160 rgrid32",
        flush=True,
    )

    worst = None
    for index in range(start, stop):
        resolution, budgets, families, p0, h = cover.judge(
            args.delta_index, index)
        row = {
            "delta_index": args.delta_index,
            "delta_lo": cover.fraction_string(dlo),
            "delta_hi": cover.fraction_string(dhi),
            "lambda_index": index,
            "lambda_lo": f"{index}/50",
            "lambda_hi": f"{index+1}/50",
            "resolution": resolution,
            "tail_budgets": [endpoint(value, False) for value in budgets],
            "families_lower": [endpoint(value, True) for value in families],
            "families_upper": [endpoint(value, False) for value in families],
            "P0_lower": endpoint(p0, True),
            "P0_upper": endpoint(p0, False),
            "H_lower": endpoint(h, True),
            "H_upper": endpoint(h, False),
        }
        print("ROW " + json.dumps(row, sort_keys=True), flush=True)
        lower = arb(row["H_lower"])
        if not arb(row["families_lower"][3]) > 0:
            raise SystemExit(f"CERTIFICATE FAIL B0 {args.delta_index} {index}")
        if not arb(row["P0_lower"]) > 0:
            raise SystemExit(f"CERTIFICATE FAIL P0 {args.delta_index} {index}")
        if not lower > 0:
            raise SystemExit(f"CERTIFICATE FAIL H {args.delta_index} {index}")
        if worst is None or lower < worst[0]:
            worst = (lower, args.delta_index, index)
    print(
        "CERTIFIED SCOPED CANDIDATE RIGHT-EDGE FIVE-FAMILY FINITE UNIT",
        args.unit, len(range(start, stop)), "rows",
        "delta_index", args.delta_index,
        "worst_lambda_index", worst[2],
        "worst_H_lower", worst[0].str(80),
        "elapsed_seconds", perf_counter() - started,
        "NO G2/G5/G6 PROMOTION",
        flush=True,
    )


if __name__ == "__main__":
    main()
