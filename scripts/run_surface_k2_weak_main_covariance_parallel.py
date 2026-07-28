"""Parallel deterministic runner for the weak-main covariance certificates."""

from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction
import hashlib
from pathlib import Path
import platform

from flint import arb, ctx

import certify_surface_k2_weak_main_covariance as base
from surface_remainder_arb_jet2 import hull


ROOT = Path(__file__).resolve().parents[1]
WORKERS = 12
LANES = {
    "near": {
        "t_min": Fraction(21, 10),
        "t_max": Fraction(31_415_927, 10_000_000),
        "t_boxes": 32,
        "grids": (24, 48),
        "prereg": (
            "docs/SURFACE-K2-WEAK-MAIN-COVARIANCE-V2-PREREG-20260728.md"
        ),
    },
    "far": {
        "t_min": Fraction(0),
        "t_max": Fraction(21, 10),
        "t_boxes": 32,
        "grids": (24, 48, 96),
        "prereg": (
            "docs/SURFACE-K2-WEAK-MAIN-COVARIANCE-FAR-PREREG-20260728.md"
        ),
    },
}
COMMON_DEPENDENCIES = (
    "scripts/run_surface_k2_weak_main_covariance_parallel.py",
    "docs/SURFACE-K2-WEAK-MAIN-COVARIANCE-PARALLEL-V3-PREREG-20260728.md",
    "docs/INCIDENT-WEAK-MAIN-TRANSCRIPT-LOSSY-ENDPOINTS-20260728.md",
    (
        "docs/"
        "SURFACE-K2-WEAK-MAIN-COVARIANCE-REPORTING-V4-PREREG-20260728.md"
    ),
)
_TAIL = None


def sha256(relative: str) -> str:
    return hashlib.sha256((ROOT/relative).read_bytes()).hexdigest().upper()


def worker_init() -> None:
    global _TAIL
    ctx.prec = base.ARB_BITS
    _TAIL = base.uniform_tail_charges()


def worker(task: tuple[str, int, int]) -> dict[str, object]:
    lane_name, di, ti = task
    lane = LANES[lane_name]
    delta_width = base.DELTA_MAX/base.DELTA_BOXES
    t_width = (
        (lane["t_max"]-lane["t_min"])/lane["t_boxes"]
    )
    dlo = delta_width*di
    dhi = delta_width*(di+1)
    tlo = lane["t_min"]+t_width*ti
    thi = lane["t_min"]+t_width*(ti+1)
    delta = hull(base.aq(dlo), base.aq(dhi))
    t = hull(base.aq(tlo), base.aq(thi))
    attempts = []
    for grid in lane["grids"]:
        try:
            kd, xmain = base.judge(delta, t, grid, _TAIL)
            kd_lower = arb(kd.lower())
            lower = arb(xmain.lower())
            attempts.append(
                (
                    grid,
                    kd.str(18),
                    kd_lower.str(50),
                    xmain.str(18),
                    lower.str(50),
                    "",
                )
            )
            if lower > base.aq(base.TARGET):
                return {
                    "accepted": True,
                    "lane": lane_name,
                    "di": di,
                    "ti": ti,
                    "dlo": str(dlo),
                    "dhi": str(dhi),
                    "tlo": str(tlo),
                    "thi": str(thi),
                    "grid": grid,
                    "kd": kd.str(18),
                    "kd_lower": kd_lower.str(50),
                    "xmain": xmain.str(18),
                    "lower": lower.str(50),
                    "attempts": attempts,
                }
        except Exception as exc:
            attempts.append(
                (grid, "", "", "", "", f"{type(exc).__name__}: {exc}")
            )
    return {
        "accepted": False,
        "lane": lane_name,
        "di": di,
        "ti": ti,
        "dlo": str(dlo),
        "dhi": str(dhi),
        "tlo": str(tlo),
        "thi": str(thi),
        "attempts": attempts,
    }


def run(lane_name: str, progress_path: Path) -> dict[str, object]:
    lane = LANES[lane_name]
    tasks = [
        (lane_name, di, ti)
        for di in range(base.DELTA_BOXES)
        for ti in range(lane["t_boxes"])
    ]
    results = []
    failures = 0
    with progress_path.open("x", encoding="utf-8", newline="\n") as progress:
        progress.write(
            f"START lane={lane_name} boxes={len(tasks)} workers={WORKERS}\n"
        )
        progress.flush()
        with ProcessPoolExecutor(
            max_workers=WORKERS,
            initializer=worker_init,
        ) as executor:
            futures = [executor.submit(worker, task) for task in tasks]
            for completed, future in enumerate(as_completed(futures), 1):
                result = future.result()
                results.append(result)
                if not result["accepted"]:
                    failures += 1
                progress.write(
                    f"DONE {completed}/{len(tasks)} "
                    f"d={result['di']} t={result['ti']} "
                    f"accepted={result['accepted']} failures={failures}\n"
                )
                progress.flush()
        progress.write(f"END completed={len(results)} failures={failures}\n")
    results.sort(key=lambda item: (item["di"], item["ti"]))
    return {"lane": lane, "results": results, "failures": failures}


def print_header(lane_name: str) -> dict[str, arb]:
    lane = LANES[lane_name]
    print("PROVENANCE git_head", base.current_head(), flush=True)
    print("PROVENANCE python", platform.python_version(), flush=True)
    print("PROVENANCE python_flint", base.flint.__version__, flush=True)
    print("PROVENANCE arb_bits", base.ARB_BITS, flush=True)
    print("PROVENANCE workers", WORKERS, flush=True)
    dependencies = tuple(dict.fromkeys(
        tuple(base.DEPENDENCIES)+COMMON_DEPENDENCIES+(lane["prereg"],)
    ))
    for relative in dependencies:
        print("DEPENDENCY", relative, sha256(relative), flush=True)
    grids = ",".join(str(value) for value in lane["grids"])
    print(
        "CONFIG",
        f"lane={lane_name}",
        "delta=0:9/1000:18",
        f"t={lane['t_min']}:{lane['t_max']}:{lane['t_boxes']}",
        "side=12",
        f"grids={grids}",
        "companion_order=4",
        "z0=20",
        "workers=12",
        flush=True,
    )
    return base.uniform_tail_charges()


def emit(lane_name: str, result: dict[str, object], tail: dict[str, arb]) -> int:
    print("WEAK MAIN TRUE-COMPANION COVARIANCE", lane_name.upper())
    for name in ("rate", "kernel_constant", "g_abs", "kd", "kf", "gdd", "gdf"):
        print("TAIL", name, tail[name].str(50))
    grid_counts = {grid: 0 for grid in LANES[lane_name]["grids"]}
    worst_lower = arb(1)
    worst_label = ""
    for row in result["results"]:
        if row["accepted"]:
            grid_counts[row["grid"]] += 1
            lower = arb(row["lower"])
            if lower < worst_lower:
                worst_lower = lower
                worst_label = f"d{row['di']}:t{row['ti']}:g{row['grid']}"
            print(
                "ROW",
                row["di"],
                row["ti"],
                f"{row['dlo']}:{row['dhi']}",
                f"{row['tlo']}:{row['thi']}",
                "grid",
                row["grid"],
                "KD",
                row["kd"],
                "KDLOWER",
                row["kd_lower"],
                "XMAIN",
                row["xmain"],
                "XMAINLOWER",
                row["lower"],
            )
        else:
            print(
                "FAILROW",
                row["di"],
                row["ti"],
                f"{row['dlo']}:{row['dhi']}",
                f"{row['tlo']}:{row['thi']}",
                "attempts",
                repr(row["attempts"]),
            )
    print("GRID_COUNTS", grid_counts)
    print(
        "WORST_LOWER",
        worst_lower.str(50),
        "at",
        worst_label,
        "> -1/20",
    )
    if result["failures"]:
        print(
            "WEAK MAIN TRUE-COMPANION COVARIANCE FAIL",
            lane_name,
            "failures",
            result["failures"],
        )
        print("SCOPE diagnostic failure map only; no promotion")
        return 1
    print("WEAK MAIN TRUE-COMPANION COVARIANCE PASS", lane_name)
    print(
        "SCOPE weak X_main premise only; "
        "terminal union and manuscript remain open"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lane", choices=tuple(LANES), required=True)
    parser.add_argument("--progress-file", type=Path, required=True)
    args = parser.parse_args()
    ctx.prec = base.ARB_BITS
    tail = print_header(args.lane)
    result = run(args.lane, args.progress_file)
    return emit(args.lane, result, tail)


if __name__ == "__main__":
    raise SystemExit(main())
