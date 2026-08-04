"""Diagnostic minimum-grid-48 refinement of accepted weak-main rows."""

from __future__ import annotations

from concurrent.futures import ProcessPoolExecutor, as_completed
from decimal import Decimal, getcontext
from fractions import Fraction
import hashlib
from pathlib import Path
import platform
import re

from flint import arb, ctx

import certify_surface_k2_weak_main_covariance as base
import run_surface_k2_weak_main_covariance_parallel as runner
import validate_surface_k2_weak_main_covariance_transcripts as validator
from surface_remainder_arb_jet2 import hull


ROOT = Path(__file__).resolve().parents[1]
WORKERS = 12
GRID = 48
PREREG = (
    "docs/SURFACE-K2-WEAK-MAIN-FLOOR48-DIAGNOSTIC-PREREG-20260728.md"
)
DEPENDENCIES = (
    "scripts/diagnose_surface_k2_weak_main_floor48.py",
    PREREG,
    "scripts/certify_surface_k2_weak_main_covariance.py",
    "scripts/surface_bessel_integral_remainder.py",
    "scripts/surface_remainder_delta0_moving_tail.py",
)
ROW = re.compile(
    r"ROW (\d+) (\d+) \S+ \S+ grid (24|48|96) "
    r"KD .+ KDLOWER .+ XMAIN .+ XMAINLOWER (.+)"
)
_TAIL = None


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def worker_init() -> None:
    global _TAIL
    ctx.prec = base.ARB_BITS
    _TAIL = base.uniform_tail_charges()


def box(lane_name: str, di: int, ti: int) -> tuple[arb, arb]:
    lane = runner.LANES[lane_name]
    delta_width = base.DELTA_MAX/base.DELTA_BOXES
    t_width = (lane["t_max"]-lane["t_min"])/lane["t_boxes"]
    delta = hull(
        base.aq(delta_width*di),
        base.aq(delta_width*(di+1)),
    )
    t = hull(
        base.aq(lane["t_min"]+t_width*ti),
        base.aq(lane["t_min"]+t_width*(ti+1)),
    )
    return delta, t


def refine(task: tuple[str, int, int, str]) -> dict[str, object]:
    lane_name, di, ti, old_lower_text = task
    try:
        delta, t = box(lane_name, di, ti)
        kd, xmain = base.judge(delta, t, GRID, _TAIL)
        kd_lower = arb(kd.lower())
        lower = arb(xmain.lower())
        old_lower = arb(old_lower_text)
        return {
            "ok": bool(kd_lower > 0 and lower > old_lower),
            "lane": lane_name,
            "di": di,
            "ti": ti,
            "old_lower": old_lower.str(50),
            "kd_lower": kd_lower.str(50),
            "lower": lower.str(50),
            "error": "",
        }
    except Exception as exc:
        return {
            "ok": False,
            "lane": lane_name,
            "di": di,
            "ti": ti,
            "old_lower": old_lower_text,
            "kd_lower": "",
            "lower": "",
            "error": f"{type(exc).__name__}: {exc}",
        }


def rows(lane_name: str) -> list[dict[str, object]]:
    production, _, _, _ = validator.artifact_paths(lane_name)
    parsed = []
    for line in production.read_text(encoding="utf-8").splitlines():
        match = ROW.fullmatch(line)
        if match is None:
            continue
        parsed.append(
            {
                "lane": lane_name,
                "di": int(match.group(1)),
                "ti": int(match.group(2)),
                "grid": int(match.group(3)),
                "lower": match.group(4),
            }
        )
    if len(parsed) != base.DELTA_BOXES*runner.LANES[lane_name]["t_boxes"]:
        raise AssertionError((lane_name, len(parsed)))
    return parsed


def main() -> int:
    getcontext().prec = 120
    ctx.prec = base.ARB_BITS
    validations = {
        lane: validator.validate(lane) for lane in ("near", "far")
    }
    original = [row for lane in ("near", "far") for row in rows(lane)]
    tasks = [
        (row["lane"], row["di"], row["ti"], row["lower"])
        for row in original if row["grid"] == 24
    ]
    results = []
    with ProcessPoolExecutor(
        max_workers=WORKERS,
        initializer=worker_init,
    ) as executor:
        futures = [executor.submit(refine, task) for task in tasks]
        for future in as_completed(futures):
            results.append(future.result())
    results.sort(key=lambda item: (item["lane"], item["di"], item["ti"]))

    print("PROVENANCE git_head", base.current_head())
    print("PROVENANCE python", platform.python_version())
    print("PROVENANCE python_flint", base.flint.__version__)
    print("PROVENANCE arb_bits", base.ARB_BITS)
    print("PROVENANCE workers", WORKERS)
    for relative in DEPENDENCIES:
        print("DEPENDENCY", relative, sha256(ROOT/relative))
    for lane, result in validations.items():
        print("SOURCE", lane, result["sha256"], result["rows"])
    print("CONFIG selected_grid=24 diagnostic_grid=48")

    failures = 0
    replacement = {
        (item["lane"], item["di"], item["ti"]): item["lower"]
        for item in results if item["ok"]
    }
    for item in results:
        if not item["ok"]:
            failures += 1
        print(
            "REFINE",
            item["lane"],
            item["di"],
            item["ti"],
            "OLDLOWER",
            item["old_lower"],
            "KDLOWER",
            item["kd_lower"],
            "NEWLOWER",
            item["lower"],
            "OK",
            item["ok"],
            "ERROR",
            repr(item["error"]),
        )
    if failures:
        print("FLOOR-GRID-48 DIAGNOSTIC FAIL failures", failures)
        print("SCOPE diagnostic only; theorem gates unchanged")
        return 1

    worst = Decimal(1)
    label = ""
    for item in original:
        key = (item["lane"], item["di"], item["ti"])
        text = replacement.get(key, item["lower"])
        lower, _ = validator.endpoints(text)
        if lower < worst:
            worst = lower
            label = f"{item['lane']}:d{item['di']}:t{item['ti']}"
    print("FLOOR48_COUNTS refined", len(results), "total", len(original))
    print("FLOOR48_WORST_LOWER", worst, "at", label)
    print("FLOOR-GRID-48 DIAGNOSTIC PASS")
    print("SCOPE diagnostic only; theorem gates unchanged")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
