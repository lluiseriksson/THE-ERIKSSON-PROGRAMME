"""Resumable launcher for the 15 five-row G5 design-cover units."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import os
from pathlib import Path
import subprocess
import sys

import surface_right_edge_five_family_cover_design as cover


ROOT = Path(__file__).resolve().parents[1]
PREFIX = "surface_right_edge_five_family_cover_design_lambda_"


def units():
    return [(start, min(start+5, 75)) for start in range(0, 75, 5)]


def slug(unit):
    return f"{unit[0]:02d}_{unit[1]:02d}"


def output_path(unit):
    return ROOT/"scripts"/f"{PREFIX}{slug(unit)}.txt"


def terminal(unit):
    return (
        "FIVE-FAMILY COVER DESIGN PASS delta 0 8 lambda "
        f"{unit[0]} {unit[1]} "
    )


def complete(unit):
    path = output_path(unit)
    if not path.exists():
        return False
    content = path.read_text(encoding="utf-8", errors="replace")
    dependencies = {
        line.split()[1]: line.split()[2] for line in content.splitlines()
        if line.startswith("DEPENDENCY ")
    }
    expected = {
        relative: hashlib.sha256((ROOT/relative).read_bytes()).hexdigest()
        for relative in cover.DEPENDENCIES
    }
    return (terminal(unit) in content
            and "COVER DESIGN FAIL" not in content
            and dependencies == expected)


def run_one(unit):
    path = output_path(unit)
    temporary = path.with_suffix(f".{os.getpid()}.tmp")
    result = subprocess.run(
        [sys.executable, str(ROOT/"scripts"/
         "surface_right_edge_five_family_cover_design.py"),
         "--start", str(unit[0]), "--stop", str(unit[1]),
         "--delta-start", "0", "--delta-stop", "8"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=None,
    )
    temporary.write_bytes(result.stdout)
    if result.returncode != 0:
        failed = path.with_suffix(".failed.txt")
        temporary.replace(failed)
        raise RuntimeError(f"design unit {slug(unit)} failed")
    temporary.replace(path)
    if not complete(unit):
        raise RuntimeError(f"design unit {slug(unit)} lacks terminal marker")
    return unit


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, choices=(1, 2, 3), default=3)
    parser.add_argument("--max-units", type=int, default=None)
    args = parser.parse_args()
    pending = [unit for unit in units() if not complete(unit)]
    if args.max_units is not None:
        if args.max_units < 1:
            parser.error("--max-units must be positive")
        pending = pending[:args.max_units]
    print("G5 DESIGN LAUNCH pending", len(pending), "workers", args.workers,
          flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_one, unit): unit for unit in pending}
        for completed, future in enumerate(as_completed(futures), 1):
            unit = future.result()
            print("G5 DESIGN UNIT COMPLETE", slug(unit), completed,
                  "of", len(pending), flush=True)
    print("G5 DESIGN LAUNCH COMPLETE", len(pending), "new units", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
