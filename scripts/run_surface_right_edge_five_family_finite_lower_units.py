"""Resumable launcher for frozen lower finite-G5 production units."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import os
from pathlib import Path
import subprocess
import sys

import certify_surface_right_edge_five_family_finite_lower as cert


ROOT = Path(__file__).resolve().parents[1]


def output_path(unit):
    return ROOT/"scripts"/(
        "certify_surface_right_edge_five_family_finite_lower_"
        f"{cert.unit_slug(unit)}_transcript.txt")


def terminal(unit):
    rows = len(cert.cover.DELTA_BANDS)*(unit[1]-unit[0])
    return ("CERTIFIED RIGHT-EDGE FIVE-FAMILY FINITE UNIT "
            f"{cert.unit_slug(unit)} {rows} rows ")


def complete(unit, head):
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
        for relative in cert.DEPENDENCIES
    }
    return (f"PROVENANCE git_head {head}\n" in content
            and terminal(unit) in content
            and "CERTIFICATE FAIL" not in content
            and dependencies == expected)


def run_one(unit, head):
    path = output_path(unit)
    temporary = path.with_suffix(f".{os.getpid()}.tmp")
    result = subprocess.run(
        [sys.executable, str(ROOT/"scripts"/
         "certify_surface_right_edge_five_family_finite_lower.py"),
         "--unit", cert.unit_slug(unit)], cwd=ROOT,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=None)
    temporary.write_bytes(result.stdout)
    if result.returncode != 0:
        temporary.replace(path.with_suffix(".failed.txt"))
        raise RuntimeError(f"lower finite production {cert.unit_slug(unit)} failed")
    temporary.replace(path)
    if not complete(unit, head):
        raise RuntimeError(f"lower finite production {cert.unit_slug(unit)} stale")
    return unit


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int,
                        choices=(1, 2, 3, 4, 6, 8), default=3)
    parser.add_argument("--max-units", type=int, default=None)
    args = parser.parse_args()
    head = cert.current_head()
    pending = [unit for unit in cert.UNITS if not complete(unit, head)]
    if args.max_units is not None:
        pending = pending[:args.max_units]
    print("LOWER FINITE G5 PRODUCTION LAUNCH head", head, "pending",
          len(pending), "workers", args.workers, flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_one, unit, head): unit for unit in pending}
        for count, future in enumerate(as_completed(futures), 1):
            unit = future.result()
            print("LOWER FINITE G5 PRODUCTION UNIT COMPLETE",
                  cert.unit_slug(unit), count, "of", len(pending), flush=True)
    print("LOWER FINITE G5 PRODUCTION LAUNCH COMPLETE", len(pending),
          "new units", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
