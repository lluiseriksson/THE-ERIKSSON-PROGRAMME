"""Fresh replay runner for the preregistered compact G5 extension."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import subprocess
import sys

import certify_right_edge_beta_taylor_cached_extension as cert

ROOT = Path(__file__).resolve().parents[1]


def replay_path(unit):
    return ROOT / "scripts" / f"certify_right_edge_compact_extension_{unit}_rerun.txt"


def run_one(unit):
    path = replay_path(unit)
    temporary = path.with_suffix(f".{os.getpid()}.tmp")
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" /
         "certify_right_edge_beta_taylor_cached_extension.py"),
         "--unit", unit], cwd=ROOT, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=None)
    temporary.write_bytes(result.stdout)
    if result.returncode != 0:
        temporary.replace(path.with_suffix(".failed.txt"))
        raise RuntimeError(f"compact extension replay {unit} failed")
    temporary.replace(path)
    return unit


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, choices=(1, 2, 3), default=3)
    args = parser.parse_args()
    units = tuple(cert.SEGMENTS)
    print("COMPACT G5 REPLAY LAUNCH", len(units), "workers", args.workers,
          flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_one, unit): unit for unit in units}
        for count, future in enumerate(as_completed(futures), 1):
            print("COMPACT G5 REPLAY UNIT COMPLETE", future.result(),
                  count, "of", len(units), flush=True)
    print("COMPACT G5 REPLAY LAUNCH COMPLETE", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
