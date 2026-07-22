"""Run or replay the two frozen scaled-bulk [35,36] candidate units."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import subprocess
import sys

import certify_surface_scaled_bulk_35_36_candidate as cert

ROOT = Path(__file__).resolve().parents[1]


def path(unit: str, suffix: str = "") -> Path:
    return ROOT / "scripts" / f"surface_scaled_bulk_{unit}{suffix}.txt"


def run(unit: str, suffix: str = "") -> None:
    target = path(unit, suffix)
    tmp = target.with_suffix(f".{os.getpid()}.tmp")
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" /
         "certify_surface_scaled_bulk_35_36_candidate.py"),
         "--unit", unit], cwd=ROOT, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=None)
    tmp.write_bytes(result.stdout)
    if result.returncode:
        tmp.replace(target.with_suffix(".failed.txt"))
        raise RuntimeError(f"scaled bulk candidate {unit} failed")
    tmp.replace(target)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, choices=(1, 2), default=2)
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    suffix = "_rerun" if args.replay else ""
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(run, unit, suffix)
                   for unit in cert.SEGMENTS]
        for future in as_completed(futures):
            future.result()
    print("SCALED BULK [35,36] CANDIDATE",
          "REPLAY" if args.replay else "PRODUCTION", "COMPLETE",
          len(cert.SEGMENTS))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
