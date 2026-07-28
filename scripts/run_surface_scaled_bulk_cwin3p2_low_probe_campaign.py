"""Run a bounded candidate-only low-beta CWIN=3/2 probe."""

from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "scripts" / "run_surface_scaled_bulk_cwin3p2_high_unit.py"


def run_one(start: Fraction, i: int, replay: bool) -> str:
    lo = start + Fraction(i, 4)
    hi = lo + Fraction(1, 4)
    unit = f"low_{str(lo).replace('/', 'p')}_{str(hi).replace('/', 'p')}"
    command = [sys.executable, str(RUNNER), "--unit", unit,
               "--lo", str(lo), "--hi", str(hi)]
    if replay:
        command.append("--replay")
    completed = subprocess.run(command, cwd=ROOT, text=True,
                               stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=None)
    if completed.returncode:
        raise RuntimeError(completed.stdout)
    return completed.stdout.strip()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--workers", type=int, choices=(1, 2), default=2)
    parser.add_argument("--count", type=int, choices=range(1, 5), default=3)
    parser.add_argument("--start", default="81/4",
                        help="rational beta start, in quarter-step units")
    args = parser.parse_args()
    start = Fraction(args.start)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(run_one, start, i, args.replay)
                   for i in range(args.count)]
        for future in as_completed(futures):
            print(future.result(), flush=True)
    print("LOW PROBE COMPLETE", "REPLAY" if args.replay else "PRODUCTION",
          args.count, flush=True)


if __name__ == "__main__":
    main()
