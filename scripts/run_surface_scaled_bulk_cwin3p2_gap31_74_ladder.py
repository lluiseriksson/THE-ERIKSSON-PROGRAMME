"""Run a fixed width-1/16 production/replay slice of the [31,74] ladder."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "scripts" / "run_surface_scaled_bulk_cwin3p2_high_unit.py"
PREREG = "SURFACE-SCALED-BULK-CWIN3P2-GAP31-74-LADDER-PREREG-20260722.md"
START = Fraction(31)
STOP = Fraction(74)
WIDTH = Fraction(1, 16)
TOTAL = int((STOP - START) / WIDTH)


def label(value: Fraction) -> str:
    return str(value).replace("/", "p").replace("-", "m").replace(".", "p")


def unit(index: int) -> tuple[str, Fraction, Fraction]:
    if not 0 <= index < TOTAL:
        raise ValueError(f"index {index} outside 0..{TOTAL-1}")
    lo = START + index * WIDTH
    hi = lo + WIDTH
    return f"gap31_74_{label(lo)}_{label(hi)}", lo, hi


def run_one(index: int) -> str:
    name, lo, hi = unit(index)
    lines = []
    for replay in (False, True):
        cmd = [sys.executable, str(RUNNER), "--unit", name,
               "--lo", str(lo), "--hi", str(hi)]
        if replay:
            cmd.append("--replay")
        proc = subprocess.run(cmd, cwd=ROOT, text=True,
                              stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=None)
        lines.append(proc.stdout.strip())
        if proc.returncode:
            raise RuntimeError("\n".join(lines))
    return f"index={index} unit={name} lo={lo} hi={hi}\n" + "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--start-index", type=int, default=0)
    parser.add_argument("--count", type=int, default=1)
    parser.add_argument("--workers", type=int, choices=(1, 2, 4), default=2)
    args = parser.parse_args()
    stop = args.start_index + args.count
    if args.start_index < 0 or stop > TOTAL:
        raise SystemExit(f"slice must lie in [0,{TOTAL}]")
    indices = list(range(args.start_index, stop))
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_one, i): i for i in indices}
        for future in as_completed(futures):
            print(future.result(), flush=True)
    print(f"LADDER SLICE PASS start={args.start_index} count={args.count}",
          flush=True)


if __name__ == "__main__":
    main()
