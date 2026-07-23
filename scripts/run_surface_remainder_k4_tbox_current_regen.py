"""Regenerate the candidate K4 t-box ladder against current dependencies.

Outputs use ``_current_regen`` names so the historical candidate transcripts
are never overwritten.  The companion comparison step must decide whether a
replacement is admissible; this runner itself never promotes K4.
"""

from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_surface_remainder_k4_t_box_probe.py"
PI_HI = Fraction(31415927, 10_000_000)
BOXES = [(f"{i:03d}_{i+1:03d}", Fraction(i, 100), Fraction(i + 1, 100))
         for i in range(300, 314)] + [("314_pi", Fraction(157, 50), PI_HI)]


def run_one(unit: str, tlo: Fraction, thi: Fraction, replay: bool) -> str:
    suffix = "_rerun" if replay else ""
    out = ROOT / "scripts" / f"surface_remainder_k4_tbox_{unit}_20260723_current_regen{suffix}.txt"
    command = [sys.executable, str(DRIVER),
               "--delta-lo", "1/25", "--delta-hi", "81/2000",
               "--t-lo", str(tlo), "--t-hi", str(thi),
               "--max-cells", "2304", "--precision", "140",
               "--output", str(out.relative_to(ROOT))]
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=None)
    if result.returncode:
        raise RuntimeError(f"{unit}: {result.stdout}")
    return result.stdout.strip()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--workers", type=int, choices=(1, 2, 3, 4), default=3)
    args = parser.parse_args()
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(run_one, unit, lo, hi, args.replay)
                   for unit, lo, hi in BOXES]
        for future in as_completed(futures):
            print(future.result(), flush=True)
    print("K4 CURRENT REGEN COMPLETE", "REPLAY" if args.replay else "PRODUCTION",
          len(BOXES), flush=True)


if __name__ == "__main__":
    main()
