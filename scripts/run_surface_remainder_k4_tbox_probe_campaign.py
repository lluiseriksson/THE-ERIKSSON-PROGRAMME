"""Bounded candidate-only K4 t-box production/replay campaign."""

from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_surface_remainder_k4_t_box_probe.py"
BOXES = (
    ("delta0040_t225_230", Fraction(11, 5), Fraction(23, 10)),
    ("delta0040_t230_240", Fraction(23, 10), Fraction(12, 5)),
)


def run_one(unit, tlo, thi, replay):
    suffix = "_rerun" if replay else ""
    out = ROOT / "scripts" / f"surface_remainder_k4_tbox_{unit}{suffix}.txt"
    command = [sys.executable, str(DRIVER),
               "--delta-lo", "1/25", "--delta-hi", "81/2000",
               "--t-lo", str(tlo), "--t-hi", str(thi),
               "--max-cells", "9216", "--precision", "140",
               "--output", str(out.relative_to(ROOT))]
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
    args = parser.parse_args()
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(run_one, unit, tlo, thi, args.replay)
                   for unit, tlo, thi in BOXES]
        for future in as_completed(futures):
            print(future.result(), flush=True)
    print("K4 T-BOX CAMPAIGN COMPLETE",
          "REPLAY" if args.replay else "PRODUCTION", len(BOXES), flush=True)


if __name__ == "__main__":
    main()
