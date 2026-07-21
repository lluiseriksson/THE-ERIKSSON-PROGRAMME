"""Run the preregistered high-order [74,78] boxes with bounded parallelism."""

from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
import argparse
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "scripts" / "run_surface_scaled_bulk_cwin3p2_high_unit.py"


def label(value: Fraction) -> str:
    text = f"{float(value):.8f}".rstrip("0").rstrip(".")
    return text.replace(".", "p")


BOXES = tuple(
    (f"high_{label(Fraction(74) + Fraction(i, 4))}_"
     f"{label(Fraction(74) + Fraction(i + 1, 4))}",
     Fraction(74) + Fraction(i, 4), Fraction(74) + Fraction(i + 1, 4))
    for i in range(16)
)


def run_one(unit: str, lo: Fraction, hi: Fraction, replay: bool, skip: bool) -> str:
    suffix = "_rerun" if replay else ""
    out = ROOT / "scripts" / f"surface_scaled_bulk_{unit}{suffix}.txt"
    if skip and out.is_file():
        return f"SKIP {unit} {'REPLAY' if replay else 'PRODUCTION'}"
    command = [sys.executable, str(RUNNER), "--unit", unit,
               "--lo", str(lo), "--hi", str(hi)]
    if replay:
        command.append("--replay")
    completed = subprocess.run(command, cwd=ROOT, text=True,
                               stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=None)
    if completed.returncode:
        failed = out.with_suffix(".failed.txt")
        failed.write_text(completed.stdout, encoding="utf-8")
        raise RuntimeError(f"{unit} failed; see {failed.name}")
    return f"PASS {unit} {'REPLAY' if replay else 'PRODUCTION'}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--workers", type=int, choices=(1, 2), default=2)
    parser.add_argument("--skip-existing", action="store_true")
    parser.add_argument("--start-index", type=int, default=0)
    parser.add_argument("--stop-index", type=int, default=len(BOXES))
    args = parser.parse_args()
    if not 0 <= args.start_index <= args.stop_index <= len(BOXES):
        parser.error("invalid campaign index range")
    selected = BOXES[args.start_index:args.stop_index]
    done = 0
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(run_one, unit, lo, hi, args.replay,
                               args.skip_existing)
                   for unit, lo, hi in selected]
        for future in as_completed(futures):
            done += 1
            print(f"CAMPAIGN {done}/{len(selected)} {future.result()}",
                  flush=True)
    print("CAMPAIGN COMPLETE", "REPLAY" if args.replay else "PRODUCTION",
          len(selected), flush=True)


if __name__ == "__main__":
    main()
