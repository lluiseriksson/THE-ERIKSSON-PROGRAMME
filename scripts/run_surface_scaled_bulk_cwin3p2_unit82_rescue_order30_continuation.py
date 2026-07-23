"""Run the remaining three order-30 unit-82 rescue beta slices."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts/run_surface_scaled_bulk_cwin3p2_unit82_rescue_order30_slice.py"
SLICES = (
    ("slice2", Fraction(1101, 16), Fraction(1103, 16)),
    ("slice3", Fraction(1103, 16), Fraction(1104, 16)),
)


def run_one(label: str, lo: Fraction, hi: Fraction, replay: bool) -> str:
    suffix = "_rerun" if replay else ""
    out = ROOT / "scripts" / f"surface_scaled_bulk_unit82_rescue_order30_{label}{suffix}.txt"
    command = [sys.executable, str(DRIVER), "--beta-lo", str(lo),
               "--beta-hi", str(hi), "--output", str(out.relative_to(ROOT))]
    if replay:
        command.append("--replay")
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=None)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout.strip()


def main() -> None:
    replay = "--replay" in sys.argv[1:]
    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [pool.submit(run_one, label, lo, hi, replay)
                   for label, lo, hi in SLICES]
        for future in as_completed(futures):
            print(future.result(), flush=True)
    print("UNIT82 RESCUE CONTINUATION COMPLETE", "REPLAY" if replay else "PRODUCTION")


if __name__ == "__main__":
    main()
