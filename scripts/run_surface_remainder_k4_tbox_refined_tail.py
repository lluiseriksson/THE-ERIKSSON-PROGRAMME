"""Run the fixed-width K4 t-box tail continuation."""

from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_surface_remainder_k4_t_box_probe.py"
BOXES = (
    ("delta0040_t228_229", Fraction(57, 25), Fraction(229, 100)),
    ("delta0040_t229_230", Fraction(229, 100), Fraction(23, 10)),
)


def run_one(unit, tlo, thi, replay):
    suffix = "_rerun" if replay else ""
    out = ROOT / "scripts" / f"surface_remainder_k4_tbox_{unit}{suffix}.txt"
    command = [sys.executable, str(DRIVER),
               "--delta-lo", "1/25", "--delta-hi", "81/2000",
               "--t-lo", str(tlo), "--t-hi", str(thi),
               "--max-cells", "9216", "--precision", "140",
               "--output", str(out.relative_to(ROOT))]
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=None)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout.strip()


def main():
    replay = "--replay" in sys.argv
    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [pool.submit(run_one, unit, tlo, thi, replay)
                   for unit, tlo, thi in BOXES]
        for future in as_completed(futures):
            print(future.result(), flush=True)
    print("K4 REFINED TAIL COMPLETE", "REPLAY" if replay else "PRODUCTION",
          flush=True)


if __name__ == "__main__":
    main()
