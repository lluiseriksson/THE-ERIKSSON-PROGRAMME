"""Run the fixed-width continuation of the K4 candidate t ladder."""

from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_surface_remainder_k4_t_box_probe.py"
BOXES = (
    ("delta0040_t226_227", Fraction(113, 50), Fraction(227, 100)),
    ("delta0040_t227_228", Fraction(227, 100), Fraction(57, 25)),
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
    print("K4 REFINED CONTINUATION COMPLETE",
          "REPLAY" if replay else "PRODUCTION", flush=True)


if __name__ == "__main__":
    main()
