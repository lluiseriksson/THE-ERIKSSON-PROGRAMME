"""Production/replay runner for the preregistered K4 band."""

import argparse
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_surface_remainder_k4_centered_00280_00285.py"
UNIT = "k4_00280_00285"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    suffix = "_rerun" if args.replay else ""
    out = ROOT / "scripts" / f"surface_remainder_k4_{UNIT}{suffix}.txt"
    tmp = out.with_suffix(f".{os.getpid()}.tmp")
    result = subprocess.run([sys.executable, str(DRIVER)], cwd=ROOT,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True,
                            timeout=None)
    tmp.write_text(result.stdout, encoding="utf-8")
    if result.returncode:
        tmp.replace(out.with_suffix(".failed.txt"))
        raise SystemExit(result.returncode)
    tmp.replace(out)
    print("K4 CENTERED", UNIT,
          "REPLAY" if args.replay else "PRODUCTION", "PASS")


if __name__ == "__main__":
    main()
