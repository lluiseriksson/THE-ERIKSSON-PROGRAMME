"""Run/replay the frozen order-13 scaled-bulk [36,37] candidate."""

import argparse
from pathlib import Path
import subprocess
import sys

import certify_surface_scaled_bulk_36_37_candidate as cert

ROOT = Path(__file__).resolve().parents[1]


def path(suffix: str = "") -> Path:
    return ROOT / "scripts" / f"surface_scaled_bulk_36_37{suffix}.txt"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    suffix = "_rerun" if args.replay else ""
    target = path(suffix)
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" /
         "certify_surface_scaled_bulk_36_37_candidate.py")],
        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=None)
    target.write_bytes(result.stdout)
    if result.returncode:
        raise RuntimeError("order-13 scaled-bulk candidate failed")
    print("SCALED BULK [36,37] CANDIDATE",
          "REPLAY" if args.replay else "PRODUCTION", "COMPLETE")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
