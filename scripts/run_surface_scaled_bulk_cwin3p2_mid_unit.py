"""Run the preregistered mid-order unit, optionally as its replay."""

from pathlib import Path
import argparse
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_mid.py"
UNIT = "gap_765_16_193_4"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    suffix = "_rerun" if args.replay else ""
    output = ROOT / "scripts" / f"surface_scaled_bulk_{UNIT}{suffix}.txt"
    completed = subprocess.run(
        [sys.executable, str(DRIVER)], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=None,
    )
    output.write_text(completed.stdout, encoding="utf-8")
    if completed.returncode:
        return completed.returncode
    print("CWIN3P2 MID", "REPLAY" if args.replay else "PRODUCTION", "PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
