"""Resumable launcher for the four compact G5 extension units."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import os
from pathlib import Path
import subprocess
import sys

import certify_right_edge_beta_taylor_cached_extension as cert


ROOT = Path(__file__).resolve().parents[1]


def output_path(unit):
    return ROOT/"scripts"/f"certify_right_edge_compact_extension_{unit}.txt"


def terminal(unit):
    return f"CERTIFIED RIGHT-EDGE COMPACT EXTENSION UNIT {unit} "


def current_head():
    return cert.current_head()


def complete(unit, head):
    path = output_path(unit)
    if not path.exists():
        return False
    content = path.read_text(encoding="utf-8", errors="replace")
    dependencies = {
        line.split()[1]: line.split()[2] for line in content.splitlines()
        if line.startswith("DEPENDENCY ")
    }
    expected = {
        relative: hashlib.sha256((ROOT/relative).read_bytes()).hexdigest()
        for relative in cert.DEPENDENCIES
    }
    return (f"PROVENANCE git_head {head}\n" in content
            and terminal(unit) in content
            and dependencies == expected)


def run_one(unit, head):
    path = output_path(unit)
    temporary = path.with_suffix(f".{os.getpid()}.tmp")
    result = subprocess.run(
        [sys.executable, str(ROOT/"scripts"/
         "certify_right_edge_beta_taylor_cached_extension.py"),
         "--unit", unit], cwd=ROOT, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=None)
    temporary.write_bytes(result.stdout)
    if result.returncode != 0:
        temporary.replace(path.with_suffix(".failed.txt"))
        raise RuntimeError(f"compact extension unit {unit} failed")
    temporary.replace(path)
    if not complete(unit, head):
        raise RuntimeError(f"compact extension unit {unit} stale")
    return unit


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, choices=(1, 2, 3), default=3)
    parser.add_argument("--max-units", type=int, default=None)
    args = parser.parse_args()
    head = current_head()
    pending = [unit for unit in cert.SEGMENTS if not complete(unit, head)]
    if args.max_units is not None:
        pending = pending[:args.max_units]
    print("COMPACT G5 EXTENSION LAUNCH pending", len(pending), "workers",
          args.workers, "head", head, flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_one, unit, head): unit for unit in pending}
        for count, future in enumerate(as_completed(futures), 1):
            unit = future.result()
            print("COMPACT G5 EXTENSION UNIT COMPLETE", unit, count, "of",
                  len(pending), flush=True)
    print("COMPACT G5 EXTENSION LAUNCH COMPLETE", len(pending), "new units",
          flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
