"""Resumable one-beta-interval production for the scaled-left bridge."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import os
from pathlib import Path
import subprocess
import sys

import surface_finite_beta_scaled_partition as partition
import certify_surface_finite_beta_scaled_left as cert


ROOT = Path(__file__).resolve().parents[1]


def output_path(index):
    return ROOT / "scripts" / (
        f"certify_surface_finite_beta_scaled_left_beta_index_{index:04d}_transcript.txt")


def label(index):
    return f"beta_index_{index:04d}"


def complete(index, head):
    path = output_path(index)
    if not path.exists():
        return False
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    deps = {line.split()[1]: line.split()[2] for line in lines
            if line.startswith("DEPENDENCY ")}
    expected = {relative: hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
                for relative in cert.DEPENDENCIES}
    return (f"PROVENANCE git_head {head}" in lines
            and any(line.startswith(
                f"CERTIFIED FINITE-BETA SCALED LEFT UNIT {label(index)} 1")
                for line in lines)
            and not any("CERTIFICATE FAIL" in line for line in lines)
            and len([line for line in lines if line.startswith("ROW ")]) > 0
            and deps == expected)


def run_one(index, head):
    path = output_path(index)
    tmp = path.with_suffix(f".{os.getpid()}.tmp")
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" /
         "certify_surface_finite_beta_scaled_left.py"),
         "--beta-index", str(index)], cwd=ROOT,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=None)
    tmp.write_bytes(result.stdout)
    if result.returncode != 0:
        tmp.replace(path.with_suffix(".failed.txt"))
        raise RuntimeError(f"single scaled-left index {index} failed")
    tmp.replace(path)
    if not complete(index, head):
        raise RuntimeError(f"single scaled-left index {index} stale")
    return index


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, choices=(1, 2, 3, 4, 6, 8, 12, 16), default=1)
    parser.add_argument("--max-indices", type=int, default=None)
    args = parser.parse_args()
    head = cert.current_head()
    pending = [index for index in range(len(partition.BETA_INTERVALS))
               if not complete(index, head)]
    if args.max_indices is not None:
        pending = pending[:args.max_indices]
    print("SCALED LEFT SINGLE PRODUCTION LAUNCH head", head,
          "pending", len(pending), "workers", args.workers, flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_one, index, head): index for index in pending}
        for count, future in enumerate(as_completed(futures), 1):
            index = future.result()
            print("SCALED LEFT SINGLE UNIT COMPLETE", index,
                  count, "of", len(pending), flush=True)
    print("SCALED LEFT SINGLE PRODUCTION COMPLETE", len(pending), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
