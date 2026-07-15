"""Independent replay of the 912 scaled-left finite-beta certificates."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
from pathlib import Path
import subprocess
import sys

import certify_surface_finite_beta_scaled_left as cert
import surface_finite_beta_scaled_partition as partition


ROOT = Path(__file__).resolve().parents[1]


def output_path(index):
    return ROOT / "scripts" / (
        f"certify_surface_finite_beta_scaled_left_beta_index_{index:04d}_rerun_transcript.txt")


def run_one(index, head, expected):
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" /
         "certify_surface_finite_beta_scaled_left.py"),
         "--beta-index", str(index)], cwd=ROOT,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=None)
    output_path(index).write_bytes(result.stdout)
    if result.returncode:
        raise RuntimeError(f"scaled-left independent rerun failed: {index}")
    lines = result.stdout.decode("utf-8", "replace").splitlines()
    assert f"PROVENANCE git_head {head}" in lines
    deps = {line.split()[1]: line.split()[2] for line in lines
            if line.startswith("DEPENDENCY ")}
    assert deps == expected and "CERTIFICATE FAIL" not in lines
    return index


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, choices=(1, 2, 4, 8, 16), default=8)
    parser.add_argument("--max-indices", type=int, default=None)
    args = parser.parse_args()
    head = cert.current_head()
    expected = {rel: hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()
                for rel in cert.DEPENDENCIES}
    pending = [i for i in range(len(partition.BETA_INTERVALS))
               if not output_path(i).exists()]
    if args.max_indices is not None:
        pending = pending[:args.max_indices]
    print("SCALED LEFT INDEPENDENT RERUN head", head,
          "pending", len(pending), "workers", args.workers, flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_one, i, head, expected): i for i in pending}
        for count, future in enumerate(as_completed(futures), 1):
            print("SCALED LEFT INDEPENDENT RERUN COMPLETE", future.result(),
                  count, "of", len(pending), flush=True)
    print("SCALED LEFT INDEPENDENT RERUN COMPLETE", len(pending), flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
