"""Independent replay of the frozen upper finite-G5 cover."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
from pathlib import Path
import subprocess
import sys

import certify_surface_right_edge_five_family_finite as cert

ROOT = Path(__file__).resolve().parents[1]


def output_path(unit):
    return ROOT / "scripts" / (
        "certify_surface_right_edge_five_family_finite_"
        f"{cert.unit_slug(unit)}_rerun_transcript.txt")


def run_one(unit, head, expected):
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" /
         "certify_surface_right_edge_five_family_finite.py"),
         "--unit", cert.unit_slug(unit)], cwd=ROOT,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=None)
    output_path(unit).write_bytes(result.stdout)
    if result.returncode:
        raise RuntimeError(f"upper finite rerun failed: {cert.unit_slug(unit)}")
    lines = result.stdout.decode("utf-8", "replace").splitlines()
    assert f"PROVENANCE git_head {head}" in lines
    deps = {line.split()[1]: line.split()[2] for line in lines
            if line.startswith("DEPENDENCY ")}
    assert deps == expected and "CERTIFICATE FAIL" not in lines
    return unit


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, choices=(1, 2, 4, 8), default=4)
    parser.add_argument("--max-units", type=int, default=None)
    args = parser.parse_args()
    head = cert.current_head()
    expected = {rel: hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()
                for rel in cert.DEPENDENCIES}
    pending = [unit for unit in cert.UNITS if not output_path(unit).exists()]
    if args.max_units is not None:
        pending = pending[:args.max_units]
    print("UPPER FINITE G5 INDEPENDENT RERUN head", head,
          "pending", len(pending), "workers", args.workers, flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_one, unit, head, expected): unit
                   for unit in pending}
        for count, future in enumerate(as_completed(futures), 1):
            print("UPPER FINITE G5 INDEPENDENT RERUN COMPLETE",
                  cert.unit_slug(future.result()), count, "of", len(pending),
                  flush=True)
    print("UPPER FINITE G5 INDEPENDENT RERUN COMPLETE", len(pending), flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
