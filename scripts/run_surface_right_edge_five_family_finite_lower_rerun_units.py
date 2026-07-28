"""Independent replay of the frozen lower finite-G5 production units.

The replay writes ``*_rerun_transcript.txt`` and never overwrites the
authoritative production transcripts.  It is intentionally a fresh process
per unit so the rerun can be compared cell-by-cell after completion.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
from pathlib import Path
import subprocess
import sys

import certify_surface_right_edge_five_family_finite_lower as cert
ROOT = Path(__file__).resolve().parents[1]


def output_path(unit):
    return ROOT / "scripts" / (
        "certify_surface_right_edge_five_family_finite_lower_"
        f"{cert.unit_slug(unit)}_rerun_transcript.txt")


def run_one(unit, head, expected):
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" /
         "certify_surface_right_edge_five_family_finite_lower.py"),
         "--unit", cert.unit_slug(unit)], cwd=ROOT,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=None)
    path = output_path(unit)
    path.write_bytes(result.stdout)
    if result.returncode:
        raise RuntimeError(f"independent lower rerun failed: {cert.unit_slug(unit)}")
    lines = result.stdout.decode("utf-8", "replace").splitlines()
    assert f"PROVENANCE git_head {head}" in lines
    deps = {line.split()[1]: line.split()[2] for line in lines
            if line.startswith("DEPENDENCY ")}
    assert deps == expected
    assert "CERTIFICATE FAIL" not in lines
    return unit


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-units", type=int, default=None)
    parser.add_argument("--workers", type=int, choices=(1, 2, 4, 8), default=4)
    args = parser.parse_args()
    head = cert.current_head()
    expected = {
        rel: hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()
        for rel in cert.DEPENDENCIES
    }
    pending = []
    for unit in cert.UNITS:
        path = output_path(unit)
        if path.exists():
            continue
        pending.append(unit)
    if args.max_units is not None:
        pending = pending[:args.max_units]
    print("LOWER FINITE G5 INDEPENDENT RERUN head", head,
          "pending", len(pending), flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_one, unit, head, expected): unit
                   for unit in pending}
        for future in as_completed(futures):
            unit = future.result()
            print("LOWER FINITE G5 INDEPENDENT RERUN COMPLETE",
                  cert.unit_slug(unit), flush=True)
    print("LOWER FINITE G5 INDEPENDENT RERUN COMPLETE", len(pending), flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
