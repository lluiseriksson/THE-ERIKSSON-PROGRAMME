"""Production/replay driver for the R6 exact-outer tenth-birth lane."""

import argparse
import hashlib
import platform
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import flint
from flint import arb, ctx

import probe_surface_remainder_r6_companion_charge as exact
import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_r4_extension_010_hybrid_contract as contract
import surface_remainder_delta0_r6_extension_010_cover as cover


ROOT = Path(__file__).resolve().parents[1]
TARGET = 7600


def _hash(path):
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest().upper()


def row(index):
    ctx.prec = 140
    radius, coefficient5, value, margin = (
        __import__("surface_remainder_delta0_r6_exact_outer_three_witness",
                   fromlist=["judge"]).judge(index))
    return {
        "index": index,
        "radius": str(radius),
        "coefficient5": coefficient5.str(40),
        "value_charge": value.str(40),
        "margin_lower": arb(margin.lower()).str(40),
        "passed": bool(arb(margin.lower()) > 0),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--stop", type=int, default=None)
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    boxes = list(regular.sealed.born_t_boxes())
    stop = len(boxes) if args.stop is None else args.stop
    if not (0 <= args.start < stop <= len(boxes)):
        raise ValueError("invalid born-box slice")
    print("R6 EXACT-OUTER PRODUCTION", flush=True)
    print("PROVENANCE script_sha256=" + _hash(
        "scripts/certify_surface_remainder_r6_exact_outer_010.py"), flush=True)
    print("PROVENANCE judge_sha256=" + _hash(
        "scripts/surface_remainder_delta0_r6_exact_outer_three_witness.py"), flush=True)
    print("PROVENANCE cover_sha256=" + _hash(
        "scripts/surface_remainder_delta0_r6_extension_010_cover.py"), flush=True)
    print("PROVENANCE split_outer_sha256=" + _hash(
        "scripts/surface_remainder_delta0_outer_domain_r6split.py"), flush=True)
    print("PROVENANCE exact_integral_sha256=" + _hash(
        "scripts/probe_surface_remainder_r6_exact_box_integral.py"), flush=True)
    print("PROVENANCE companion_sha256=" + _hash(
        "scripts/probe_surface_remainder_r6_companion_charge.py"), flush=True)
    print("PROVENANCE contract_sha256=" + _hash(
        "scripts/surface_remainder_delta0_r4_extension_010_hybrid_contract.py"), flush=True)
    print("PROVENANCE python=" + platform.python_version(), flush=True)
    print("PROVENANCE flint=" + getattr(flint, "__version__", "UNKNOWN"), flush=True)
    print(f"CONFIG start={args.start} stop={stop} workers={args.workers} "
          f"target={TARGET} delta=0:1/100", flush=True)
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        rows = list(pool.map(row, range(args.start, stop)))
    for result in rows:
        print("ROW", result["index"], "radius", result["radius"],
              "Y5", result["coefficient5"], "value", result["value_charge"],
              "margin_lower", result["margin_lower"],
              "PASS" if result["passed"] else "FAIL", flush=True)
    passed = all(result["passed"] for result in rows)
    print("ROWS", len(rows), "PASS_COUNT",
          sum(result["passed"] for result in rows), flush=True)
    print("R6 EXACT-OUTER PRODUCTION PASS" if passed
          else "R6 EXACT-OUTER PRODUCTION FAIL", flush=True)
    print("SCOPE design-only; no G2/G6 promotion", flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
