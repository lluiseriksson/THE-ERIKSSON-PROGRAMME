"""Over-order exact guard for the registered R7/R8 heads."""

from __future__ import annotations

import hashlib
from pathlib import Path
import platform
import subprocess

import sympy as sp

import surface_remainder_delta0_seventh_eighth_coefficient as exact


GUARD_RETAINED = 11


def verify_guard():
    original = exact.RETAINED
    try:
        exact.RETAINED = GUARD_RETAINED
        values = exact.derive_coefficients()
    finally:
        exact.RETAINED = original
    if len(values) != GUARD_RETAINED-1:
        raise AssertionError(len(values))
    c = sp.symbols("c", positive=True)
    targets = exact.frozen_targets(c)
    for order, target in enumerate(targets):
        difference = sp.cancel(values[order]-target)
        if difference != 0:
            raise AssertionError(
                f"guard mismatch at Y{order}: {difference}"
            )
    for order, value in enumerate(values):
        if value.has(sp.Float):
            raise AssertionError(f"Float contamination at Y{order}")
        numerator, denominator = sp.cancel(value).as_numer_denom()
        if denominator == 0 or value.has(sp.zoo, sp.nan, sp.oo):
            raise AssertionError(f"non-finite guard head Y{order}")
        if numerator == 0 and order >= 8:
            raise AssertionError(f"unexpected zero guard head Y{order}")
    return [sp.factor(value) for value in values]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest().upper()


def main():
    path = Path(__file__).resolve()
    root = path.parents[1]
    prereg = (
        root/"docs"/
        "SURFACE-REMAINDER-R7-R8-GUARD-PREREG-20260728.md"
    )
    dependency = (
        root/"scripts"/
        "surface_remainder_delta0_seventh_eighth_coefficient.py"
    )
    head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=root,
        text=True,
    ).strip()
    print("R7/R8 OVER-ORDER EXACT GUARD", flush=True)
    print(f"git_head {head}", flush=True)
    print(f"python {platform.python_version()}", flush=True)
    print(f"sympy {sp.__version__}", flush=True)
    print(f"guard_retained {GUARD_RETAINED}", flush=True)
    print(f"script_sha256 {digest(path)}", flush=True)
    print(f"prereg_sha256 {digest(prereg)}", flush=True)
    print(f"dependency_sha256 {digest(dependency)}", flush=True)
    values = verify_guard()
    for order, value in enumerate(values):
        print(f"Y{order} {value}", flush=True)
    print("R7/R8 OVER-ORDER EXACT GUARD PASS", flush=True)
    print(
        "SCOPE truncation stability only; K2 and manuscript open",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
