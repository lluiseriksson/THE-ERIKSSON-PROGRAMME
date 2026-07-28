"""Check the frozen R7/R8 targets with the sparse exact series engine."""

from __future__ import annotations

import hashlib
from pathlib import Path
import platform
import subprocess
import sys

import sympy as sp

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import derive_surface_remainder_delta0_r7_design as sparse
from surface_remainder_delta0_exact_targets import (
    frozen_targets,
)


def verify():
    c = sp.symbols("c", positive=True)
    values = sparse.derive()
    targets = frozen_targets(c)
    if len(values) != 8:
        raise AssertionError(len(values))
    for order, (value, target) in enumerate(zip(values, targets)):
        if value.has(sp.Float):
            raise AssertionError(f"Float contamination at Y{order}")
        difference = sp.cancel(value-target)
        if difference != 0:
            raise AssertionError(
                f"sparse target mismatch Y{order}: {difference}"
            )
    return [sp.factor(value) for value in values]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest().upper()


def main():
    path = Path(__file__).resolve()
    root = path.parents[1]
    dependency = root/"scripts"/"derive_surface_remainder_delta0_r7_design.py"
    prereg = (
        root/"docs"/
        "SURFACE-R7-R8-LIST-TARGET-CHECK-PREREG-20260728.md"
    )
    head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=root,
        text=True,
    ).strip()
    print("R7/R8 SPARSE EXACT TARGET CHECK")
    print("git_head", head)
    print("python", platform.python_version())
    print("sympy", sp.__version__)
    print("script_sha256", digest(path))
    print("dependency_sha256", digest(dependency))
    print("prereg_sha256", digest(prereg))
    values = verify()
    for order, value in enumerate(values):
        print(f"Y{order} {value}")
    print("R7/R8 SPARSE EXACT TARGET CHECK PASS")
    print(
        "SCOPE single exact symbolic engine plus replay; "
        "independent numerical corroboration and K2 remain open"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
