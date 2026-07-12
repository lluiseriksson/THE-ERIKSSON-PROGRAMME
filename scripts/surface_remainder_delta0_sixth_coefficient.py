"""Exact sixth coefficient of the regularized S2 carrier."""

import hashlib
from pathlib import Path
import platform
import subprocess

import sympy as sp

from derive_surface_remainder_delta0_sixth_fast import derive_coefficients


def target_y5(c):
    return ((8148*c**12+17095*c**10+10768*c**8+634576*c**6
             -2557408*c**4+2283296*c**2-549376)/(131072*c**18))


def derive():
    c = sp.symbols("c", positive=True)
    coefficient = derive_coefficients()[5]
    assert sp.simplify(coefficient-target_y5(c)) == 0
    return sp.factor(coefficient)


def check():
    path = Path(__file__).resolve()
    root = path.parents[1]
    dependency = root/"scripts"/"derive_surface_remainder_delta0_sixth_fast.py"
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    print("PROVENANCE script=scripts/"+path.name, flush=True)
    print("PROVENANCE script_sha256="
          +hashlib.sha256(path.read_bytes()).hexdigest(), flush=True)
    print("PROVENANCE dependency_sha256="
          +hashlib.sha256(dependency.read_bytes()).hexdigest(), flush=True)
    print("PROVENANCE git_head="+head, flush=True)
    print("PROVENANCE python="+platform.python_version(), flush=True)
    print("PROVENANCE sympy="+sp.__version__, flush=True)
    print("Y delta coefficient 5 =", derive(), flush=True)
    print("TARGET MATCH: sixth coefficient r6(c)", flush=True)


if __name__ == "__main__":
    check()
