"""Exact root-count and endpoint-sign audit for the R7/R8 design heads."""

from __future__ import annotations

import hashlib
import subprocess
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
PREREG = ROOT / "docs/SURFACE-REMAINDER-R7-R8-ROOT-PARTITION-PREREG-20260724.md"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_head() -> str:
    return subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
    ).strip()


def sign(value: sp.Expr) -> int:
    return int(sp.sign(value))


def main() -> int:
    x = sp.symbols("x")
    p7 = sp.Poly(
        2085412*x**7 + 6775103*x**6 + 11636676*x**5 - 52644752*x**4
        + 1046587520*x**3 - 2880628992*x**2 + 2254849024*x - 513015808,
        x,
        domain=sp.ZZ,
    )
    p8 = sp.Poly(
        19936*x**8 + 119595*x**7 + 323054*x**6 + 637408*x**5
        - 12653880*x**4 + 104539328*x**3 - 219463616*x**2
        + 153352416*x - 33064504,
        x,
        domain=sp.ZZ,
    )
    lo, hi = sp.Rational(1, 2), sp.Rational(1)
    cages = {
        "R7": (p7, sp.Rational(7105, 10000), sp.Rational(7106, 10000)),
        "R8": (p8, sp.Rational(6822, 10000), sp.Rational(6823, 10000)),
    }

    print("R7/R8 EXACT ROOT-PARTITION AUDIT")
    print(f"git_head {git_head()}")
    print("python_sympy", sp.__version__)
    print(f"dependency {PREREG.relative_to(ROOT).as_posix()} sha256 {digest(PREREG)}")
    script = Path(__file__)
    print(f"dependency {script.relative_to(ROOT).as_posix()} sha256 {digest(script)}")
    for name, (poly, cage_lo, cage_hi) in cages.items():
        total = sp.polys.polytools.count_roots(poly, lo, hi)
        in_cage = sp.polys.polytools.count_roots(poly, cage_lo, cage_hi)
        assert total == 1, (name, total)
        assert in_cage == 1, (name, in_cage)
        endpoint_signs = (sign(poly.eval(lo)), sign(poly.eval(hi)))
        cage_signs = (sign(poly.eval(cage_lo)), sign(poly.eval(cage_hi)))
        assert endpoint_signs == (1, -1), (name, endpoint_signs)
        assert cage_signs == (1, -1), (name, cage_signs)
        print(
            f"{name} roots_[1/2,1]={total} roots_cage={in_cage} "
            f"cage=[{cage_lo},{cage_hi}] "
            f"endpoint_signs={endpoint_signs} cage_endpoint_signs={cage_signs}"
        )
    print("R7/R8 ROOT-PARTITION AUDIT PASS")
    print("SCOPE exact root isolation only; no majorant or G2 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
