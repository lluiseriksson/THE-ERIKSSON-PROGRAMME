"""Degree-eight fixed-square complex geometry at the registered radius."""

from __future__ import annotations

import hashlib
from pathlib import Path
import platform
import subprocess

from flint import arb, ctx

from surface_bessel_integral_remainder import relative_coefficients


RHO = arb(17)/2000
SIDE = arb(12)
CMIN = arb(2).sqrt()/2
COMPANION_ORDER = 8


def polynomial_deviation(family, h_abs):
    coefficients = relative_coefficients(family, COMPANION_ORDER)
    return sum(
        (
            arb(abs(coefficient.numerator))/coefficient.denominator
            * h_abs**order
            for order, coefficient in enumerate(coefficients[1:], 1)
        ),
        arb(0),
    )


def bounds():
    sine_argument = RHO.sqrt()*SIDE/2
    p_abs = sine_argument.sinh()**2
    d_floor = 2*(1-2*p_abs)
    radicand_deviation = 2*p_abs+p_abs**2/CMIN**2
    root_floor = (1-radicand_deviation).sqrt()
    root_from_one = radicand_deviation/(1+root_floor)
    one_plus_root_floor = 2-root_from_one
    h_abs = RHO/(4*CMIN*root_floor)
    a_deviation = polynomial_deviation("A", h_abs)
    b_deviation = polynomial_deviation("B", h_abs)
    return {
        "p_abs": p_abs,
        "d_floor": d_floor,
        "radicand_deviation": radicand_deviation,
        "root_floor": root_floor,
        "one_plus_root_floor": one_plus_root_floor,
        "h_abs": h_abs,
        "a_floor": 1-a_deviation,
        "b_floor": 1-b_deviation,
    }


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest().upper()


def main():
    ctx.prec = 180
    values = bounds()
    assert values["p_abs"] < arb("0.35")
    assert values["d_floor"] > arb("0.64")
    assert values["radicand_deviation"] < arb("0.92")
    assert values["root_floor"] > arb("0.30")
    assert values["one_plus_root_floor"] > arb("1.30")
    assert values["a_floor"] > arb("0.995")
    assert values["b_floor"] > arb("0.98")
    path = Path(__file__).resolve()
    root = path.parents[1]
    prereg = (
        root/"docs"/
        "SURFACE-K2-R8-COMPLEX-GEOMETRY-PREREG-20260728.md"
    )
    head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=root,
        text=True,
    ).strip()
    print("K2 R8 FIXED-SQUARE COMPLEX GEOMETRY")
    print("git_head", head)
    print("python", platform.python_version())
    print("script_sha256", digest(path))
    print("prereg_sha256", digest(prereg))
    print("rho", RHO, "side", SIDE)
    for name, value in values.items():
        print(name, value)
    print(
        "K2 R8 FIXED-SQUARE COMPLEX GEOMETRY PASS; "
        "INTEGRATED KD, TRUE COMPANION, AND EXTERIOR OPEN"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
