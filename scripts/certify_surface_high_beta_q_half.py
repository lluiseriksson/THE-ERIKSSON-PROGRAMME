"""Certified high-beta lower bound for <Phi>/<D>.

This reuses the four analytic charges of the proved signed-mass lemma, but
assembles them against ``Phi-D/2`` instead of against ``D``.  With

    P = sin(s/2)^2, Q = sin(alpha/2)^2,

For ``h=19/20``, symmetry of the positive kernel gives, on the main
rectangle,

    Phi_sym-h*D >= (2-2h)-(6-2h)(P+Q).

On the mirror rectangle, in the local variables P',Q',

    Phi_sym-h*D >= (2+2h)-(12+4h)p+12p^2 > 0,

where p=sin(3/5)^2 and the last expression is the exact box minimum.
Globally, completing the square gives

    Phi_sym-h*D >= -1-h^2/3.

Consequently the existing main-mass lower bound L and the upper charges
G and R for the main weighted mass and remaining mass imply

    <Phi>-h<D> >= (2-2h)L-(6-2h)G-(1+h^2/3)R.

The sweep below certifies that this quantity is positive for
beta >= 1000/9 and 0<t<=pi-3/(2 beta).  Division is performed only after
the already certified strict positivity of <D>; no quotient of independent
interval bounds is used.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import math
from pathlib import Path
import platform
import sys

import flint
from flint import arb, ctx


ctx.prec = 160

ROOT = Path(__file__).resolve().parents[1]
MASS_SCRIPT = ROOT / "scripts" / "cascade1_floor_arb.py"

BETA0 = Fraction(1000, 9)
CWIN = Fraction(3, 2)
TARGET = Fraction(19, 20)
PI_UP = Fraction(31415927, 10000000)
RADIUS = Fraction(6, 5)


def aq(value: Fraction | int) -> arb:
    value = Fraction(value)
    return arb(value.numerator) / arb(value.denominator)


def interval(lo: Fraction | float, hi: Fraction | float) -> arb:
    lo_ball = aq(lo) if isinstance(lo, Fraction) else arb(str(lo))
    hi_ball = aq(hi) if isinstance(hi, Fraction) else arb(str(hi))
    return (lo_ball + hi_ball) / 2 + (hi_ball - lo_ball) / 2 * arb("0 +/- 1")


def lower(value: arb) -> arb:
    return arb(value.lower())


def upper(value: arb) -> arb:
    return arb(value.upper())


CABS_B = arb("1.089")
CABS_M = arb("1.230")
CP = arb("0.2214")
FLB = arb("0.6811")
RB = aq(RADIUS)
P_EDGE = (RB / 2).sin() ** 2
WMAX = 2 * P_EDGE
SQ2PI = (2 * arb.pi()).sqrt()
PR2 = (RB / 2).sin() ** 4
TARGET_ARB = aq(TARGET)
MAIN_CONSTANT = 2 - 2 * TARGET_ARB
MAIN_WEIGHT = 6 - 2 * TARGET_ARB
MIRROR_POINTWISE = (
    2 + 2 * TARGET_ARB
    - (12 + 4 * TARGET_ARB) * P_EDGE
    + 12 * P_EDGE**2
)
GLOBAL_LOSS = 1 + TARGET_ARB**2 / 3


def rest_mass_upper(beta: arb, c: arb, bc: arb, zs: arb) -> arb:
    """The Abel-corrected REST mass charge from cascade 1."""

    def area_rest(v: Fraction) -> arb:
        av = aq(v)
        branch_b = 4 * arb.pi() ** 3 * av
        if v < Fraction(1, 2):
            branch_a = 16 * arb.pi() * av / (1 - 2 * av).sqrt()
            if bool(branch_a < branch_b):
                return branch_a - arb("4.006")
        return branch_b - arb("4.006")

    def phi(v: Fraction) -> arb:
        av = aq(v)
        return (1 - av) ** arb("-0.75") * (-2 * bc * av).exp()

    v0 = Fraction(159, 500)
    step = Fraction(1, 50)
    stop = Fraction(9, 10)
    v = min(v0 + step, stop)
    total = phi(v0) * area_rest(v)
    while v < stop:
        next_v = min(v + step, stop)
        total += phi(v) * (area_rest(next_v) - area_rest(v))
        v = next_v
    prefactor = beta / (4 * SQ2PI) / c ** arb("1.5")
    shard = (
        (2 * arb.pi()) ** 2
        * beta ** arb("2.5")
        * (-(1 - arb("0.1").sqrt()) * zs).exp()
    )
    return prefactor * total + shard


def charges(t: arb, beta: arb) -> tuple[arb, arb, arb, arb]:
    """Return (L,G,M,R) in the common scaled mass units."""
    c = (t / 4).cos()
    s4 = (t / 4).sin()
    zs = 4 * beta * c
    bc = beta * c
    delta4 = c - s4

    bracket_1 = 1 - 3 / (8 * zs) - arb("0.6") / zs**2
    bracket_2 = 1 - (-bc * RB**2 / 2).exp() - 3 / (8 * bc)
    main_lower = (
        (SQ2PI / 4)
        / c ** arb("2.5")
        * bracket_1
        * bracket_2**2
    )

    rate = CP * arb("1.9") * FLB * bc
    main_weighted = (
        beta
        / (4 * SQ2PI)
        / c ** arb("1.5")
        * CABS_B
        * (arb.pi() / 4)
        / rate**2
    )

    if lower(s4) >= arb("0.58"):
        q4 = WMAX / (4 * s4**2)
        mirror_rate = CP * arb("1.9") * (1 - q4) * beta * s4
        mirror = (
            beta
            / (4 * SQ2PI)
            / s4 ** arb("1.5")
            * CABS_M
            * arb.pi()
            / mirror_rate
            * (-4 * beta * delta4).exp()
        )
    elif lower(s4) >= arb("0.40"):
        mirror = (
            4
            * RB**2
            * beta ** arb("2.5")
            * (-4 * beta * delta4).exp()
        )
    else:
        far_deficit = c - (c * c * PR2 + s4 * s4).sqrt()
        mirror = (
            4
            * RB**2
            * beta ** arb("2.5")
            * (-4 * beta * far_deficit).exp()
        )

    rest = rest_mass_upper(beta, c, bc, zs)
    return main_lower, main_weighted, mirror, rest


def target_margin(t: arb, beta: arb) -> arb:
    main_lower, main_weighted, mirror, rest = charges(t, beta)
    del mirror
    if lower(MIRROR_POINTWISE) <= 0:
        raise AssertionError("registered mirror pointwise margin is not positive")
    return (
        lower(MAIN_CONSTANT * main_lower)
        - upper(MAIN_WEIGHT * main_weighted)
        - upper(GLOBAL_LOSS * rest)
    )


def deep_edge_margin() -> arb:
    """Direct x=pi-t substitution on 0<x<=1e-3."""
    x = interval(Fraction(0), Fraction(1, 1000))
    t = arb.pi() - x
    c = (t / 4).cos()
    s4 = (t / 4).sin()

    bracket_1 = 1 - x / (16 * c) - arb("0.6") * x**2 / (36 * c**2)
    bracket_2 = 1 - interval(Fraction(0), Fraction(1, 10**300)) - x / (4 * c)
    main_lower = (
        (SQ2PI / 4)
        / c ** arb("2.5")
        * bracket_1
        * bracket_2**2
    )

    # main_weighted = C/(beta*c^(7/2)), beta=3/(2x)
    weighted_coefficient = (
        (1 / (4 * SQ2PI))
        * CABS_B
        * (arb.pi() / 4)
        / (CP * arb("1.9") * FLB) ** 2
    )
    main_weighted = weighted_coefficient * (2 * x / 3) / c ** arb("3.5")

    q4 = WMAX / (4 * s4**2)
    mirror_rate_without_beta = CP * arb("1.9") * (1 - q4) * s4
    suppression = (
        -(aq(CWIN) * arb(2).sqrt()) * (1 - x**2 / 96)
    ).exp()
    mirror = (
        1
        / (4 * SQ2PI)
        / s4 ** arb("1.5")
        * CABS_M
        * arb.pi()
        / mirror_rate_without_beta
        * suppression
    )

    # The identical deep-edge estimate used by the signed-mass certificate.
    rest = interval(Fraction(0), Fraction(1, 10**180))
    del mirror
    return (
        lower(MAIN_CONSTANT * main_lower)
        - upper(MAIN_WEIGHT * main_weighted)
        - upper(GLOBAL_LOSS * rest)
    )


def certify() -> dict[str, object]:
    worst = arb(10)
    worst_label = ""
    passed = True

    # For fixed t every adverse charge decreases with beta, while L increases.
    # Hence beta=BETA0 owns t<=pi-CWIN/BETA0.
    t_max = PI_UP - CWIN / BETA0
    count_a = 800
    for index in range(count_a):
        lo = t_max * index / count_a
        hi = t_max * (index + 1) / count_a
        value = target_margin(interval(lo, hi), aq(BETA0))
        if lower(value) <= 0:
            passed = False
        if lower(value) < lower(worst):
            worst, worst_label = value, f"A:{index}"

    # On the moving path beta=CWIN/x, use enclosing (t,beta) boxes.
    x_min = 1e-3
    x_max = float(CWIN / BETA0)
    count_b = 80
    for index in range(count_b):
        lo = x_min * ((x_max / x_min) ** (index / count_b))
        hi = x_min * ((x_max / x_min) ** ((index + 1) / count_b))
        t_box = arb.pi() - interval(lo, hi)
        beta_box = interval(
            math.nextafter(1.5 / hi, 0.0),
            math.nextafter(1.5 / lo, math.inf),
        )
        value = target_margin(t_box, beta_box)
        if lower(value) <= 0:
            passed = False
        if lower(value) < lower(worst):
            worst, worst_label = value, f"B:{index}"

    value_c = deep_edge_margin()
    if lower(value_c) <= 0:
        passed = False
    if lower(value_c) < lower(worst):
        worst, worst_label = value_c, "C"

    return {
        "passed": passed,
        "segment_a_boxes": count_a,
        "segment_b_boxes": count_b,
        "deep_edge_boxes": 1,
        "worst": worst,
        "worst_label": worst_label,
        "target": TARGET,
        "mirror_pointwise": MIRROR_POINTWISE,
    }


def provenance() -> dict[str, str]:
    path = Path(__file__).resolve()
    return {
        "script": str(path.relative_to(ROOT)).replace("\\", "/"),
        "script_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "cascade1_floor_arb_sha256": hashlib.sha256(
            MASS_SCRIPT.read_bytes()
        ).hexdigest(),
        "python": platform.python_version(),
        "python_flint": getattr(flint, "__version__", "UNKNOWN"),
        "arb_prec_bits": str(ctx.prec),
    }


def main() -> int:
    for key, value in provenance().items():
        print(f"PROVENANCE {key}={value}")
    result = certify()
    print(
        "CONFIG beta>=1000/9 t=(0,pi-3/(2beta)] "
        "main_boxes=800 moving_boxes=80 deep_edge=1"
    )
    print(f"TARGET_Q {result['target']}")
    print(f"MIRROR_POINTWISE {result['mirror_pointwise'].str(30)}")
    print(
        f"WORST label={result['worst_label']} "
        f"margin={result['worst'].str(30)}"
    )
    if result["passed"]:
        print(
            "CERTIFIED: <Phi>-(19/20)<D>>0 on the complete high-beta "
            "relay; with <D>>0, <Phi>/<D>>19/20"
        )
        return 0
    print("FAILED: high-beta Q-half margin is not strictly positive")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
