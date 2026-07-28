"""Paired-moment design probe for the high-beta scaled left edge."""

from fractions import Fraction
from math import comb, factorial
import sys

from flint import arb, ctx

import certify_bulk_beta_taylor_scaled_design as scaled


SPLICE = Fraction(19, 100)
BETA_ORDER = 20
T_ORDER = 20


def endpoint_fourier(box):
    fourier = {}
    zero = arb(0)
    for family in ("a", "b"):
        for q in range(BETA_ORDER+1):
            for r in range(T_ORDER+2):
                fourier[family, q, r] = box.box.fourier_derivative(
                    zero, q, r, family)
    return fourier


def moment(fourier, family: str, q: int, p: int):
    r = 2*p+1
    sign = -1 if p % 2 else 1
    return sign*fourier[family, q, r]


def paired_coefficient(fourier, q_beta: int, k: int) -> arb:
    out = arb(0)
    for p in range(k+1):
        q = k-p
        if p >= q:
            continue
        weight = (arb(1)/(arb(factorial(2*p))*arb(factorial(2*q+1)))
                  - arb(1)/(arb(factorial(2*p+1))*arb(factorial(2*q))))
        determinant = arb(0)
        for j in range(q_beta+1):
            determinant += arb(comb(q_beta, j))*(
                moment(fourier, "a", j, p)
                *moment(fourier, "b", q_beta-j, q)
                - moment(fourier, "a", j, q)
                *moment(fourier, "b", q_beta-j, p))
        out += weight*determinant
    return 2*((-1)**k)*out


def identity_regression(box, fourier):
    for qb in range(BETA_ORDER+1):
        for k in range(1, T_ORDER//2):
            r = 2*k+1
            direct = paired_coefficient(fourier, qb, k)
            generic = box.box.mixed_W(fourier, qb, r)/factorial(r)
            if not direct.overlaps(generic):
                raise AssertionError((qb, k, direct, generic))


def coefficient_beta_enclosure(box, fourier, hi_abs, k: int) -> arb:
    bulk = scaled.bulk
    hb = bulk.hull(-bulk.aq(box.beta_rad), bulk.aq(box.beta_rad))
    out = arb(0)
    power = arb(1)
    for qb in range(BETA_ORDER+1):
        out += paired_coefficient(fourier, qb, k)*power/factorial(qb)
        power *= hb
    qrem = BETA_ORDER+1
    r = 2*k+1
    remainder = (bulk.aq(box.beta_rad)**qrem/factorial(qrem)
                 *box._abs_mixed(hi_abs, qrem, r)/factorial(r))
    return out+remainder*bulk.pm1()


def paired_normalized(box, coefficient_boxes, hi_abs,
                      t_lo: Fraction, t_hi: Fraction) -> arb:
    bulk = scaled.bulk
    t = bulk.hull(bulk.aq(t_lo), bulk.aq(t_hi))
    t2 = t*t
    value = arb(0)
    power = arb(1)
    for coefficient in coefficient_boxes:
        value += coefficient*power
        power *= t2
    rt = T_ORDER+1
    spatial_abs = sum((
        bulk.aq(box.beta_rad)**qb/factorial(qb)
        *box.box.abs_mixed_center(qb, rt)
        for qb in range(BETA_ORDER+1)), arb(0))
    qrem = BETA_ORDER+1
    spatial_abs += (bulk.aq(box.beta_rad)**qrem/factorial(qrem)
                    *box._abs_mixed(hi_abs, qrem, rt))
    error = bulk.aq(t_hi)**(rt-3)/factorial(rt)*spatial_abs
    return value+error*bulk.pm1()


def cover(evaluator, lo: Fraction, hi: Fraction,
          min_width=Fraction(1, 1_000_000)) -> int:
    count = 0
    stack = [(lo, hi)]
    while stack:
        a, b = stack.pop()
        if evaluator(a, b) < 0:
            count += 1
        elif b-a <= min_width:
            raise RuntimeError("paired left failure near t=%s" % float(a))
        else:
            mid = (a+b)/2
            stack.append((mid, b)); stack.append((a, mid))
    return count


def main() -> int:
    ctx.prec = 180
    scaled.install_design_backend()
    import certify_left_edge_beta_taylor_arb as left

    lo = Fraction(sys.argv[1]) if len(sys.argv) > 1 else Fraction(80)
    hi = Fraction(sys.argv[2]) if len(sys.argv) > 2 else Fraction(801, 10)
    box = left.LeftEdgeBox(
        lo, hi, order=BETA_ORDER, t_order=T_ORDER, prec=180)
    fourier = endpoint_fourier(box)
    identity_regression(box, fourier)
    hi_abs = box._absolute_sums_at_hi(BETA_ORDER+1, T_ORDER+2)
    coefficients = [
        coefficient_beta_enclosure(box, fourier, hi_abs, k)
        for k in range(1, T_ORDER//2)
    ]
    normalized = cover(
        lambda a, b: paired_normalized(box, coefficients, hi_abs, a, b),
        Fraction(0), SPLICE)
    regular = left.cover_regular(box, SPLICE, Fraction(3, 5))
    print("SCALED PAIRED LEFT DESIGN PASS", float(lo), float(hi),
          "normalized", normalized, "regular", regular,
          "beta_order", BETA_ORDER, "t_order", T_ORDER,
          "splice", SPLICE, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
