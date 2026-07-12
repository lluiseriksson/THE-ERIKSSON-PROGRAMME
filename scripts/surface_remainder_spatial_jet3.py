"""Bivariate normalized Taylor jets through total spatial degree five.

The filename is retained because the degree-three K2 prototype imported it.
The live positive-box lane now integrates degrees zero through four and charges
only the total-degree-five spatial remainder.
"""

from dataclasses import dataclass
from math import factorial

from flint import arb


MAX_DEGREE = 5
INDICES = tuple((i, degree-i) for degree in range(MAX_DEGREE+1)
                for i in range(degree+1))


def A(value):
    if isinstance(value, arb) or getattr(value, "_jet_scalar_marker", False):
        return value
    return arb(str(value))


@dataclass(frozen=True)
class Jet3:
    coefficients: dict[tuple[int, int], arb]

    def get(self, i, j):
        return self.coefficients.get((i, j), arb(0))


def jet(value) -> Jet3:
    return value if isinstance(value, Jet3) else Jet3({(0, 0): A(value)})


def variable_x(value) -> Jet3:
    return Jet3({(0, 0): A(value), (1, 0): arb(1)})


def variable_y(value) -> Jet3:
    return Jet3({(0, 0): A(value), (0, 1): arb(1)})


def jadd(a, b):
    a, b = jet(a), jet(b)
    return Jet3({index: a.get(*index)+b.get(*index) for index in INDICES})


def jneg(a):
    a = jet(a)
    return Jet3({index: -a.get(*index) for index in INDICES})


def jmul(a, b):
    a, b = jet(a), jet(b)
    out = {}
    for i, j in INDICES:
        total = arb(0)
        for p in range(i+1):
            for q in range(j+1):
                total += a.get(p, q)*b.get(i-p, j-q)
        out[i, j] = total
    return Jet3(out)


def jscale(a, value):
    return jmul(a, value)


def _compose(a, normalized_derivatives):
    a = jet(a)
    h = Jet3({index: (arb(0) if index == (0, 0) else a.get(*index))
              for index in INDICES})
    powers = [jet(1)]
    for _ in range(MAX_DEGREE):
        powers.append(jmul(powers[-1], h))
    out = jet(0)
    for coefficient, power in zip(normalized_derivatives, powers):
        out = jadd(out, jscale(power, coefficient))
    return out


def jinv(a):
    a = jet(a); value = a.get(0, 0)
    inverse = 1/value
    coefficients = []
    power = inverse
    for degree in range(MAX_DEGREE+1):
        coefficients.append(power if degree % 2 == 0 else -power)
        power *= inverse
    return _compose(a, coefficients)


def jsqrt(a):
    a = jet(a); root = a.get(0, 0).sqrt()
    inverse_value = 1/a.get(0, 0)
    coefficients = []
    binomial = arb(1)
    inverse_power = arb(1)
    for degree in range(MAX_DEGREE+1):
        coefficients.append(root*binomial*inverse_power)
        binomial *= (arb(1)/2-degree)/arb(degree+1)
        inverse_power *= inverse_value
    return _compose(a, coefficients)


def jexp(a):
    a = jet(a); value = a.get(0, 0).exp()
    return _compose(a, [value/arb(factorial(k))
                        for k in range(MAX_DEGREE+1)])


def jsin(a):
    a = jet(a); value = a.get(0, 0)
    cycle = (value.sin(), value.cos(), -value.sin(), -value.cos())
    return _compose(a, [cycle[k % 4]/arb(factorial(k))
                        for k in range(MAX_DEGREE+1)])


def jcos(a):
    a = jet(a); value = a.get(0, 0)
    cycle = (value.cos(), -value.sin(), -value.cos(), value.sin())
    return _compose(a, [cycle[k % 4]/arb(factorial(k))
                        for k in range(MAX_DEGREE+1)])


def derivative(a, i, j):
    """Return the ordinary partial derivative from normalized storage."""
    return jet(a).get(i, j)*factorial(i)*factorial(j)
