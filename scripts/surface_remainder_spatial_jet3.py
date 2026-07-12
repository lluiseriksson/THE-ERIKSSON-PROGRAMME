"""Bivariate normalized Taylor jets through total spatial degree three."""

from dataclasses import dataclass
from math import factorial

from flint import arb


INDICES = tuple((i, degree-i) for degree in range(4)
                for i in range(degree+1))


def A(value):
    return value if isinstance(value, arb) else arb(str(value))


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
    powers = [jet(1), h]
    powers.extend((jmul(powers[-1], h) for _ in range(2)))
    out = jet(0)
    for coefficient, power in zip(normalized_derivatives, powers):
        out = jadd(out, jscale(power, coefficient))
    return out


def jinv(a):
    a = jet(a); value = a.get(0, 0)
    return _compose(a, [1/value, -1/value**2, 1/value**3, -1/value**4])


def jsqrt(a):
    a = jet(a); root = a.get(0, 0).sqrt()
    return _compose(a, [root, 1/(2*root), -1/(8*root**3),
                        1/(16*root**5)])


def jexp(a):
    a = jet(a); value = a.get(0, 0).exp()
    return _compose(a, [value, value, value/2, value/6])


def jsin(a):
    a = jet(a); value = a.get(0, 0)
    return _compose(a, [value.sin(), value.cos(), -value.sin()/2,
                        -value.cos()/6])


def jcos(a):
    a = jet(a); value = a.get(0, 0)
    return _compose(a, [value.cos(), -value.sin(), -value.cos()/2,
                        value.sin()/6])


def derivative(a, i, j):
    """Return the ordinary partial derivative from normalized storage."""
    return jet(a).get(i, j)*factorial(i)*factorial(j)
