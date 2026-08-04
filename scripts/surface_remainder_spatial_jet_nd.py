"""Normalized total-degree jets in a fixed number of spatial variables."""

from dataclasses import dataclass
from itertools import product
from math import factorial

from flint import arb


def indices(dimension, degree):
    return tuple(index for index in product(range(degree+1), repeat=dimension)
                 if sum(index) <= degree)


def A(value):
    if isinstance(value, arb) or getattr(value, "_jet_scalar_marker", False):
        return value
    return arb(str(value))


@dataclass(frozen=True)
class JetND:
    coefficients: dict
    dimension: int = 4
    degree: int = 5

    def get(self, index):
        return self.coefficients.get(tuple(index), arb(0))


def jet(value, dimension=4, degree=5):
    if isinstance(value, JetND):
        return value
    return JetND({(0,)*dimension: A(value)}, dimension, degree)


def variable(value, axis, dimension=4, degree=5):
    unit = [0]*dimension
    unit[axis] = 1
    return JetND({(0,)*dimension: A(value), tuple(unit): arb(1)},
                 dimension, degree)


def jadd(a, b):
    if not isinstance(a, JetND):
        a = jet(a, b.dimension, b.degree)
    if not isinstance(b, JetND):
        b = jet(b, a.dimension, a.degree)
    assert (a.dimension, a.degree) == (b.dimension, b.degree)
    return JetND({i: a.get(i)+b.get(i) for i in indices(a.dimension, a.degree)},
                 a.dimension, a.degree)


def jneg(a):
    a = a if isinstance(a, JetND) else jet(a)
    return JetND({i: -a.get(i) for i in indices(a.dimension, a.degree)},
                 a.dimension, a.degree)


def subindices(index):
    return product(*(range(value+1) for value in index))


def jmul(a, b):
    if not isinstance(a, JetND):
        a = jet(a, b.dimension, b.degree)
    if not isinstance(b, JetND):
        b = jet(b, a.dimension, a.degree)
    out = {}
    for index in indices(a.dimension, a.degree):
        out[index] = sum((a.get(part)*b.get(
            tuple(index[k]-part[k] for k in range(a.dimension)))
            for part in subindices(index)), arb(0))
    return JetND(out, a.dimension, a.degree)


def jscale(a, value):
    return jmul(a, value)


def _compose(a, normalized_derivatives):
    zero = (0,)*a.dimension
    h = JetND({i: (arb(0) if i == zero else a.get(i))
               for i in indices(a.dimension, a.degree)},
              a.dimension, a.degree)
    powers = [jet(1, a.dimension, a.degree)]
    for _ in range(a.degree):
        powers.append(jmul(powers[-1], h))
    out = jet(0, a.dimension, a.degree)
    for coefficient, power in zip(normalized_derivatives, powers):
        out = jadd(out, jscale(power, coefficient))
    return out


def jinv(a):
    value = a.get((0,)*a.dimension)
    inverse, power, coefficients = 1/value, 1/value, []
    for degree in range(a.degree+1):
        coefficients.append(power if degree % 2 == 0 else -power)
        power *= inverse
    return _compose(a, coefficients)


def jsqrt(a):
    value = a.get((0,)*a.dimension)
    root, inverse = value.sqrt(), 1/value
    coefficients, binomial, inverse_power = [], arb(1), arb(1)
    for degree in range(a.degree+1):
        coefficients.append(root*binomial*inverse_power)
        binomial *= (arb(1)/2-degree)/arb(degree+1)
        inverse_power *= inverse
    return _compose(a, coefficients)


def jexp(a):
    value = a.get((0,)*a.dimension).exp()
    return _compose(a, [value/arb(factorial(k))
                        for k in range(a.degree+1)])


def jsin(a):
    value = a.get((0,)*a.dimension)
    cycle = (value.sin(), value.cos(), -value.sin(), -value.cos())
    return _compose(a, [cycle[k % 4]/arb(factorial(k))
                        for k in range(a.degree+1)])


def jcos(a):
    value = a.get((0,)*a.dimension)
    cycle = (value.cos(), -value.sin(), -value.cos(), value.sin())
    return _compose(a, [cycle[k % 4]/arb(factorial(k))
                        for k in range(a.degree+1)])
