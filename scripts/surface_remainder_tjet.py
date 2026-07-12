"""Fourth-order parameter jet used for centred t-box remainder bounds.

``d`` through ``d4`` store ordinary (not factorial-normalized) derivatives.
Internally the arithmetic converts to normalized Taylor coefficients.  This
lets the terminal integrator retain three centre derivatives and pay only a
fourth-order whole-box remainder.
"""

from dataclasses import dataclass
from math import factorial

from flint import arb


def A(value):
    return value if isinstance(value, arb) else arb(str(value))


@dataclass(frozen=True)
class TJet:
    v: arb
    d: arb = arb(0)
    d2: arb = arb(0)
    d3: arb = arb(0)
    d4: arb = arb(0)
    _jet_scalar_marker = True

    def __add__(self, other):
        other = tjet(other)
        return TJet(*(a+b for a, b in zip(self.derivatives(),
                                          other.derivatives())))

    __radd__ = __add__

    def __neg__(self):
        return TJet(*(-value for value in self.derivatives()))

    def __sub__(self, other):
        return self+(-tjet(other))

    def __rsub__(self, other):
        return tjet(other)+(-self)

    def __mul__(self, other):
        other = tjet(other)
        return from_normalized(_mul_coefficients(
            self.normalized(), other.normalized()))

    __rmul__ = __mul__

    def inv(self):
        a = self.normalized()
        out = [arb(0) for _ in range(5)]
        out[0] = 1/a[0]
        for n in range(1, 5):
            out[n] = -out[0]*sum(
                (a[k]*out[n-k] for k in range(1, n+1)), arb(0))
        return from_normalized(out)

    def __truediv__(self, other):
        return self*tjet(other).inv()

    def __rtruediv__(self, other):
        return tjet(other)*self.inv()

    def __pow__(self, power):
        if not isinstance(power, int):
            raise TypeError("TJet power must be an integer")
        if power == 0:
            return tjet(1)
        if power == 1:
            # Do not evaluate the generic p(p-1)*v^(p-2) term: when
            # ``v`` contains zero it would create the spurious form
            # 0 * v^(-1), hence NaN, although x^1 is exactly x.
            return self
        if power < 0:
            return (self.inv())**(-power)
        out = tjet(1)
        base = self
        exponent = power
        while exponent:
            if exponent & 1:
                out *= base
            exponent >>= 1
            if exponent:
                base *= base
        return out

    def sqrt(self):
        root = self.v.sqrt()
        inverse = 1/self.v
        coefficients = []
        binomial = arb(1)
        inverse_power = arb(1)
        for degree in range(5):
            coefficients.append(root*binomial*inverse_power)
            binomial *= (arb(1)/2-degree)/arb(degree+1)
            inverse_power *= inverse
        return self._compose(coefficients)

    def exp(self):
        value = self.v.exp()
        return self._compose([value/arb(factorial(k)) for k in range(5)])

    def sin(self):
        cycle = (self.v.sin(), self.v.cos(), -self.v.sin(), -self.v.cos())
        return self._compose([cycle[k % 4]/arb(factorial(k))
                              for k in range(5)])

    def cos(self):
        cycle = (self.v.cos(), -self.v.sin(), -self.v.cos(), self.v.sin())
        return self._compose([cycle[k % 4]/arb(factorial(k))
                              for k in range(5)])

    def derivatives(self):
        return (self.v, self.d, self.d2, self.d3, self.d4)

    def normalized(self):
        return tuple(value/arb(factorial(k))
                     for k, value in enumerate(self.derivatives()))

    def _compose(self, outer):
        inner = list(self.normalized())
        inner[0] = arb(0)
        powers = [[arb(1)]+[arb(0)]*4]
        for _ in range(4):
            powers.append(_mul_coefficients(powers[-1], inner))
        out = [arb(0) for _ in range(5)]
        for coefficient, power in zip(outer, powers):
            for order in range(5):
                out[order] += coefficient*power[order]
        return from_normalized(out)


def _mul_coefficients(a, b):
    return [sum((a[k]*b[n-k] for k in range(n+1)), arb(0))
            for n in range(5)]


def from_normalized(coefficients):
    return TJet(*(coefficient*arb(factorial(k))
                  for k, coefficient in enumerate(coefficients)))


def tjet(value, derivative=arb(0), second_derivative=arb(0),
         third_derivative=arb(0), fourth_derivative=arb(0)):
    return value if isinstance(value, TJet) else TJet(
        A(value), A(derivative), A(second_derivative),
        A(third_derivative), A(fourth_derivative))


def symmetric(value_radius, derivative_radius=arb(0),
              second_derivative_radius=arb(0),
              third_derivative_radius=arb(0),
              fourth_derivative_radius=arb(0)):
    return TJet(A(value_radius)*arb("0 +/- 1"),
                A(derivative_radius)*arb("0 +/- 1"),
                A(second_derivative_radius)*arb("0 +/- 1"),
                A(third_derivative_radius)*arb("0 +/- 1"),
                A(fourth_derivative_radius)*arb("0 +/- 1"))
