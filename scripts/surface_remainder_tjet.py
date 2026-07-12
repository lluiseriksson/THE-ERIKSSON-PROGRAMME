"""Second-order parameter jet used for centred t-box remainder bounds.

``d`` and ``d2`` store ordinary (not factorial-normalized) derivatives.
Keeping the second derivative lets the terminal integrator use a genuine
Taylor bound in the parameter instead of paying a first-order interval
dependency cost across the whole parameter box.
"""

from dataclasses import dataclass

from flint import arb


def A(value):
    return value if isinstance(value, arb) else arb(str(value))


@dataclass(frozen=True)
class TJet:
    v: arb
    d: arb = arb(0)
    d2: arb = arb(0)
    _jet_scalar_marker = True

    def __add__(self, other):
        other = tjet(other)
        return TJet(self.v+other.v, self.d+other.d, self.d2+other.d2)

    __radd__ = __add__

    def __neg__(self):
        return TJet(-self.v, -self.d, -self.d2)

    def __sub__(self, other):
        return self+(-tjet(other))

    def __rsub__(self, other):
        return tjet(other)+(-self)

    def __mul__(self, other):
        other = tjet(other)
        return TJet(
            self.v*other.v,
            self.d*other.v+self.v*other.d,
            self.d2*other.v+2*self.d*other.d+self.v*other.d2,
        )

    __rmul__ = __mul__

    def inv(self):
        inverse = 1/self.v
        first = -self.d*inverse*inverse
        second = (2*(self.d*self.d)*inverse*inverse*inverse
                  -self.d2*inverse*inverse)
        return TJet(
            inverse,
            first,
            second,
        )

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
        return TJet(
            self.v**power,
            power*self.v**(power-1)*self.d,
            power*(power-1)*self.v**(power-2)*(self.d*self.d)
            + power*self.v**(power-1)*self.d2,
        )

    def sqrt(self):
        root = self.v.sqrt()
        inverse_root = 1/root
        return TJet(
            root,
            self.d*inverse_root/2,
            self.d2*inverse_root/2
            -(self.d*self.d)*inverse_root*inverse_root*inverse_root/4,
        )

    def exp(self):
        value = self.v.exp()
        return TJet(value, value*self.d, value*(self.d*self.d+self.d2))

    def sin(self):
        return TJet(
            self.v.sin(),
            self.v.cos()*self.d,
            -self.v.sin()*(self.d*self.d)+self.v.cos()*self.d2,
        )

    def cos(self):
        return TJet(
            self.v.cos(),
            -self.v.sin()*self.d,
            -self.v.cos()*(self.d*self.d)-self.v.sin()*self.d2,
        )


def tjet(value, derivative=arb(0), second_derivative=arb(0)):
    return value if isinstance(value, TJet) else TJet(
        A(value), A(derivative), A(second_derivative))


def symmetric(value_radius, derivative_radius=arb(0),
              second_derivative_radius=arb(0)):
    return TJet(A(value_radius)*arb("0 +/- 1"),
                A(derivative_radius)*arb("0 +/- 1"),
                A(second_derivative_radius)*arb("0 +/- 1"))
