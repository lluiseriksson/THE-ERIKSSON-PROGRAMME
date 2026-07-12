"""First-order parameter jet used for centred t-box remainder bounds."""

from dataclasses import dataclass

from flint import arb


def A(value):
    return value if isinstance(value, arb) else arb(str(value))


@dataclass(frozen=True)
class TJet:
    v: arb
    d: arb = arb(0)
    _jet_scalar_marker = True

    def __add__(self, other):
        other = tjet(other)
        return TJet(self.v+other.v, self.d+other.d)

    __radd__ = __add__

    def __neg__(self):
        return TJet(-self.v, -self.d)

    def __sub__(self, other):
        return self+(-tjet(other))

    def __rsub__(self, other):
        return tjet(other)+(-self)

    def __mul__(self, other):
        other = tjet(other)
        return TJet(self.v*other.v, self.d*other.v+self.v*other.d)

    __rmul__ = __mul__

    def inv(self):
        return TJet(1/self.v, -self.d/self.v**2)

    def __truediv__(self, other):
        return self*tjet(other).inv()

    def __rtruediv__(self, other):
        return tjet(other)*self.inv()

    def __pow__(self, power):
        if not isinstance(power, int):
            raise TypeError("TJet power must be an integer")
        if power == 0:
            return tjet(1)
        if power < 0:
            return (self.inv())**(-power)
        return TJet(self.v**power, power*self.v**(power-1)*self.d)

    def sqrt(self):
        root = self.v.sqrt()
        return TJet(root, self.d/(2*root))

    def exp(self):
        value = self.v.exp()
        return TJet(value, value*self.d)

    def sin(self):
        return TJet(self.v.sin(), self.v.cos()*self.d)

    def cos(self):
        return TJet(self.v.cos(), -self.v.sin()*self.d)


def tjet(value, derivative=arb(0)):
    return value if isinstance(value, TJet) else TJet(A(value), A(derivative))


def symmetric(value_radius, derivative_radius=arb(0)):
    return TJet(A(value_radius)*arb("0 +/- 1"),
                A(derivative_radius)*arb("0 +/- 1"))
