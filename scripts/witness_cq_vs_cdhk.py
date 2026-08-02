"""An explicit witness that C_q and C_DHK are not equal in general.

IN THE PAPER'S OWN CONVENTIONS, which the first version of this script did not
use.  A referee caught it: the first version took the HERMITIAN Pauli matrices
and the UNNORMALIZED trace, and printed -2 and +6.  Those are true statements
about a real inequality, but they are not the values of the paper's equations
(11)-(12), which use

    tr_2 = (1/2) Tr                the normalized fundamental trace
    A_k  = c * i * sigma_k         ANTIHERMITIAN generator directions

The idea survived the correction; the numbers did not.  Recorded here rather
than quietly swapping the constants.

NOTATION.  `sigma_x, sigma_y, sigma_z` are the hermitian Pauli matrices; the
paper's three directions are `A_k = c i sigma_k`.  The GROUP element in the
witness is written `i sigma_x` and never "iX", because in the paper `X` already
names an antihermitian direction -- reusing it is what made the first version
confusing.

THE NORMALIZATION c IS NEVER NEEDED.  Both operators insert A exactly twice, so
both are homogeneous of degree 2 in c; the witness therefore separates them for
every c != 0, and c = 0 is excluded because it kills all three directions.  So
this closes without reading c off the Lean producer, which is unavailable.

Arithmetic is exact: entries are Gaussian rationals (pairs of Fractions), never
floats.  No acceptance depends on an `assert`.
"""

import sys
from fractions import Fraction as F

ZERO = (F(0), F(0))
ONE = (F(1), F(0))
IU = (F(0), F(1))


def cadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def cmul(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def cscale(s, x):
    return (s * x[0], s * x[1])


def cneg(x):
    return (-x[0], -x[1])


def cconj(x):
    return (x[0], -x[1])


SX = ((ZERO, ONE), (ONE, ZERO))
SY = ((ZERO, cneg(IU)), (IU, ZERO))
SZ = ((ONE, ZERO), (ZERO, cneg(ONE)))
ID = ((ONE, ZERO), (ZERO, ONE))


def mul(a, b):
    return tuple(tuple(cadd(cmul(a[i][0], b[0][j]), cmul(a[i][1], b[1][j]))
                       for j in range(2)) for i in range(2))


def scale(s, a):
    return tuple(tuple(cscale(s, a[i][j]) for j in range(2)) for i in range(2))


def imul(a):
    return tuple(tuple(cmul(IU, a[i][j]) for j in range(2)) for i in range(2))


def dagger(a):
    return tuple(tuple(cconj(a[j][i]) for j in range(2)) for i in range(2))


def tr2(a):
    """The NORMALIZED fundamental trace tr_2 = (1/2) Tr, as the paper uses."""
    t = cadd(a[0][0], a[1][1])
    return (t[0] / 2, t[1] / 2)


def chain(*ms):
    out = ID
    for m in ms:
        out = mul(out, m)
    return out


def csum(vals):
    out = ZERO
    for v in vals:
        out = cadd(out, v)
    return out


def fmt(z):
    if z[1] == 0:
        return str(z[0])
    return "%s%+si" % (z[0], z[1])


def directions(c):
    """The paper's three antihermitian directions A_k = c i sigma_k."""
    return [scale(c, imul(s)) for s in (SX, SY, SZ)]


def c_dhk(a1, a2, a3, a4, al, be, A):
    return csum(tr2(chain(dagger(a3), be, a2, Ak, dagger(a4), al, a1, Ak))
                for Ak in A)


def c_q(a1, a2, a3, a4, al, be, A):
    return csum(tr2(chain(be, a2, dagger(a4), Ak, al, a1, dagger(a3), Ak))
                for Ak in A)


def main():
    failures = []
    checks = 0

    g = imul(SX)
    det = cadd(cmul(g[0][0], g[1][1]), cneg(cmul(g[0][1], g[1][0])))
    if det != ONE or mul(dagger(g), g) != ID:
        failures.append("i*sigma_x is not in SU(2): det %s" % fmt(det))
    else:
        checks += 1
    print("group element  i*sigma_x : det = %s, unitary = %s"
          % (fmt(det), mul(dagger(g), g) == ID))

    anti = True
    for c in (F(1), F(1, 2)):
        for k, Ak in enumerate(directions(c)):
            if dagger(Ak) != scale(F(-1), Ak):
                failures.append("A_%d not antihermitian at c=%s" % (k, c))
                anti = False
    if anti:
        checks += 1
    print("generators A_k = c i sigma_k : antihermitian, checked at c = 1 and 1/2")

    args = (ID, ID, ID, g, ID, g)
    base_d = c_dhk(*args, A=directions(F(1)))
    base_q = c_q(*args, A=directions(F(1)))
    half_d = c_dhk(*args, A=directions(F(1, 2)))
    half_q = c_q(*args, A=directions(F(1, 2)))
    if half_d == cscale(F(1, 4), base_d) and half_q == cscale(F(1, 4), base_q):
        checks += 1
    else:
        failures.append("degree-2 homogeneity in c failed")
    print("homogeneity in c : degree 2 in both operators, verified at c = 1/2")

    diff = cadd(base_q, cneg(base_d))
    print("")
    print("WITNESS   a1 = a2 = a3 = alpha = 1,   a4 = beta = i*sigma_x")
    print("  C_DHK        = (%s) c^2" % fmt(base_d))
    print("  C_q          = (%s) c^2" % fmt(base_q))
    print("  C_q - C_DHK  = (%s) c^2" % fmt(diff))
    print("")
    print("  nonzero for EVERY c != 0, and c = 0 is excluded because it makes")
    print("  all three directions vanish.  The normalization is not needed.")
    print("")
    print("  at the standard normalization c = 1/2  (A_k = (i/2) sigma_k):")
    print("    C_DHK = %s" % fmt(half_d))
    print("    C_q   = %s" % fmt(half_q))

    if diff != ZERO:
        checks += 1
    else:
        failures.append("the two operators AGREE on this witness")

    for line in failures:
        sys.stderr.write("FAIL: %s\n" % line)
    print("")
    print("checks passed: %d of 4" % checks)
    if failures:
        return 1
    if checks != 4:
        sys.stderr.write("FAIL: counter %d does not match 4\n" % checks)
        return 1
    print("PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
