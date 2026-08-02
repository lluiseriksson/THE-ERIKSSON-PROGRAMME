"""An explicit witness that C_q and C_DHK are not equal in general.

The reviewer's objection is exactly right: two different trace expressions are
not a proof of inequality, because SU(2) satisfies special identities that can
collapse syntactically different formulas.  A witness is required.

Searched over a1..a4, alpha, beta in {I, iX, iY, iZ} -- every one of which lies
in SU(2) (det = 1, unitary) and has GAUSSIAN INTEGER entries.  That matters:
a witness in this set is exactly representable, so the same numbers can be
compiled in Lean and closed by `norm_num` with no floating point anywhere.

    C_DHK(a) = sum_A tr( a3^-1 beta a2 A a4^-1 alpha a1 A )
    C_q  (a) = sum_A tr( beta a2 a4^-1 A alpha a1 a3^-1 A )

with A ranging over the three Pauli matrices.

No acceptance here depends on an `assert`: every check raises or returns
non-zero explicitly, in normal and in `-O` mode alike.
"""

import itertools
import sys

I2 = ((1, 0), (0, 1))
X = ((0, 1), (1, 0))
Y = ((0, complex(0, -1)), (complex(0, 1), 0))
Z = ((1, 0), (0, -1))
PAULI = (X, Y, Z)


def mul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2))
                 for i in range(2))


def dagger(a):
    return tuple(tuple(complex(a[j][i]).conjugate() for j in range(2)) for i in range(2))


def tr(a):
    return a[0][0] + a[1][1]


def chain(*ms):
    out = I2
    for m in ms:
        out = mul(out, m)
    return out


def c_dhk(a1, a2, a3, a4, al, be):
    # a3^-1 beta a2 A a4^-1 alpha a1 A, summed over Pauli A
    return sum(tr(chain(dagger(a3), be, a2, A, dagger(a4), al, a1, A)) for A in PAULI)


def c_q(a1, a2, a3, a4, al, be):
    # beta a2 a4^-1 A alpha a1 a3^-1 A, summed over Pauli A
    return sum(tr(chain(be, a2, dagger(a4), A, al, a1, dagger(a3), A)) for A in PAULI)


def main():
    iX = tuple(tuple(complex(0, 1) * x for x in row) for row in X)
    iY = tuple(tuple(complex(0, 1) * x for x in row) for row in Y)
    iZ = tuple(tuple(complex(0, 1) * x for x in row) for row in Z)
    basis = [("1", I2), ("iX", iX), ("iY", iY), ("iZ", iZ)]

    # The elements really are in SU(2); check it rather than assume it.
    bad = 0
    for name, m in basis:
        det = m[0][0] * m[1][1] - m[0][1] * m[1][0]
        unit = mul(dagger(m), m)
        if abs(det - 1) > 1e-12:
            sys.stderr.write("FAIL: %s has det %s\n" % (name, det))
            bad += 1
        if abs(unit[0][0] - 1) + abs(unit[1][1] - 1) + abs(unit[0][1]) + abs(unit[1][0]) > 1e-12:
            sys.stderr.write("FAIL: %s is not unitary\n" % name)
            bad += 1
    if bad:
        return 1
    print("all four basis elements verified in SU(2): det 1, unitary")

    hits = []
    for combo in itertools.product(basis, repeat=6):
        names = [c[0] for c in combo]
        ms = [c[1] for c in combo]
        d = c_dhk(*ms)
        q = c_q(*ms)
        if abs(d - q) > 1e-9:
            hits.append((names, d, q, abs(d - q)))

    print("combinations searched: %d" % (len(basis) ** 6))
    print("combinations where C_q != C_DHK: %d" % len(hits))

    if not hits:
        sys.stderr.write("FAIL: no witness found -- the operators may agree on "
                         "this basis, which would NOT settle the general case\n")
        return 1

    # Prefer the witness with the most identity entries: the shortest to state,
    # and the cheapest to recompute by hand or in Lean.
    hits.sort(key=lambda h: (-h[0].count("1"), h[0]))
    names, d, q, gap = hits[0]
    print("")
    print("SIMPLEST WITNESS")
    print("  a1,a2,a3,a4,alpha,beta = %s" % ", ".join(names))
    print("  C_DHK = %s" % fmt(d))
    print("  C_q   = %s" % fmt(q))
    print("  |difference| = %s" % gap)
    print("")
    print("next four witnesses, for cross-checking:")
    for names2, d2, q2, _ in hits[1:5]:
        print("  %-28s C_DHK=%-12s C_q=%s"
              % (", ".join(names2), fmt(d2), fmt(q2)))

    checked = len(hits)
    print("")
    print("witnesses found: %d" % checked)
    if checked < 1:
        return 1
    print("PASS")
    return 0


def fmt(z):
    z = complex(z)
    re, im = z.real, z.imag
    if abs(im) < 1e-12:
        return "%g" % re
    return "%g%+gi" % (re, im)


if __name__ == "__main__":
    sys.exit(main())
