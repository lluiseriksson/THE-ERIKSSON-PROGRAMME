"""Symbolic finite-mode audit of the shifted-correlation identity."""

import sympy as sp


def verify():
    z = sp.symbols("z", nonzero=True)
    ii = sp.I
    for n in range(9):
        k = 2*n + 1
        sin_nd = lambda m: (z**(2*m)-z**(-2*m))/(2*ii)
        original = n*sin_nd(n+1) - (n+1)*sin_nd(n)
        sin_half = (z-z**-1)/(2*ii)
        cos_half = (z+z**-1)/2
        sin_khalf = (z**k-z**(-k))/(2*ii)
        cos_khalf = (z**k+z**(-k))/2
        shifted = k*sin_half*cos_khalf-cos_half*sin_khalf
        assert sp.cancel(original-shifted) == 0
    print(
        "SHIFTED CORRELATION ALGEBRA PASS: modes n=0,...,8; "
        "orthogonality proof remains analytic, G5 radius remains open"
    )


if __name__ == "__main__":
    verify()
