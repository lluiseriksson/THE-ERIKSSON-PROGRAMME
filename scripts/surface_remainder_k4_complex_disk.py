"""Majorant-series gate for the K4 complex delta disk.

For ``|delta|<=7/100`` and the scaled square ``|sigma|,|tau|<=4``, the
entire sinc-square series bounds the rationalized deficit ``delta*A`` away
from one for both stress-cell saddles.  The square is a conservative superset
of the registered radius-four ball.  Coefficient and tail bounds remain open.
"""

from flint import arb, ctx


T = arb(29)/10
RHO = arb(7)/100
DELTA_MAX = arb(1)/15
RADIUS = arb(4)


def lower(value):
    return arb(value.lower())


def upper(value):
    return arb(value.upper())


def sinc_square_majorant(x):
    root = x.sqrt()
    return (root.sinh()/root)**2


def saddle_row(amplitude):
    x = RHO*RADIUS**2/4
    p_abs = upper(RADIUS**2/4*sinc_square_majorant(x))
    k = lower(amplitude**2)
    delta_a_abs = upper(RHO*(2*p_abs+RHO*p_abs**2/k))
    eta = lower(1-delta_a_abs)
    assert RHO > DELTA_MAX
    assert k > 0 and delta_a_abs < 1 and eta > 0
    return {
        "rho": RHO,
        "sinc_square_abs_upper": upper(sinc_square_majorant(x)),
        "P_abs_upper": p_abs,
        "delta_A_abs_upper": delta_a_abs,
        "eta_lower": eta,
    }


def certify():
    ctx.prec = 140
    return {
        "main": saddle_row((T/4).cos()),
        "mirror": saddle_row((T/4).sin()),
    }


if __name__ == "__main__":
    rows = certify()
    print("K4 COMPLEX DISK PASS", {
        name: {key: value.str(30) for key, value in row.items()}
        for name, row in rows.items()
    }, "COEFFICIENT AND TAIL BOUNDS STILL REQUIRED")
