"""Arb gate for real main/mirror coercivity on the K4 regular ball.

The certificate is local to the registered stress value ``t=2.9``,
``delta<=1/15``, and scaled radius ``R=4``.  It does not prove the complex
disk bounds or the exterior-tail estimates required by K4 production.
"""

from flint import arb, ctx


T = arb(29)/10
DELTA_MAX = arb(1)/15
RADIUS = arb(4)


def lower(value):
    return arb(value.lower())


def upper(value):
    return arb(value.upper())


def saddle_row(amplitude):
    # p=sin^2(s/2), q=sin^2(alpha/2).  Each coordinate is at most R.
    angle = DELTA_MAX.sqrt()*RADIUS/2
    p_max = upper(angle.sin()**2)
    sum_max = 2*p_max
    k = lower(amplitude**2)
    # pq <= (p+q)^2/4 <= sum_max*(p+q)/4.
    gamma = lower(1-sum_max/(4*k))
    eta = lower(1-sum_max)
    # sin(s/2)>=s/pi on this domain, hence p+q>=delta*r^2/pi^2.
    kappa = lower(gamma/arb.pi()**2)
    assert lower(angle) >= 0 and upper(angle) < arb.pi()/2
    assert k > 0 and gamma > 0 and eta > 0 and kappa > 0
    return {
        "amplitude_squared_lower": k,
        "p_plus_q_upper": sum_max,
        "gamma_lower": gamma,
        "one_minus_w_lower": eta,
        "A_over_r2_lower": kappa,
    }


def certify():
    ctx.prec = 140
    return {
        "main": saddle_row((T/4).cos()),
        "mirror": saddle_row((T/4).sin()),
    }


if __name__ == "__main__":
    rows = certify()
    print("K4 REAL COERCIVITY PASS", {
        name: {key: value.str(30) for key, value in row.items()}
        for name, row in rows.items()
    }, "COMPLEX DISK AND OUTER TAIL STILL REQUIRED")
