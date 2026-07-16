"""Numerical transport oracle for the regular-ball K4 chart.

The regular chart uses ``s=sqrt(delta)*sigma`` and
``alpha=sqrt(delta)*tau``.  This executable check compares a high-order
finite-difference derivative at fixed physical ``(s,alpha)`` with the full
Euler-transport operator.  It is a local identity audit only; it is not a
K4 cover or a budget certificate.
"""

from mpmath import mp


def g(delta, sigma, tau):
    # A non-separable analytic stress function.  The mixed terms make all
    # D, E, ED, and E^2 contributions nonzero at the test point.
    return mp.exp(mp.mpf("0.3") * delta) * (
        1 + mp.mpf("0.2") * sigma + mp.mpf("0.1") * tau**2
        + mp.mpf("0.05") * delta * sigma * tau
        + mp.mpf("0.03") * sigma**2 * tau
    )


def transported_second(delta, sigma, tau):
    D = lambda x: mp.diff(lambda d: g(d, x, tau), delta)
    D2 = mp.diff(lambda d: g(d, sigma, tau), delta, 2)
    gs = mp.diff(lambda x: g(delta, x, tau), sigma)
    gt = mp.diff(lambda y: g(delta, sigma, y), tau)
    gss = mp.diff(lambda x: g(delta, x, tau), sigma, 2)
    gtt = mp.diff(lambda y: g(delta, sigma, y), tau, 2)
    gst = mp.diff(lambda x: mp.diff(lambda y: g(delta, x, y), tau), sigma)
    gds = mp.diff(lambda d: mp.diff(lambda x: g(d, x, tau), sigma), delta)
    gdt = mp.diff(lambda d: mp.diff(lambda y: g(d, sigma, y), tau), delta)
    E = sigma * gs + tau * gt
    ED = sigma * gds + tau * gdt
    E2 = E + sigma**2 * gss + 2 * sigma * tau * gst + tau**2 * gtt
    return D2 - ED / delta + E / (2 * delta**2) + E2 / (4 * delta**2)


def physical_value(delta, s, alpha):
    root = mp.sqrt(delta)
    return g(delta, s / root, alpha / root)


def five_point_second(delta, s, alpha, h):
    return (
        -physical_value(delta + 2*h, s, alpha)
        + 16 * physical_value(delta + h, s, alpha)
        - 30 * physical_value(delta, s, alpha)
        + 16 * physical_value(delta - h, s, alpha)
        - physical_value(delta - 2*h, s, alpha)
    ) / (12 * h**2)


def main():
    mp.dps = 100
    delta = mp.mpf(1) / 40
    s = mp.mpf("0.17")
    alpha = mp.mpf("0.11")
    sigma, tau = s / mp.sqrt(delta), alpha / mp.sqrt(delta)
    h = delta * mp.mpf("1e-4")
    direct = five_point_second(delta, s, alpha, h)
    transported = transported_second(delta, sigma, tau)
    error = abs(direct - transported)
    print("K4 TRANSPORT ORACLE")
    print("delta", delta, "s", s, "alpha", alpha)
    print("sigma", sigma, "tau", tau, "h", h)
    print("direct_finite_difference", mp.nstr(direct, 40))
    print("transported_operator", mp.nstr(transported, 40))
    print("absolute_error", mp.nstr(error, 12))
    # The comparison is a finite-difference audit, so the threshold is
    # deliberately much looser than the 100-digit working precision.
    if error > mp.mpf("1e-10"):
        raise SystemExit("transport oracle failed")
    print("K4 TRANSPORT ORACLE PASS; LOCAL IDENTITY ONLY")


if __name__ == "__main__":
    main()
