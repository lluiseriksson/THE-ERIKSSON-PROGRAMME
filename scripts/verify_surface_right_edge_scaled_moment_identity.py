"""Exact audit of every factor in the paired right-edge moment formula."""

import sympy as sp


def verify():
    delta, lam, scale = sp.symbols(
        "delta lambda scale", positive=True, nonzero=True)
    S = sp.symbols("S", positive=True)
    kd, kf, kt, hdd, hdf = sp.symbols("kd kf kt hdd hdf")

    # The original moment integrals in terms of the scaled definitions.
    mu_d = kd / scale
    mu_f = delta * kf / scale
    mu_t = kt / scale                 # integral K*(Phi-D)
    hd_d = delta**2 * hdd / scale     # integral H_B*D^2
    hd_f = delta**3 * hdf / scale     # integral H_B*D*F
    beta = 1 / delta

    # D=2(1-P-Q) and K_t=-4 beta^3 S(1-P-Q)H_B
    # imply K_t=-2 beta^3 S D H_B.  Also
    # F_t=-(S/2)(Phi-D) and C_t=-S/2.
    e_prime = (
        -S/2 - S*mu_t/(2*mu_d)
        -2*beta**3*S*(mu_d*hd_f-mu_f*hd_d)/mu_d**2
    )
    h_direct = sp.cancel(-e_prime/lam)
    z = kd**2+kd*kt+4*(kd*hdf-kf*hdd)
    h_scaled = S*z/(2*lam*kd**2)
    assert sp.cancel(h_direct-h_scaled) == 0

    # Independent derivation from E=C+mu_F/mu_D and the two derivative
    # identities, guarding the sign as well as the factors 2 and 4.
    c_prime = -S/2
    mu_d_prime = -2*beta**3*S*hd_d
    mu_f_prime = -S*mu_t/2-2*beta**3*S*hd_f
    quotient_derivative = sp.cancel(
        c_prime+mu_f_prime/mu_d-mu_f*mu_d_prime/mu_d**2)
    assert sp.cancel(quotient_derivative-e_prime) == 0

    print(
        "SCALED MOMENT IDENTITY PASS: "
        "H=S[kd^2+kd*kt+4(kd*hdf-kf*hdd)]/(2 lambda kd^2)"
    )


if __name__ == "__main__":
    verify()
