"""Exact mirror-involution audit for the high-beta determinant.

The identity removes the artificial beta growth in the old absolute
mirror-times-mirror product bound.  It makes no sign or numerical claim
about the transformed principal determinant.
"""

import sympy as sp


def verify():
    c, d0, n0 = sp.symbols("C D_p N_p")
    # C_p=2 sin(t/4)^2-1=-C, D o T=-D_p, N_C o T=-N_{C_p}.
    cp = -c
    d_t = -d0
    n_t = -n0
    f_t = sp.expand(n_t - c*d_t)
    f_p = sp.expand(n0 - cp*d0)
    assert sp.expand(f_t + 2*c*d_t + f_p) == 0

    a, f, u, w, scale, beta = sp.symbols(
        "a f u w scale beta", nonzero=True
    )
    # After the calibration F -> F+2CD, the four mirror moments are
    # (-a,-f,+u,+w), up to one common positive chart scale.
    b = -scale*a
    g = -scale*f
    v = scale*u
    x = scale*w
    principal_det = a*w-f*u
    mirror_det = sp.expand(b*x-g*v)
    assert sp.expand(mirror_det + scale**2*principal_det) == 0

    kappa = 4*beta**3
    full_mass = sp.symbols("d", nonzero=True)
    x_p = sp.cancel(kappa*principal_det/a**2)
    adverse_mirror = sp.cancel(kappa*(g*v-b*x)/full_mass**2)
    weighted_x_p = sp.cancel(
        (scale*a/full_mass)**2*x_p
    )
    assert sp.cancel(adverse_mirror-weighted_x_p) == 0
    return {
        "calibrated_mirror_F": -f_p,
        "mirror_determinant": mirror_det,
        "adverse_mirror": adverse_mirror,
        "weighted_transformed_X": weighted_x_p,
    }


def main() -> int:
    verify()
    print("MIRROR DETERMINANT INVOLUTION ALGEBRA PASS")
    print("(F_C+2 C D) o T = -F_{C_p}, C_p=-C")
    print("b*x-g*v = -scale^2*(a_p*w_p-f_p*u_p)")
    print(
        "4 beta^3*(g*v-b*x)/d^2 "
        "= (scale*a_p/d)^2*X_p"
    )
    print("SCOPE exact algebra only; transformed X_p bound remains open")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
