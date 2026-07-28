from flint import ctx

import verify_surface_remainder_k4_poisson as oracle


def test_poisson_oracle_overlaps_direct_bessel_value():
    ctx.prec = 100
    for nu in (0, 1):
        integral, target = oracle.verify_case(30, nu, 2048)
        assert integral.overlaps(target)
