"""Moving-band Gaussian rate using its nonzero physical deficit.

On the omitted band ``max(s,alpha)>=physical_inner`` at least one of
``p=sin(s/2)^2`` and ``q=sin(alpha/2)^2`` is bounded below.  Since
``p,q<=sin(0.6)^2<c^2`` on the physical square and ``c^2>=1/2``, the exact
deficit ``w=p+q-p*q/c^2`` is increasing in either variable.  Hence
``w>=sin(physical_inner/2)^2`` and the denominator in
``1-sqrt(1-w)=w/(1+sqrt(1-w))`` is strictly smaller than two throughout the
band.  No manifested helper imports this design module.
"""

from fractions import Fraction

from flint import arb

import surface_remainder_delta0_outer_domain_v6 as v6
import surface_remainder_delta0_tlocal_band_design as local
from surface_bessel_integral_remainder import aq


def gaussian_rate_on_band(cmin: arb, physical_inner: Fraction) -> arb:
    if not Fraction(1) <= physical_inner < Fraction(6, 5):
        raise ValueError("physical band split must lie in [1,6/5)")
    p_floor = (aq(physical_inner)/2).sin()**2
    denominator = 1+(1-p_floor).sqrt()
    return local.gaussian_rate_from_cmin(cmin)*2/denominator


def direct_moving_band_value_coefficients_from(
        delta_max: Fraction, physical_inner: Fraction, t_hi: arb):
    dmax = v6._require_delta(delta_max)
    cmin = local.cmin_from_t_hi(t_hi)
    rate = gaussian_rate_on_band(cmin, physical_inner)
    majorants = local.moment_majorants(delta_max, cmin)
    exact_radius = aq(physical_inner)*(1/dmax).sqrt()
    scaled_floor = int((10*exact_radius).floor().unique_fmpz())
    radius_lower = Fraction(scaled_floor, 10)
    if not aq(radius_lower) < exact_radius:
        raise AssertionError("physical band radius must be strictly interior")
    out = {}
    for name, series in majorants.items():
        term = series[0]
        threshold = rate/dmax
        from fractions import Fraction as F
        assert threshold > aq(F(term.p+2, 2)+5)
        out[name] = local.radial_tail_at_rate(
            term, aq(radius_lower), rate)/dmax**5
    return radius_lower, out

