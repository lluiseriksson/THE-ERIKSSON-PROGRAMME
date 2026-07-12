"""Degree-seven spatial remainder cell for the positive K2 lane."""

from types import FunctionType

from flint import arb

import surface_remainder_positive_physical_spatial3 as template
import surface_remainder_spatial_jet7 as j7
from surface_remainder_tjet import TJet, symmetric


# Rebind the already audited physical formulas to Jet7 operations.  The
# template files remain byte-invariant for their manifested certificate.
G = dict(template.__dict__)
G.update({
    "Jet3": j7.Jet7, "jet": j7.jet, "variable_x": j7.variable_x,
    "variable_y": j7.variable_y, "jadd": j7.jadd, "jneg": j7.jneg,
    "jmul": j7.jmul, "jscale": j7.jscale, "jinv": j7.jinv,
    "jsqrt": j7.jsqrt, "jexp": j7.jexp, "jsin": j7.jsin,
    "jcos": j7.jcos,
})


def _clone(name):
    source = getattr(template, name)
    function = FunctionType(source.__code__, G, name, source.__defaults__,
                            source.__closure__)
    G[name] = function
    return function


for _name in ("sconst", "sadd", "sneg", "sscale", "smul", "sinv",
              "ssqrt", "sexp", "spoly", "physical_radius2_floor",
              "_apply_radius2_floor", "physical_moment_parts",
              "linear_moment", "_remove_constant_and_linear"):
    globals()[_name] = _clone(_name)

PREC = template.PREC
hull = template.hull
variable_x, variable_y = j7.variable_x, j7.variable_y


def centered_cell(delta: arb, t, slo: arb, shi: arb,
                  alo: arb, ahi: arb, calibration):
    """Integrate degrees 0..6 and charge total spatial degree seven."""
    sm, am = (slo+shi)/2, (alo+ahi)/2
    rx, ry = (shi-slo)/2, (ahi-alo)/2
    center_prefactors, center_phase = physical_moment_parts(
        delta, t, variable_x(sm), variable_y(am))
    box_prefactors, box_phase = physical_moment_parts(
        delta, t, variable_x(hull(slo, shi)), variable_y(hull(alo, ahi)))
    qseries = [j7.jet(value) for value in calibration]
    for prefactors in (center_prefactors, box_prefactors):
        prefactors["KF"] = sadd(prefactors["KF"],
                                sneg(smul(qseries, prefactors["KD"])))
        prefactors["HDF"] = sadd(prefactors["HDF"],
                                 sneg(smul(qseries, prefactors["HDD"])))
    center = {name: smul(value, sexp([j7.jet(0)]+center_phase[1:]))
              for name, value in center_prefactors.items()}
    box = {name: smul(value, sexp([j7.jet(0)]+box_phase[1:]))
           for name, value in box_prefactors.items()}
    pc, pb = center_phase[0], box_phase[0]
    if isinstance(pc.get(0, 0), TJet):
        gx, gy = arb(pc.get(1, 0).v.mid()), arb(pc.get(0, 1).v.mid())
    else:
        gx, gy = arb(pc.get(1, 0).mid()), arb(pc.get(0, 1).mid())
    center_residual = j7.jexp(_remove_constant_and_linear(pc, gx, gy))
    box_residual = j7.jexp(_remove_constant_and_linear(pb, gx, gy))
    mx = [linear_moment(gx, 2*rx, order) for order in range(7)]
    my = [linear_moment(gy, 2*ry, order) for order in range(7)]
    mass = mx[0]*my[0]
    out = {}
    for name in center:
        coefficients = []
        for cc, bb in zip(center[name], box[name]):
            fc, fb = j7.jmul(cc, center_residual), j7.jmul(bb, box_residual)
            retained = sum((fc.get(i, degree-i)*mx[i]*my[degree-i]
                            for degree in range(7)
                            for i in range(degree+1)), arb(0))
            radii = []
            for derivative in ("v", "d", "d2", "d3", "d4"):
                radii.append(sum((arb(getattr(fb.get(i, 7-i), derivative)
                                      .abs_upper())*rx**i*ry**(7-i)
                                  for i in range(8)), arb(0))*mass)
            carrier = retained+symmetric(*radii)
            coefficients.append(4*pc.get(0, 0).exp()*carrier)
        out[name] = coefficients
    return out
