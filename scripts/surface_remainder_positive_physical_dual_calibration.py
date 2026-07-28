"""Degree-five cell with separate exact KF and HDF calibrations."""

from flint import arb

import surface_remainder_positive_physical_spatial3 as p
from surface_remainder_tjet import symmetric


PREC = p.PREC


def centered_cell(delta, t, slo, shi, alo, ahi, qk, qh):
    sm, am = (slo+shi)/2, (alo+ahi)/2
    rx, ry = (shi-slo)/2, (ahi-alo)/2
    cp, cphase = p.physical_moment_parts(
        delta, t, p.variable_x(sm), p.variable_y(am))
    bp, bphase = p.physical_moment_parts(
        delta, t, p.variable_x(p.hull(slo, shi)),
        p.variable_y(p.hull(alo, ahi)))
    qkj, qhj = [p.jet(x) for x in qk], [p.jet(x) for x in qh]
    for values in (cp, bp):
        values["KF"] = p.sadd(values["KF"], p.sneg(p.smul(qkj, values["KD"])))
        values["HDF"] = p.sadd(values["HDF"], p.sneg(p.smul(qhj, values["HDD"])))
    center = {name: p.smul(value, p.sexp([p.jet(0)]+cphase[1:]))
              for name, value in cp.items()}
    box = {name: p.smul(value, p.sexp([p.jet(0)]+bphase[1:]))
           for name, value in bp.items()}
    pc, pb = cphase[0], bphase[0]
    gx, gy = arb(pc.get(1, 0).v.mid()), arb(pc.get(0, 1).v.mid())
    cr = p.jexp(p._remove_constant_and_linear(pc, gx, gy))
    br = p.jexp(p._remove_constant_and_linear(pb, gx, gy))
    mx = [p.linear_moment(gx, 2*rx, order) for order in range(5)]
    my = [p.linear_moment(gy, 2*ry, order) for order in range(5)]
    mass = mx[0]*my[0]
    out = {}
    for name in center:
        row = []
        for cc, bb in zip(center[name], box[name]):
            fc, fb = p.jmul(cc, cr), p.jmul(bb, br)
            retained = sum((fc.get(i, d-i)*mx[i]*my[d-i]
                            for d in range(5) for i in range(d+1)), arb(0))
            radii = [sum((arb(getattr(fb.get(i, 5-i), derivative).abs_upper())
                          *rx**i*ry**(5-i) for i in range(6)), arb(0))*mass
                     for derivative in ("v", "d", "d2", "d3", "d4")]
            row.append(4*pc.get(0, 0).exp()*(retained+symmetric(*radii)))
        out[name] = row
    return out
