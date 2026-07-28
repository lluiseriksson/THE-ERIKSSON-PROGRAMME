"""Cancellation-preserving sign judge for the finite five-family bridge.

The sign of ``H`` is the sign of ``P0`` because ``B0>0``.  Rather than form
the difference of two large products, this helper factors out ``B0`` and
judges

    Q = A0*(1 - lambda**2*B1/(4*B0)) + lambda**2*A1/4.

It is a design module until a separate production/replay contract is written.
"""
from flint import arb
import surface_right_edge_five_family_central_design as central

def assemble_ratio(delta, lam, families):
    U0,U1,U2,B0,B1 = families
    y=(delta*lam/2)**2
    s=central.elementary_series(y,'s'); sy=central.elementary_series(y,'sy')
    j=central.elementary_series(y,'j'); jy=central.elementary_series(y,'jy')
    A0=j*delta**2*U0+2*s*U1
    A1=jy*delta**4*U0+(j+2*sy)*delta**2*U1+2*s*U2
    q=A0*(1-lam**2*(B1/B0)/4)+lam**2*A1/4
    return q,B0

def central_ratio(delta,lam,side=arb(5)/2,qgrid=80,rgrid=16,thetagrid=4,phigrid=4,budgets=()):
    vals=central.central_families(delta,lam,side=side,qgrid=qgrid,rgrid=rgrid,thetagrid=thetagrid,phigrid=phigrid)
    if budgets: vals=tuple(v+b*arb('0 +/- 1') for v,b in zip(vals,budgets))
    return assemble_ratio(delta,lam,vals)
