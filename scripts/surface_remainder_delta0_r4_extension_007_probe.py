"""Adversarial two-core/seven-annulus probe for delta<=0.007."""

from fractions import Fraction
from flint import arb, ctx
import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v4 as outer
from surface_remainder_delta0_companion_error import moment_error_coefficients
from surface_remainder_delta0_fourth_coefficient import target_y3
from surface_remainder_delta0_r4_extension_probe import assemble_y_through_four
from surface_remainder_s2_direct_judge import closed_forms

DELTA_MAX = Fraction(7, 1000)
CORE_BOXES = ((Fraction(0), Fraction(1, 200)),
              (Fraction(1, 200), Fraction(3, 500)),
              (Fraction(3, 500), DELTA_MAX))
ANNULUS_BOXES = tuple((Fraction(j,1000), Fraction(j+1,1000))
                      for j in range(7))
PHYSICAL_INNER = Fraction(11, 10)
GRIDS = (96, 192, 384)

def judge(lo, hi, grid):
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    core = []
    for dlo, dhi in CORE_BOXES:
        lane = regular.hull(regular.aq(dlo), regular.aq(dhi))
        core.append(regular.parallel_integrate_coefficients(lane, t, grid))
    c4, kd = arb(0), None
    mags = {n:arb(0) for n in ("kd","kf","hdd","hdf")}
    for dlo, dhi in ANNULUS_BOXES:
        if dhi <= Fraction(1, 200): source = core[0]
        elif dhi <= Fraction(3, 500): source = core[1]
        else: source = core[2]
        moments = outer.add_outer_derivatives_box_to(
            source, dlo, dhi, PHYSICAL_INNER)
        y = assemble_y_through_four(moments, t); row=y.coeffs()+[arb(0)]*5
        c4=max(c4,arb(row[4].abs_upper()))
        low=arb(moments["kd"].coeffs()[0].lower()); kd=low if kd is None else min(kd,low)
        for n,v in moments.items(): mags[n]=max(mags[n],arb(v.coeffs()[0].abs_upper()))
    lane=regular.hull(arb(0),regular.aq(DELTA_MAX)); _,_,r3,theta=closed_forms(t)
    head=arb((r3+target_y3((t/4).cos())*lane).abs_upper())
    radius,bands=outer.direct_moving_band_value_coefficients_from(DELTA_MAX,PHYSICAL_INNER)
    companion=moment_error_coefficients().__dict__; errors={n:bands[n]+companion[n] for n in bands}
    value=outer.normalized_y_error_from_moment_coefficients(DELTA_MAX,kd,mags,errors)
    d=regular.aq(DELTA_MAX); return radius,c4,value,theta-head-(c4+value)*d**2

def main():
    ctx.prec=140; lo,hi=list(regular.sealed.born_t_boxes())[-1]
    print("R4 007 DESIGN",CORE_BOXES,ANNULUS_BOXES,"physical",PHYSICAL_INNER,"grids",GRIDS,flush=True)
    for grid in GRIDS:
        try: radius,c4,value,margin=judge(lo,hi,grid)
        except (ValueError,ZeroDivisionError) as e:
            print("TRY",grid,"UNRESOLVED",type(e).__name__,flush=True); continue
        lower=arb(margin.lower()); print("TRY",grid,"radius",radius,"Y4",c4,"C_value",value,"margin_lower",lower,flush=True)
        if lower>0: print("R4 007 ADVERSARIAL DESIGN PASS; COVER REQUIRED"); return 0
    print("R4 007 ADVERSARIAL DESIGN FAIL"); return 1

if __name__=="__main__": raise SystemExit(main())
