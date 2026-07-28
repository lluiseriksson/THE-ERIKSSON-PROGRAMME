"""Verify that the pre-registered 384*delta^4 target fits Theta3."""

from flint import arb, ctx

from surface_remainder_arb_jet2 import hull


def check(boxes: int = 1000):
    ctx.prec = 140
    c0 = arb(2).sqrt()/2
    delta = arb(1)/20
    worst = None
    worst_box = None
    for index in range(boxes):
        c = hull(c0+(1-c0)*index/boxes,
                 c0+(1-c0)*(index+1)/boxes)
        leading = (4*c**2-1)/(8*c**3)
        r3 = (-12*c**6-485*c**4+796*c**2-224)/(1024*c**9)
        r4 = ((28*c**8+41*c**6-1464*c**4+1856*c**2-500)
              /(1024*c**12))
        r3_abs = arb(r3.abs_upper())
        theta3 = (r3_abs+arb("1.10")*leading/c**2
                  +arb("0.5")/c**3+arb("0.05"))
        available = (theta3-r3_abs-arb(r4.abs_upper())*delta)/delta**2
        lower = arb(available.lower())
        if worst is None or lower < worst:
            worst, worst_box = lower, index
    assert worst > 384
    print("R5 BUDGET PASS: coefficient 384 fits; "
          "worst_lower=%s c_box=%d/%d" %
          (worst.str(20), worst_box, boxes), flush=True)
    return worst


if __name__ == "__main__":
    check()
