"""Verify that the registered 150000*delta^6 target fits Theta3."""

from flint import arb, ctx

from surface_remainder_arb_jet2 import hull


def check(boxes: int = 2000):
    ctx.prec = 140
    c0, delta = arb(2).sqrt()/2, arb(1)/20
    worst = None
    for index in range(boxes):
        c = hull(c0+(1-c0)*index/boxes,
                 c0+(1-c0)*(index+1)/boxes)
        leading = (4*c**2-1)/(8*c**3)
        r4 = ((28*c**8+41*c**6-1464*c**4+1856*c**2-500)
              /(1024*c**12))
        r5 = ((12940*c**10+16077*c**8+173288*c**6-1300912*c**4
               +1358400*c**2-346112)/(262144*c**15))
        r6 = ((8148*c**12+17095*c**10+10768*c**8+634576*c**6
               -2557408*c**4+2283296*c**2-549376)/(131072*c**18))
        slack = arb("1.10")*leading/c**2+arb("0.5")/c**3+arb("0.05")
        available = (slack-arb(r4.abs_upper())*delta
                     -arb(r5.abs_upper())*delta**2
                     -arb(r6.abs_upper())*delta**3)/delta**4
        lower = arb(available.lower())
        if worst is None or lower < worst:
            worst = lower
    assert worst > 150000
    print("R7 BUDGET PASS: coefficient 150000 fits; worst_lower=%s" %
          worst.str(20), flush=True)
    return worst


if __name__ == "__main__":
    check()
