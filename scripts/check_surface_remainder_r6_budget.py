"""Verify that the registered 7600*delta^5 target fits Theta3."""

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
        slack = arb("1.10")*leading/c**2+arb("0.5")/c**3+arb("0.05")
        available = (slack-arb(r4.abs_upper())*delta
                     -arb(r5.abs_upper())*delta**2)/delta**3
        lower = arb(available.lower())
        if worst is None or lower < worst:
            worst = lower
    assert worst > 7600
    print("R6 BUDGET PASS: coefficient 7600 fits; worst_lower=%s" %
          worst.str(20), flush=True)
    return worst


if __name__ == "__main__":
    check()
