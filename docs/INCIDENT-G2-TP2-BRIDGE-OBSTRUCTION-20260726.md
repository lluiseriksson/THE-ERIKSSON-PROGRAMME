# Killed bridge is not globally TP2 (2026-07-26)

The tempting probabilistic closure route would use total positivity of the
killed von Mises step kernel

```text
q_beta(u,v) = exp(beta*cos(u-v)) - exp(beta*cos(u+v)).
```

That hypothesis is false globally.  The executable Arb witness
`scripts/certify_killed_von_mises_not_tp2.py` evaluates the exact determinant
at `beta=3`, `u=(3*pi/20,4*pi/20)`, and `v=(15*pi/20,16*pi/20)`, and proves a
strictly negative outward-rounded value.  Therefore a TP2/MLR bridge proof
cannot be inserted into the Surface-Theorem relay without an additional
restricted-domain decomposition that handles the sign-changing minors.

This is a route obstruction only.  It neither disproves ratio monotonicity nor
changes G2, K2, K4, S1'''/S2''', or G6.
