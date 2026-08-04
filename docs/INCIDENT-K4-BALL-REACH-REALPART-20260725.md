# Incident — K4 real-part modulus remains unusable on the registered disk

Date: 2026-07-25. The preregistered driver
`scripts/probe_surface_k4_ball_reach_realpart.py` was run at the frozen
parameters `t=29/10`, `rho=7/100`, `R=4`, `Phi=12566371/1000000`,
`r=59/2000`, Arb-140, and `N<=16`, using the new rectangular complex cover.

The module and its four unit tests pass, and the disk guard is strict. The
full design judge nevertheless fails:

```text
main   exponent_real_upper  145270.960733876...
mirror exponent_real_upper  120518.082928361...
best tail2                 ~1.9365e63092
headroom_half              0.3621
K4 BALL REACH REALPART FAIL
```

The bound is finite and sound as a rectangular-cover enclosure, but its
dependency/branch overestimation is much worse than the old crude modulus.
This rejects this particular A1 realization; it is not a counterexample to
the regular-ball theorem. The output remains design-only and no K4,
`S1'''/S2'''`, G1, G2, or G6 state changes.

The next admissible K4 route must use a genuinely sector-aware real-part
argument (or abandon the full complex disk for a different analytic patch),
not merely a rectangular absolute-value enclosure.
