# Preregistration: K4 regular-ball reach-feasibility probe

**Date:** 2026-07-22  
**Scope:** analytic falsification/design probe only; no K4 or G6 promotion.

The fixed parameters are `t=29/10`, complex radius `rho=7/100`, scaled
square radius `R=4`, phi-head `Phi=4*pi`, carrier `nuD_main`, Arb precision
140, and Taylor degree cap `N=16`.  The script computes a deliberately crude
closed-form complex modulus using the existing `|delta A|` disk bound, the
hyperbolic-sine bound for the scaled `S(delta,phi)`, and the exponential
modulus.  It then evaluates the explicit second-derivative Cauchy tail

```text
M * (N+1)(N+2) * (r/rho)^(N-1) / (1-r/rho),
       r = 59/2000,
```

and compares the result with half of the known `nuD` headroom at the positive
stress edge (fraction `0.2758`).  A failure for every `N<=16` is a terminal
incident for this architecture; a pass is still only a design candidate and
does not supply the missing moving-tail or t-uniform bounds.
