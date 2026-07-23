# R7/R8 symbolic heads — design record (2026-07-23)

The isolated symbolic derivation
`scripts/derive_surface_remainder_delta0_r7_design.py` completed after a
full simplification run (201.4 s).  It produced the following formal heads,
with `c` the registered positive carrier variable:

```text
R7(c) = (2085412*c^14 + 6775103*c^12 + 11636676*c^10
         - 52644752*c^8 + 1046587520*c^6 - 2880628992*c^4
         + 2254849024*c^2 - 513015808) / (33554432*c^21)

R8(c) = (19936*c^16 + 119595*c^14 + 323054*c^12 + 637408*c^10
         - 12653880*c^8 + 104539328*c^6 - 219463616*c^4
         + 153352416*c^2 - 33064504) / (524288*c^24)
```

This is a symbolic design output only.  The script has no interval sign
checker, no uniform tail bound, no `(delta,t)` remainder budget, and no
production/replay manifest.  Consequently it does not promote K2, G2, G6,
or any manuscript claim.  The next admissible step is to build an independent
exact-rational/interval checker for these heads and register its domain and
budget before observing numerical margins.

## Immediate sign audit

An independent exact-polynomial audit in `x=c^2` found one real root of each
numerator in the nominal interval `x in [1/2,1]`:

```text
R7 numerator root: x ~= 0.710545772008841
R8 numerator root: x ~= 0.682237812842058
```

The endpoint evaluations are positive at `x=1/2` and negative at `x=1` for
both numerators. Thus these raw heads cannot be used as globally positive
majorants on the registered carrier interval without a new decomposition or
an additional compensating argument. This is a negative design result, not a
counterexample to the Surface Theorem.
