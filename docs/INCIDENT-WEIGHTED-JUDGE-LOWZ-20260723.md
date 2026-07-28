# Incident: weighted S1''' scaffold reaches unresolved low-z cells

Date: 2026-07-23
Status: design-only; no K2/K4/S1'''/S2''' promotion

The existing `surface_remainder_weighted_judge_design.py` was exercised on a
small positive-delta box.  Its localized cell evaluator reached
`surface_remainder_centered_prefactor.outer_derivatives`, which deliberately
raises

```
ValueError: endpoint-recurrence path requires z > 4; use entire series
```

when a cell's Bessel argument is in the low-z region.  Coarse cells can also
produce non-finite radicand enclosures before refinement.  This is exactly the
K2 low-z/regular-extension obligation, not evidence that the weighted bound is
false.

The scaffold therefore cannot be used as a certificate or as a source of
S1'''/S2''' margins.  A production route must add the registered entire low-z
extension, split cells until the radicand is certified, and then perform the
literal weighted partition sums with production/replay provenance.

The isolated low-z dispatcher was subsequently inserted into the centred-
delta complement path as a diagnostic.  At
`delta=[0.0660,0.0661]`, `t=2.9`, the born complement partition still reached
non-finite cells and was rejected before a weighted total could be formed.
The successful factored-band smoke therefore covers only the scaled core; it
does not silently include the outer complement.
