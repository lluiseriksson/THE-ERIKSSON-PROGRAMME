# S2 t-jet local probe — pre-registration

**Registered:** 2026-07-21, before recording the local transcript

**Scope:** one fixed point, `beta=20`, `t=2.9`, on the exact physical
main square `[0,6/5]^2`.  The probe uses `raw_integrand_parts_t` and the
`Jet2` convention in which `c2` stores the second derivative (the factor
`1/2` is applied only when a Taylor remainder is assembled).  No finite
differences are used.

The target diagnostic is the local S2 budget form

```text
0.5 * |Y''(t)| <= Theta3(c),  c = cos(t/4).
```

The transcript must print script and runtime provenance, exact Arb
enclosures for `Y_t0`, `Y_t1`, `Y_t2`, `Theta3`, and the outward-rounded
`half_abs_upper`, together with the explicit candidate-only verdict.

This is not a uniform `(delta,t)` cover, does not address the `delta=0`
extension, and does not certify K2, K4, G2, G6, or the weighted S1'''/S2'''
ledger.  A passing local enclosure is therefore evidence about the
implementation path only; it cannot remove a manuscript slot or change a
closure-gate state.
