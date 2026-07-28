# H_tail companion-budget obstruction (2026-07-21)

**Status:** `SUPERSEDED-NEGATIVE`; no gate promotion.

## Correction after the full-moment normalization incident (2026-07-28)

The candidate conclusion below was computed before the correction recorded in
`INCIDENT-DELTA0-Y-DOUBLE-NORMALIZATION-20260728.md`.  With the corrected
full-moment propagation, the executable outward-rounded comparison gives

```text
order-four equivalent delta^4 coefficient = 3854.406648455...
order-five equivalent delta^4 coefficient = 253.341545441...
beta1*Theta3(1)                         = 115.082465277...
order-five / budget                     = 2.201391366...
```

Thus the order-five sufficient route also exceeds the registered budget.  The
executable audit now preserves this as a rigorous negative result.  It neither
disproves `H_tail` nor carries any load in the terminal weak-main proof.

## Historical candidate record (superseded)

The existing convergent integral remainder for the scaled Bessel factors is a
valid half-line value enclosure.  Its order-four propagation through the
carrier quotient is not strong enough at the worst splice point
`beta=beta1`, but the repository already contains an order-parametric
extension.  The comparison is now checked by the executable
`scripts/audit_surface_h_tail_companion_budget.py`.

With the fixed inputs of the existing companion-error contract
(`delta_max=0.001`, `KD >= 2`, moment absolute upper `<= 10`), the run gives

```text
Theta3(1)                 = 1.0357421875...
beta1*Theta3(1)                         = 115.082465277...
order-four equivalent delta^4 coefficient = 681.369269486...
order-five equivalent delta^4 coefficient = 4976.097909313... * beta1^-1
                                            = 44.78... (at beta1)
```

In the executable comparison the order-four equivalent coefficient is above
the registered `beta1*Theta3(1)` threshold, whereas the order-five route is
below it.  The four order-four moment coefficients are retained as a
provenance baseline; the order-five constants come from
`surface_remainder_companion_error_ordered.py` and are propagated with the
same outward-rounded quotient perturbation.

This is a real candidate for the next terminal lemma, but it is not yet a
certificate.  The remaining obligations are:

1. promote the order-five companion charge into the same fixed-domain,
   outer-tail and `t`-union judge used by K2; and
2. combine it with a direct joint normalized-carrier remainder, or prove the
   remaining extracted-chain and spatial-completion charges uniformly.

The order-five budget pass alone does not remove the separate outer-tail,
weighted S1'''/S2''' and global relay obligations.  Until those are proved
with a terminal transcript and replay, `H_tail`, G2, and G6 remain unchanged.

The existing 158-born-box R6 companion design was also rerun from
`scripts/probe_surface_remainder_r6_companion_charge.py`: its worst order-five
companion charge is `2.05340511393314865`, against the registered R6 target
`7600`.  This confirms that the higher-order charge is numerically viable on
the frozen born boxes, but the transcript itself remains explicitly
`DESIGN_ONLY` because completion, outer-domain integration, and the literal
weighted S1'''/S2''' sums are not yet discharged.
