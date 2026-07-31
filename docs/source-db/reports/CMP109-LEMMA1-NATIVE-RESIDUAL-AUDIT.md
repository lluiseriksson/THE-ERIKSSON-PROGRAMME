# CMP109 Lemma-1 native residual audit

Date: 2026-07-31

## Result

The Lemma-1 contribution is retained as a disjoint finite family of its
literal connected `2`-block localization domains.  Only the physical support
is mapped to the CMP116 `M`-block lattice.  No quotient of coincident supports
is taken, so no coarsification-fibre multiplicity is hidden in the residual
activity.

The source-facing certificate
`CMP109Lemma1Eq136SourceCertificate` fixes both the residual and its
small-field predicate to the literal CMP109 equation-(2.12) objects.  It has
strictly positive `E0`, contains the zero field, and assumes equation (1.36)
only on the printed small-field region.  Thus neither the zero-amplitude nor
the empty-domain witness can inhabit the certificate.

## Machine-checked endpoints

- `cmp109Lemma1NativeDomainFamily` and
  `cmp109Lemma1NativeDomain_blocks_injective` retain every native domain as a
  distinct index.
- `cmp109Eq212Lemma1EnergyDifference_eq_sum_indexedNativeResidualActivity`
  is the exact finite decomposition of the Lemma-1 energy difference over
  that index.
- `connectedDomainFamily_rooted_sum_pow_card_le` is the generic rooted
  lattice-animal estimate.
- `cmp109Lemma1NativeDomainFamily_coarsenedRoot_weighted_exp_metric_sum_le`
  combines the literal four-dimensional degree bound, the exact `M^4`
  preimage count of a coarse root, and CMP116 equation (2.30).
- `cmp109Lemma1NativeIndexed_rooted_residual_le` derives the complete
  centered equation-(2.20) rooted residual sum with the explicit bound
  `cmp109Lemma1NativeRootBound`.

The last theorem exposes two scalar assumptions, one for each printed decay
rate:

```text
64 * exp(-(((1 - 2*delta)*kappa)/24)) < 1
64 * exp(-((delta*kappa)/24)) < 1.
```

These are lattice-animal entropy conditions.  Their real fugacities are not
the natural exponent `q : Nat` in `M^q`, and neither is definitionally the
terminal patched-parametrix `rate` used by `shell_small`.

## Honest frontier

This checkpoint discharges the `rooted_residual` combinatorics for the native
Lemma-1 indices.  It does **not** prove:

- the analytic equation-(1.36) bound stored in
  `CMP109Lemma1Eq136SourceCertificate.bound`;
- `domain_subset` for the final contour carrier;
- `volume_budget` or the joint scalar smallness regime;
- construction of a complete `CMP116Eq226...TermSource`.

The next vertical step is to append these native indices to the direct
equation-(80) indices in the terminal domain ledger, prove the corresponding
support containment, and consume the explicit root bound in the volume
budget.  The sector Lemma-1 analytic estimate remains the principal source
obligation.

## Verification

The five focal audit modules cover 47 declarations: 46 depend on exactly
`[propext, Classical.choice, Quot.sound]`, while
`cmp109Lemma1NativeDomain_blocks_injective` uses the smaller set
`[propext, Quot.sound]`.  No project axiom or `sorry` is introduced.

The Colab Pro+ high-RAM replica used the pinned environment:

```text
leanprover/lean4:v4.29.0-rc6
Mathlib 07642720480157414db592fa85b626dafb71355b
ProofWidgets 2e58165a9dcdca9837b666528f974299ee1a51cc
```

The final public commit and immutable source links are added at publication
time; until then this report must not be read as a published checkpoint.
