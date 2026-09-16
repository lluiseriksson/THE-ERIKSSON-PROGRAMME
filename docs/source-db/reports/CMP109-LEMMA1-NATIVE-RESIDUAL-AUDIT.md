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

The printed region has been checked visually against page 9 of the primary
CMP116 PDF, equations (1.34)--(1.36).  It says
`|B| < epsilon1 * gk^{-1} on Y` and immediately states that the localized
function depends on `B` restricted to the interior of `Y`.  The earlier Lean
predicate using the ambient sup norm was therefore too strong.  The corrected
predicate takes the source sup norm only after projecting to the bilateral
fluctuation bonds whose two endpoint sites lie in the native carrier
`Y.blocks`.  Using `Y.bondSupport` would be type-incorrect: that support lies
on the additional order-two refined lattice, whereas the fluctuation field
is indexed on the same site lattice as `Y.blocks`.

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
- the source theorem that the reconstructed residual containing the global
  nonlinear correction `D(B)` satisfies that per-domain analytic contract;
- `domain_subset` for the final contour carrier;
- `volume_budget` or the joint scalar smallness regime;
- construction of a complete `CMP116Eq226...TermSource`.

The native and direct indices have since been appended in the terminal domain
ledger.  The next cutoff step must keep the source small-field carrier
separate from the centered region `Z0`: it is derived from the combined
domain family exactly as in equations (2.3)/(2.14), while the admissible
large-field set `P` lies in the disjoint exterior carrier.  The sector
Lemma-1 analytic estimate remains the principal source obligation.

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
