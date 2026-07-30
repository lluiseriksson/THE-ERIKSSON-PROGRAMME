# Local Gibbs thermodynamic limit in the uniform KP regime

## Charter

Construct, without compactness or subsequence extraction, the thermodynamic
limit of every bounded compatible local observable in the uniform KP regime.
The terminal object must be a positive normalized translation-invariant
infinite-volume state, independent of the finite-volume boundary condition,
and the finite-volume truncated-correlation estimate must pass to it.

The campaign does not modify `YangMills/RG/**` or `YangMills/OS/**`.
It is a lattice strong-coupling result and changes neither the `hRpoly`
frontier nor the recorded distance to the Clay problem.

## Non-negotiable proof architecture

The finite-volume Gibbs expectation is a quotient of two extensive objects.
Neither numerator nor partition function is to be shown convergent
separately.  The extensive far gas must cancel by an exact algebraic identity
at one volume:

```text
local marked factor
  * exp(clusterSum restricted to the literal far region - clusterSum full).
```

Only after this identity is established may estimates enter.  The remaining
cluster contribution is pinned to the finite marked support.  Common-window
terms agree exactly between two volumes; terms leaving the window are
controlled by `connectedLattice_pinned_tail_volumeUniform`.  The desired
comparison therefore has the form

```text
|E_N(O) - E_M(O)| <= tail_N(O, L) + tail_M(O, L),
```

with a volume-independent right-hand side tending to zero.  Completeness then
defines the limit of the whole sequence.  Abstract compactness or a convergent
subsequence does not close any brick.

## Brick ladder

1. **Finite-volume local substrate — green.**
   `CompatibleLocalObservable`, genuine normalized Gibbs expectations,
   positivity, normalization, bounded realization, and a volume-uniform
   pinned boundary remainder.
2. **Finite translations — green.**
   Exact covariance of realization and invariance of the finite-volume Gibbs
   expectation under each unit translation generator and finite lists of
   generators.
3. **Exact marked expansion — green.**
   The one-volume numerator identity, division by the partition function, and
   exact cancellation into the literal `farRegion` cluster difference.
4. **Common-window marginal/activity bridge — green.**
   Volume-independent edge and plaquette coordinates, exact product-marginal
   transport, and equality of marked and unmarked component integrals.
5. **Common-window cluster monomials — green.**
   `WindowPolymer`, exact preservation of incompatibility and activity, and
   equality of Ursell-weighted cluster monomials in any two fitting tori.
6. **Window decomposition and boundary estimate — in progress.**
   `LocalWindowCauchy.lean` now proves that a pinned cluster has a touching
   walk of length at most twice its total plaquette cardinality, decodes every
   seam-avoiding tuple exactly, and identifies its full Ursell/activity
   monomial in any second fitting volume.  `LocalRootedTail.lean` records the
   intrinsic `n+1` rooting factor, absorbs it with a unit-cardinality tilt,
   and proves the volume-uniform support boundary estimate using
   `connectedLattice_pinned_tail_volumeUniform` plus the necessary tilted
   tail.  `LocalCorrectionTail.lean` now performs the missing finite
   reindexing: it preserves the global total-size predicate through tuple
   symmetrization, fibers exactly over `X 0`, and proves that every finite
   partial correction tail is bounded by that rooted remainder.  It remains
   to identify the corresponding `tsum` from `clusterSum_sub_restrict`, split
   its common-window and tail pieces, and take the infinite partial-sum bound.
7. **Cauchy and infinite state — open.**
   Prove a quantitative Cauchy modulus for every observable, define the limit
   by completeness, and prove linearity, positivity, normalization, generator
   invariance, and hence finite-translation invariance.
8. **Boundary-condition independence and correlations — open.**
   Compare admissible boundary realizations by the same pinned-tail estimate
   and pass the finite-volume truncated-correlation bound to the limit.
9. **Canonical verification and paper — open.**
   Full `YangMillsCore` build, headline axiom oracles, ledger checkpoint, and
   an honest paper whose theorem claims do not run ahead of Lean.

## Current exact frontier

The finite unrooted-to-rooted reindexing is now theorem-fed:
`localCorrectionTailPartial_le_volumeUniform` gives

```text
finite correction tail
  <= exp(-ε L) * ((2 t) * (|SF| * 4d)).
```

The next theorem identifies the exact `clusterSum_sub_restrict` correction
with its size-filtered and complementary tuple series.  Clusters below the
cutoff which have sufficient seam margin decode to `WindowPolymer`s,
re-realize pointwise, and have exactly the same complete monomial in any
second fitting volume.  The complementary class is the tail just bounded.

The honest local-correction regime is the uniformly double-tilted KP window
at exponent `t + ε + 1`.  The extra `+1` is not an artefact: passing from the
symmetric predicate “some tuple member meets the marked region” to a pin at
coordinate zero costs `n+1`.  `LocalRootedTail.lean` proves this cost and does
not silently claim that the untilted pinned tail alone controls it.

No theorem in the current checkpoint asserts Cauchy convergence or the
existence of the infinite-volume state.
