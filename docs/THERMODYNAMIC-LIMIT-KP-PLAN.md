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
6. **Window decomposition and boundary estimate — open.**
   Split pinned clusters into common-window terms and clusters leaving the
   window.  Reindex the first class exactly and dominate the second with
   `connectedLattice_pinned_tail_volumeUniform`.
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

The next theorem is the finite tuple decomposition.  A cluster with a marked
plaquette having sufficient seam margin and total polymer cardinality below
the chosen cutoff decodes to a tuple of `WindowPolymer`s.  Re-realization is
exact, so `WindowPolymer.clusterMonomial_toWeightedPolymer_eq` identifies its
term in two volumes.  Failure to decode forces the cluster to cross the
window seam; the touching-path estimate converts that event into a lower
bound on total cluster size, which is exactly the tail variable used by
`connectedLattice_pinned_tail_volumeUniform`.

No theorem in the current checkpoint asserts Cauchy convergence or the
existence of the infinite-volume state.
