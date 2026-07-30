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
6. **Window decomposition and local-correction Cauchy estimate — green.**
   `LocalWindowCauchy.lean` now proves that a pinned cluster has a touching
   walk of length at most twice its total plaquette cardinality, decodes every
   seam-avoiding tuple exactly, and identifies its full Ursell/activity
   monomial in any second fitting volume.  `LocalRootedTail.lean` records the
   intrinsic `n+1` rooting factor, absorbs it with a unit-cardinality tilt,
   and proves the volume-uniform support boundary estimate using
   `connectedLattice_pinned_tail_volumeUniform` plus the necessary tilted
   tail.  `LocalCorrectionTail.lean` performs the finite
   reindexing: it preserves the global total-size predicate through tuple
   symmetrization, fibers exactly over `X 0`, and proves that every finite
   partial correction tail is bounded by that rooted remainder.
   `LocalCorrectionSeries.lean` identifies the exact
   `clusterSum_sub_restrict` correction with a summable complex series and
   splits it into below-cutoff and tail parts.  The centering, common-window,
   and small-cluster transport modules then identify every below-cutoff layer
   exactly in two admissible volumes.  `LocalSmallCorrectionCauchy.lean`
   combines that equality with the two rooted tails to obtain a direct
   two-volume estimate for the complete local correction exponent.
7. **Cauchy and infinite state — green.**
   `ThermodynamicLimit.lean` proves a quantitative Cauchy theorem for the
   complete finite-volume sequence, defines the limit by completeness of
   `ℂ`, and bundles its real part as a positive normalized real linear
   functional.  It is invariant under each positive unit translation
   generator and every finite word in those generators.  No compactness or
   subsequence is used.  `ThermodynamicNonvacuity.lean` constructs the
   uniform regime for the physical `SU(2)`, `d=2` Wilson energy throughout
   the explicit punctured interval `0 < |β| ≤ 10^-5`.
8. **Boundary-condition comparison and correlations — green, with explicit
   scope.**
   `LocalFreeBoundary.lean` constructs the genuine centered free box by
   deleting the seam and identifies its polymer gas literally with a
   restriction.  `LocalBoundaryCorrection.lean` proves the exact
   inclusion-exclusion identity and a same-volume periodic/free estimate
   from the support-to-seam pinned tail.
   `FreeBoundaryThermodynamicLimit.lean` defines an explicit cofinal
   sequence of centered free boxes and proves that the complete sequence
   converges to the same infinite value as periodic boundary conditions.
   This is independence between the two boundary realizations actually
   constructed here; it is not a theorem about arbitrary boundary
   conditions.  `ThermodynamicCorrelation.lean` identifies the normalized
   two-plaquette quotient bound with the local truncated correlation and
   passes it to the infinite state under the explicit eventual realization
   and separation hypotheses.
9. **Canonical verification and paper — complete.**
   All focal modules, the direct `YangMillsCore.lean` root, and ten headline
   axiom oracles are green.  With all nine dependency HEADs matching
   `lake-manifest.json` and a process-local `safe.directory` setting for the
   ownership-mismatched checkout, the canonical invocation terminated
   literally with `Build completed successfully (8458 jobs).` and empty
   stderr.  No dependency was deleted or updated.  The paper retains the
   exact coupling range, generator/finite-word translation scope, and
   periodic-versus-centered-free boundary scope.

## Current exact frontier

The mathematical bricks are closed at the stated scope.  The terminal
whole-sequence endpoints are

```text
cauchySeq_localGibbsExpectation_kpUniform
tendsto_infiniteLocalGibbsExpectation
infiniteLocalGibbsState
tendsto_freeBoundaryThermodynamicExpectation
abs_infiniteLocalGibbsTruncatedCorrelation_le_twoPlaquette
```

The Cauchy modulus is

```text
thermodynamicCauchyBound(q)
  = 2 * markedOuterTailBound(q)
    + markedSmallLayerCauchyBound(q,q),
```

and tends to zero.  The small-layer term contains the literal
support-pinned boundary remainder proved from
`connectedLattice_pinned_tail_volumeUniform`; the intrinsic tuple-rooting
factor is absorbed by the honest unit-cardinality tilt.

The free exhaustion uses
`freeBoundaryVolumeIndex O q = thermodynamicVolumeThreshold O q + q`.
At that same volume the norm of periodic minus free expectation is eventually
bounded by `thermodynamicCauchyBound(q)`.  Since the chosen volumes are
cofinal, the periodic subsequence converges to the already constructed
whole-sequence limit, and the free error tends to zero by squeezing.  This
proves convergence of the complete explicitly indexed free sequence, not an
existence statement obtained from compactness.

Remaining work is verification and exposition, not an unproved
thermodynamic-limit bridge: run the canonical Lake root build in a networked
shell, record its literal job count, commit/push the terminal modules and
acta, and produce the paper.  Full translation-group invariance and arbitrary
boundary conditions are outside the proved API and must not be inferred from
the generator/finite-word and periodic/centered-free endpoints.
