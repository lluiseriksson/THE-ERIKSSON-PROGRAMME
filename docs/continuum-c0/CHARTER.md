# CONTINUUM-C0 charter

Branch base: `81721890ad3e111d73cbe45074d42ec698ce07b2`
(the fetched `origin/main` tip when the isolated branch was created).

Current `origin/main` after the later audit fetch:
`1f81ec43404ae2a8c72a8c934807d4b03b8680c9`.  The branch base is seven
commits behind.  The complete delta is confined to the explicitly excluded
Paper 13 lane (`YangMills/OS/SpatialOS.lean` and its paper), `DASHBOARD.md`,
and the global `oracle_check.lean`.  No C0-owned file overlaps it.  This
branch is intentionally not rebased across those active lanes.

## Scope

CONTINUUM-C0 supplies language for asking a scaling-limit question without
asserting that four-dimensional continuum Yang--Mills exists.  Its formal
objects are:

1. a strictly positive spacing sequence `aₙ → 0`;
2. explicit scale-indexed maps from a deliberately minimal real test algebra
   to `IntegerLocalObservable`;
3. a sequence of states definitionally constructed by the existing
   `integerInfiniteLocalGibbsState` theorem from genuine Gibbs data;
4. pointwise convergence, in the ordinary topology of `ℝ`, of every embedded
   test expectation;
5. the functional value forced by that convergence; and
6. limit-stability theorems for normalization, positivity, real linearity,
   full `ℤ^d` translation invariance, and conditional real reflection
   positivity.

There is no structure named `ContinuumState`, no input field containing an
arbitrary state, and no declaration named `ContinuumExists`.

## Formal contract

`GibbsStateSequence` stores a probability measure, bounded measurable
plaquette energy, coupling sequence, and one proved `UniformLocalKPRegime` per
scale.  Its `state n` is not data: it is
`integerInfiniteLocalGibbsState` applied to those fields.

`HasWeakLimit S E` means

```text
∀ F, ∃ x : ℝ,
  Tendsto (fun n => (S.state n) (E.atScale n F)) atTop (𝓝 x).
```

The selected `weakLimitValue` is therefore downstream of convergence of
actual discrete evaluations.  The definition does not quantify over, or ask
the caller to supply, a continuum functional.  `WeakConvergesTo` is only a
comparison relation, and `weakLimit_unique` proves that any two comparison
functionals satisfying it agree pointwise.

`HasWeakLimit` alone is deliberately only a topology and does not prevent a
zero embedding.  Non-vacuity comes from the separate
`AlgebraCompatibility.map_one` gate and from the compiled canonical
point-cylinder instance.  The normalization transport theorem requires the
compatibility record explicitly.

`AlgebraCompatibility`, `OrderCompatibility`,
`GeometricScalingCompatibility`, and `ReflectionCompatibility` make the
observable-map obligations explicit.  `GeometricScalingCompatibility` is
only a numerical witness that a supplied `latticeRadius` has the declared
scaling.  Its current type does not derive that radius from
`E.atScale n F`; a genuine producer must additionally prove that linkage.
Thus merely attaching `aₙ` to a fixed observable, or supplying zero radii,
is not certified here as geometric scaling.

`ScaleConventionCompatible` separately names the obligation that this
spacing agree with a spacing convention used by an existing repository
construction.  In particular, C0 does not silently identify its numerical
sequence with the RG lane's `scaleSpacing`/`towerSize` convention.

## What is proved here

- `aₙ = 1/(n+1)` is positive and tends to zero.
- Every `UniformLocalKPRegime d B β` with `B > 0` forces
  `|β| < 1 / (((16d+1)^2)B)`.  For `d=4`, `B=2`, this is the exact bound
  `|β| < 1/8450`.
- Therefore no coupling schedule `βₙ → +∞` can remain in the existing
  four-dimensional `B=2` KP regime.  This is a proved obstruction on the
  current state producer, not evidence against a continuum construction by
  other methods.
- Pointwise weak convergence preserves:
  - the value of the unit;
  - addition and real scalar multiplication;
  - the selected positive cone;
  - every integer translation, including inverses; and
  - reflection positivity when the exact finite-scale RP producer and the
    reflection/multiplication embedding compatibilities are supplied.
- Vanishing of the actual discrete truncated-correlation sequence forces
  factorization of the selected two-point weak limit
  (`weakLimitValue_mul_eq_mul_of_truncated_tendsto_zero`).
- Under reachability and a shortest-walk no-wrap margin, coordinate
  separation gives a lower bound on `touchGraph.dist`; this reuses the
  repository's proved walk-coordinate estimate rather than postulating a
  continuum metric.
- The canonical axis-pair family fully consumes the repository's
  infinite-volume correlation theorem.  At fixed scale `k`, the
  thermodynamic-volume limit is taken first; the canonical plaquettes then
  have exact touch distance `2k`, and the connected two-point function tends
  to zero as `k → ∞`.
- Uniformly over every coupling schedule `β : ℕ → ℝ` inside the proved
  `d=4` KP window, the actual state at index `k` is constructed at coupling
  `β k`, the second plaquette is at offset `2k`, and the connected
  correlation tends to zero
  (`tendsto_d4ScaleIndexedTruncatedCorrelation_zero`).  Pairing this with
  `aₖ = 1/(k+1)` gives the paired bookkeeping endpoint
  `(physical separation, connected correlation) → (2, 0)`
  (`tendsto_d4ScaleIndexedTwoPointData`).
  The decay rate is fixed in lattice units, so its physical correlation
  length shrinks to zero.  Thus `(2, 0)` is an ultralocal/trivial two-point
  outcome in this strong-coupling lane, not construction of a continuum
  field law.  The uniform limit also carries no information that
  distinguishes one allowed schedule `β k` from another.
- A fully discharged `d=4`, `SU(2)`, `β=10⁻⁶` example uses normalized
  `Re tr U`, an origin plaquette, and a second plaquette at the genuinely
  varying offset `2k`.  Its actual constructed infinite-volume Gibbs
  connected correlation tends to zero
  (`exampleD4_twoPoint_connected_tendsto_zero`).
- A compiled example uses the real `d=4`, `SU(2)` thermodynamic Gibbs
  constructor at positive coupling `10⁻⁶`, normalized Haar measure,
  nonconstant energy `Re tr U`, and a four-edge plaquette test.  A second
  compiled path embeds that plaquette at the canonical integer anchor
  `⌊x/aₙ⌋` for a nonzero physical point, and proves convergence directly
  from integer-translation invariance.

The positive-coupling example uses identity and point-cylinder observable
embeddings.  It verifies the transport mechanics on a nonempty, non-free
discrete model.  The fixed-coupling two-point specialization varies the
separation only; the new uniform theorem also permits the constructed Gibbs
state to vary with `β k`.  Neither result supplies a physical law relating
`β k` to `aₖ`, and neither is claimed to satisfy
`GeometricScalingCompatibility` or to be a physical continuum limit.

## Open obligations, with exact types

1. **Physical scale--state coupling law**: the scale-indexed theorem accepts
   the concrete schedule `GibbsStateSequence.coupling : ℕ → ℝ` and constructs
   the state at its value `β k`, but C0 does not derive a physical relation
   between `β k` and `scale.spacing k`.  In the asymptotically-free
   convention the precise requested condition is
   `Tendsto β atTop atTop`; together with the existing KP witnesses it is
   ruled out by
   `no_asymptotically_free_scaling_in_KP_regime`.  A producer outside this
   window, with an explicit spacing convention, remains open.
   Moreover, the generic state sequence and point-cylinder constructor each
   accept a scale separately; their use together must explicitly supply
   `ScaleConventionCompatible S.scale embeddingScale.spacing` to exclude a
   silent mismatch.
2. **Geometric observable compatibility**
   (`GeometricScalingCompatibility` plus a producer-specific support
   theorem): the supplied `latticeRadius` must be derived from
   `(E.atScale n F).coord`, not chosen independently, and must grow at the
   correct rate as `aₙ → 0`.  The current compatibility record alone permits
   zero radii and is not an anti-vacuity certificate.
3. **Eventual anchor separation** (`EventuallySeparatesAnchors`): distinct
   physical points must have distinct floor anchors at all sufficiently fine
   scales.  The canonical point-cylinder map is constructed here, but this
   multi-point floor estimate remains a named obligation.
4. **Scale-convention compatibility** (`ScaleConventionCompatible`): a
   producer must relate the continuum-facing spacings to the repository's RG
   or another explicit discrete-spacing convention.
5. **Full-sequence convergence** (`HasWeakLimit`): beyond the mechanics
   example, convergence of every actual embedded expectation is an open
   obligation; no arbitrary comparison functional can discharge it.
6. **Candidate laws** (`CandidateLawRealization`): one fixed topological
   measurable configuration/distribution space, probability laws on it, test
   functions, integrability, and equality with the lattice expectations.
   For the constant-in-`n` mechanics witness, a one-point law can discharge
   this type; it becomes substantive only for a genuinely varying family.
7. **Tightness** (`UniformlyTight`): for every nonzero
   `ε : ℝ≥0∞`, one compact set captures all the candidate laws up to `ε`.
   Convergence of first expectations is not called tightness.
8. **Nontriviality** (`HasFluctuatingLimit`): some declared genuine test has
   strictly positive limiting variance.  Constants cannot discharge this
   proposition.  The predicate `isGenuineTest` is producer-supplied; the
   strict variance inequality is the actual formal gate.
9. **Reflection adapter** (`DiscreteReflectionPositive` plus
   `ReflectionCompatibility`): the current complex finite `Z₂` half-chain RP
   theorems and the real infinite-volume `SU(2)` state do not share an
   observable/state interface.  The C0 adapter explicitly requires an
   involution, a nonempty positive-half test family, and a discrete
   involution.  CONTINUUM-C0 transports RP but does not invent the missing
   producer.  These structural fields do not exclude identity reflection
   with all tests in the positive half; therefore they are not advertised as
   a physical-reflection certificate.  A future producer must additionally
   prove coordinate reversal and half-space support.
10. **Regime extension**: the proved `1/8450` wall shows that the current KP
   constructor cannot supply a schedule with `βₙ → +∞`; a different
   thermodynamic state producer is required for that lane.
11. **General separated-point correlation geometry**: C0 fully discharges
    the canonical axis-pair family using the repository's exact semitorus
    distance theorem.  Arbitrary floor-embedded multipoint tests still need
    concrete realization and no-wrap certificates at each fixed scale.
    The completed canonical theorem does not supply that general producer.
12. **Finite-separation nonvanishing**: no theorem proves a lower bound or
    even
    `∃ k, d4ScaleIndexedTruncatedCorrelation β hβ k ≠ 0`.
    This is distinct from the upper-bound endpoint and complements
    `HasFluctuatingLimit`.
13. **Reconstruction**: no measure-limit uniqueness theorem,
   OS reconstruction, Wightman theory, or continuum mass gap is supplied.

## Anti-claims

- No continuum Yang--Mills measure or field.
- No Osterwalder--Schrader/Wightman reconstruction.
- No continuum mass gap and no Clay progress.
- No inference that a constant-coupling identity-embedding example has the
  correct physical scaling.
- No inference that the uniform `(2, 0)` endpoint identifies a nontrivial
  continuum two-point function or determines the running-coupling schedule.
- No use of an assumption equivalent to the existence of the desired
  continuum theory.

The distance to the Clay problem remains ~0% (<0.1%).
