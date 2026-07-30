# CONTINUUM-C0 charter

Branch base: `81721890ad3e111d73cbe45074d42ec698ce07b2`
(the fetched `origin/main` tip when the isolated branch was created).

Current `origin/main` after the later audit fetch:
`7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`.  The branch base is one commit
behind; the complete delta is confined to
`papers/spatial-os/spatial_os.{tex,pdf}`, the explicitly excluded Paper 13
lane.  This branch is intentionally not rebased across that active lane.

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
observable-map obligations explicit.  In particular, merely attaching the
number `aₙ` to a fixed observable is not geometric scaling:
`GeometricScalingCompatibility` separately requires the scaled discrete
support radius to converge to its declared physical radius.

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
- A compiled example uses the real `d=4`, `SU(2)` thermodynamic Gibbs
  constructor at positive coupling `10⁻⁶`, normalized Haar measure,
  nonconstant energy `Re tr U`, and a four-edge plaquette test.  A second
  compiled path embeds that plaquette at the canonical integer anchor
  `⌊x/aₙ⌋` for a nonzero physical point, and proves convergence directly
  from integer-translation invariance.

The example uses identity observable embeddings.  It verifies the transport
mechanics on a nonempty, non-free discrete model.  It is not claimed to
satisfy `GeometricScalingCompatibility`, and it is not a physical continuum
limit.

## Open obligations, with exact types

1. **Geometric observable compatibility**
   (`GeometricScalingCompatibility`): the number of lattice sites read by a
   fixed physical test must grow at the correct rate as `aₙ → 0`.
2. **Eventual anchor separation** (`EventuallySeparatesAnchors`): distinct
   physical points must have distinct floor anchors at all sufficiently fine
   scales.  The canonical point-cylinder map is constructed here, but this
   multi-point floor estimate remains a named obligation.
3. **Scale-convention compatibility** (`ScaleConventionCompatible`): a
   producer must relate the continuum-facing spacings to the repository's RG
   or another explicit discrete-spacing convention.
4. **Full-sequence convergence** (`HasWeakLimit`): beyond the mechanics
   example, convergence of every actual embedded expectation is an open
   obligation; no arbitrary comparison functional can discharge it.
5. **Candidate laws** (`CandidateLawRealization`): one fixed topological
   measurable configuration/distribution space, probability laws on it, test
   functions, integrability, and equality with the lattice expectations.
6. **Tightness** (`UniformlyTight`): for every nonzero
   `ε : ℝ≥0∞`, one compact set captures all the candidate laws up to `ε`.
   Convergence of first expectations is not called tightness.
7. **Nontriviality** (`HasFluctuatingLimit`): some declared genuine test has
   strictly positive limiting variance.  Constants cannot discharge this
   proposition.
8. **Reflection adapter** (`DiscreteReflectionPositive` plus
   `ReflectionCompatibility`): the current complex finite `Z₂` half-chain RP
   theorems and the real infinite-volume `SU(2)` state do not share an
   observable/state interface.  The C0 adapter explicitly requires an
   involution, a nonempty positive-half test family, and a discrete
   involution.  CONTINUUM-C0 transports RP but does not invent the missing
   producer.  These structural fields do not exclude identity reflection
   with all tests in the positive half; therefore they are not advertised as
   a physical-reflection certificate.  A future producer must additionally
   prove coordinate reversal and half-space support.
9. **Regime extension**: the proved `1/8450` wall shows that the current KP
   constructor cannot supply a schedule with `βₙ → +∞`; a different
   thermodynamic state producer is required for that lane.
10. **Separated-point correlation geometry**: the repository has an
    infinite-volume exponential truncated-correlation bound.  C0 proves that
    a seam-avoiding shortest touching walk converts coordinate separation to
    a `touchGraph.dist` lower bound.  Fully consuming the correlation theorem
    still requires, at each fixed scale and eventually in the independent
    thermodynamic-volume index, concrete plaquettes realizing the two
    embedded tests together with reachability and shortest-walk margin.
    Only after that inner limit may the scale index tend to infinity.  C0
    does not silently assume those missing certificates or mislabel
    one-point variance as separated-point correlation.
11. **Reconstruction**: no measure-limit uniqueness theorem,
   OS reconstruction, Wightman theory, or continuum mass gap is supplied.

## Anti-claims

- No continuum Yang--Mills measure or field.
- No Osterwalder--Schrader/Wightman reconstruction.
- No continuum mass gap and no Clay progress.
- No inference that a constant-coupling identity-embedding example has the
  correct physical scaling.
- No use of an assumption equivalent to the existence of the desired
  continuum theory.

The distance to the Clay problem remains ~0% (<0.1%).
