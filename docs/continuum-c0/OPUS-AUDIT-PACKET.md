# CONTINUUM-C0 compact final audit packet

Return `PASS` or `FAIL` for the bounded C0 contract below. Treat every code
signature and build result in this packet as the exact result already checked
in Lean. Identify any logical circularity or vacuity that still makes the
bounded endpoint false. Do not request tools or additional files.

## Explicit non-claims

There is no continuum Yang--Mills existence claim, continuum measure, OS
reconstruction, continuum mass gap, Clay claim, `ContinuumState`, or
`ContinuumExists`. The canonical separated two-point family is complete;
the arbitrary floor-embedded multipoint family is not. No paper is produced.

## Scale and maps

```lean
structure ScaleSequence where
  spacing : ℕ → ℝ
  spacing_pos : ∀ n, 0 < spacing n
  tendsToZero : Tendsto spacing atTop (𝓝 0)

noncomputable def reciprocalScale : ScaleSequence where
  spacing := fun n => 1 / ((n : ℝ) + 1)
  spacing_pos := by intro n; positivity
  tendsToZero := tendsto_one_div_add_atTop_nhds_zero_nat

structure ObservableEmbedding (A) (d) (G) where
  atScale : ℕ → A → IntegerLocalObservable d G

noncomputable def latticeAnchor
    (scale) (n) (x : Fin d → ℝ) : Fin d → ℤ :=
  fun j => ⌊x j / scale.spacing n⌋

noncomputable def pointCylinderEmbedding (scale) where
  atScale n F := latticeAnchor scale n F.point +ᵥ F.observable
```

The generic map is governed by exact `AlgebraCompatibility` fields
`map_one`, `map_add`, `map_smul`, `map_mul`, `map_translate`.
`map_one` requires the embedded unit to equal discrete `const 1`, so
`embed := const 0` cannot instantiate normalization transport.
`GeometricScalingCompatibility`, `ScaleConventionCompatible`, and
`EventuallySeparatesAnchors` are explicit unproved obligations.

## Actual state producer

```lean
structure GibbsStateSequence where
  scale : ScaleSequence
  measure : Measure G
  measure_probability : IsProbabilityMeasure measure
  plaquetteEnergy : G → ℝ
  plaquetteEnergy_measurable : Measurable plaquetteEnergy
  energyBound : ℝ
  plaquetteEnergy_bounded : ∀ g, |plaquetteEnergy g| ≤ energyBound
  coupling : ℕ → ℝ
  regime : ∀ n, UniformLocalKPRegime d energyBound (coupling n)

noncomputable def GibbsStateSequence.state (S) (n) :
    TranslationInvariantLocalState d G := by
  letI := S.measure_probability
  exact integerInfiniteLocalGibbsState
    S.measure S.plaquetteEnergy_measurable
    S.plaquetteEnergy_bounded (S.regime n)
```

There is no state field. `integerInfiniteLocalGibbsState` is the repository's
constructed full-sequence thermodynamic limit of finite Gibbs expectations.

## Non-circular topology

```lean
def HasWeakLimit (S) (E) : Prop :=
  ∀ F, ∃ x : ℝ,
    Tendsto (fun n => S.expectation E n F) atTop (𝓝 x)

def WeakConvergesTo (S) (E) (ψ : A → ℝ) : Prop :=
  ∀ F, Tendsto (fun n => S.expectation E n F) atTop (𝓝 (ψ F))

theorem weakLimit_unique
    (h₁ : WeakConvergesTo S E ψ₁)
    (h₂ : WeakConvergesTo S E ψ₂) :
    ∀ F, ψ₁ F = ψ₂ F :=
  fun F => tendsto_nhds_unique (h₁ F) (h₂ F)

noncomputable def weakLimitValue (h : HasWeakLimit S E) (F) :=
  Classical.choose (h F)
```

No comparison functional is stored in the sequence or accepted by
`HasWeakLimit`.

## Proved transport

Lean proves, from actual state evaluations and explicit compatibility:

- `weakLimitValue_one = 1`;
- additivity and real scalar homogeneity;
- positivity for a cone mapping to pointwise nonnegative kernels;
- every integer translation is invariant;
- conditional reflection positivity is limit-closed; and
- if the actual discrete truncated correlations tend to zero, the two-point
  weak limit factorizes.

The reflection interface requires involutions and a nonempty positive-half
family but still admits identity reflection. This is explicitly disclosed:
the theorem is only conditional transport, not a physical RP producer.

## Quantitative regime obstruction

From `κ.radius_tilt`:

```lean
theorem UniformLocalKPRegime.abs_beta_lt
    (hB : 0 < B) (κ : UniformLocalKPRegime d B β) :
    |β| < 1 / ((((16*d+1 : ℕ) : ℝ)^2) * B)
```

The proof uses `|β|B ≤ exp(|β|B)-1`,
`1 ≤ exp(κ.t+κ.ε)`, positivity of the prefactor, and
`lt_div_iff₀`. For `d=4`, `B=2`, the denominator is
`(16*4+1)^2*2 = 65^2*2 = 8450`.

Lean also proves:

```lean
Tendsto β atTop atTop →
  ¬ ∀ n, Nonempty (UniformLocalKPRegime 4 2 (β n))
```

Thus the current producer cannot follow `βₙ → +∞`; this is not generalized
to other producers.

## Compiled actual example

The example uses `d=4`, `SU(2)`, Haar probability,
`su2FundamentalPlaquetteEnergy = Re tr U`, bound `B=2`,
positive coupling `explicitStrongCouplingRadiusD4 = 10⁻⁶`, and
`su2D4UniformLocalKPRegimeOfBound`.

`exampleD4PlaquetteTest` is the actual plaquette-holonomy observable and Lean
proves its support has cardinality four. A cylinder at physical point
`x_j = j+1` is embedded by `⌊x/aₙ⌋`; its evaluations converge because the
constructed state is fully integer-translation invariant. The coupling is
constant, so this is explicitly called a transport-mechanics witness, not a
physical scaling limit.

## Compiled scale-varying two-point theorem

`axisPlaquetteObservable τ` is a compatible local observable reading the
canonical plaquette at lattice site `τe₀`. Lean proves its finite-volume
realization literally equals the corresponding canonical plaquette
holonomy. For each fixed scale index `k`, the thermodynamic volume is then
sent to infinity. Eventually the torus is large enough that the pair at
offsets `0` and `2k` is distinct and has exact touch-graph distance `2k`.
The repository's infinite-volume exponential two-plaquette theorem therefore
gives a bound proportional to `exp(-εk)`, and Lean proves:

```lean
theorem tendsto_infiniteTruncatedCorrelation_axisPair_zero :
  Tendsto (fun k => infiniteLocalGibbsTruncatedCorrelation
    μ ... (axisPlaquetteObservable 0) (axisPlaquetteObservable (2*k)))
    atTop (𝓝 0)
```

A fully discharged specialization uses `d=4`, `SU(2)`, normalized
`Re tr U`, Haar probability, and the actual `β=10⁻⁶` constructed Gibbs state:
`exampleD4_twoPoint_connected_tendsto_zero`. Its observable sequence varies
with `k`; it is not the earlier translation-invariant one-point constant
sequence. This proves factorization in the accessible canonical
positive-coupling sector, not a continuum field law.

## Precise open obligations

`CandidateLawRealization` requires laws on one fixed topological measurable
space, probability, test functions, integrability, and equality with actual
lattice expectations.

```lean
def UniformlyTight (L) : Prop :=
  ∀ ε : ENNReal, ε ≠ 0 →
    ∃ K, IsCompact K ∧ ∀ n, L.law n Kᶜ ≤ ε

def HasFluctuatingLimit (T) (h) (isGenuineTest) : Prop :=
  ∃ F, isGenuineTest F ∧
    0 < weakLimitValue h (T.mul F F) - (weakLimitValue h F)^2
```

For arbitrary floor-embedded multipoint tests, the nested separated-point
obligation remains explicit. The canonical axis family discharges the
repository correlation theorem's inner volume geometry using exact semitorus
distance; it is not an instance of the generic `WeakLimit` embedding theorem
and does not silently generalize to arbitrary floor embeddings.

## Build/oracle evidence

Every new module elaborated successfully with Lean 4.29.0-rc6. The local
oracle command

```text
lake env lean YangMills/Continuum/Oracle.lean
```

exited `0`. All 26 printed headlines depend only on
`[propext, Classical.choice, Quot.sound]`; no project axiom occurs. Static
search found no code `sorry`, declaration `axiom`, `ContinuumState`, or
`ContinuumExists`.

## Required verdict

Does this packet satisfy the bounded C0 contract: honest language and proved
transport for formulating `a→0`, an actual nonempty discrete example, and
precisely exposed missing compatibility/tightness/nontriviality/regime/
separated-correlation producers, without asserting continuum existence?
