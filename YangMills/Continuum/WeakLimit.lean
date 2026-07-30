/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.Continuum.GibbsSequence

/-!
# Pointwise weak limits of genuine scale-indexed Gibbs evaluations

The topology is explicit and non-circular: for every test `F`, the real
numbers obtained by applying the constructed state at scale `n` to the
embedded test must converge in the ordinary topology of `ℝ`.

`weakLimitValue` is selected only after that proposition is supplied.  There
is deliberately no `ContinuumState` structure and no arbitrary limit
functional among the input data.
-/

namespace YangMills.Continuum

open Filter MeasureTheory Topology
open YangMills

variable {A : Type*}
variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable [MeasurableMul₂ G] [MeasurableInv G]

/-- Pointwise weak convergence on the declared test family. -/
def HasWeakLimit
    (S : GibbsStateSequence d G)
    (E : ObservableEmbedding A d G) : Prop :=
  ∀ F : A, ∃ x : ℝ,
    Tendsto (fun n => S.expectation E n F) atTop (𝓝 x)

/-- Convergence to a specified comparison functional.  This relation is used
only to state uniqueness; the functional is never a field of the sequence. -/
def WeakConvergesTo
    (S : GibbsStateSequence d G)
    (E : ObservableEmbedding A d G)
    (ψ : A → ℝ) : Prop :=
  ∀ F : A,
    Tendsto (fun n => S.expectation E n F) atTop (𝓝 (ψ F))

/-- A specified weak limit is pointwise unique.  Thus the value selected from
`HasWeakLimit` cannot depend on a hidden choice of continuum functional. -/
theorem weakLimit_unique
    {S : GibbsStateSequence d G}
    {E : ObservableEmbedding A d G}
    {ψ₁ ψ₂ : A → ℝ}
    (h₁ : WeakConvergesTo S E ψ₁)
    (h₂ : WeakConvergesTo S E ψ₂) :
    ∀ F, ψ₁ F = ψ₂ F :=
  fun F => tendsto_nhds_unique (h₁ F) (h₂ F)

/-- The value forced by convergence of the genuine discrete evaluations. -/
noncomputable def weakLimitValue
    {S : GibbsStateSequence d G}
    {E : ObservableEmbedding A d G}
    (h : HasWeakLimit S E) (F : A) : ℝ :=
  Classical.choose (h F)

/-- The actual discrete evaluations converge to the selected value. -/
theorem tendsto_weakLimitValue
    {S : GibbsStateSequence d G}
    {E : ObservableEmbedding A d G}
    (h : HasWeakLimit S E) (F : A) :
    Tendsto (fun n => S.expectation E n F)
      atTop (𝓝 (weakLimitValue h F)) :=
  Classical.choose_spec (h F)

/-- A weak limit on a constant-coupling family with identity embeddings.
This is a mechanics witness, not a physical continuum scaling theorem. -/
theorem hasWeakLimit_constantCoupling_identity
    (scale : ScaleSequence)
    (μ : Measure G) (hμ : IsProbabilityMeasure μ)
    (pe : G → ℝ) (hpe_meas : Measurable pe)
    (B β : ℝ) (hpe : ∀ g, |pe g| ≤ B)
    (κ : WindowPolymer.UniformLocalKPRegime d B β) :
    HasWeakLimit
      (GibbsStateSequence.constantCoupling
        scale μ hμ pe hpe_meas B β hpe κ)
      (identityObservableEmbedding (d := d) (G := G)) := by
  intro F
  letI : IsProbabilityMeasure μ := hμ
  refine ⟨integerInfiniteLocalGibbsState μ hpe_meas hpe κ F, ?_⟩
  have hconst :
      Tendsto
        (fun _ : ℕ =>
          integerInfiniteLocalGibbsState μ hpe_meas hpe κ F)
        atTop
        (𝓝 (integerInfiniteLocalGibbsState μ hpe_meas hpe κ F)) :=
    tendsto_const_nhds
  apply hconst.congr'
  exact Filter.Eventually.of_forall fun _ => rfl

/-- Constant coupling also converges on the canonical moving one-point
cylinders.  The floor anchor disappears by the constructed state's full
integer-translation invariance, so this is not an assumption of convergence. -/
theorem hasWeakLimit_constantCoupling_pointCylinder
    (scale : ScaleSequence)
    (μ : Measure G) (hμ : IsProbabilityMeasure μ)
    (pe : G → ℝ) (hpe_meas : Measurable pe)
    (B β : ℝ) (hpe : ∀ g, |pe g| ≤ B)
    (κ : WindowPolymer.UniformLocalKPRegime d B β) :
    HasWeakLimit
      (GibbsStateSequence.constantCoupling
        scale μ hμ pe hpe_meas B β hpe κ)
      (pointCylinderEmbedding (d := d) (G := G) scale) := by
  intro F
  letI : IsProbabilityMeasure μ := hμ
  refine
    ⟨integerInfiniteLocalGibbsState μ hpe_meas hpe κ F.observable, ?_⟩
  have hconst :
      Tendsto
        (fun _ : ℕ =>
          integerInfiniteLocalGibbsState μ hpe_meas hpe κ F.observable)
        atTop
        (𝓝
          (integerInfiniteLocalGibbsState μ hpe_meas hpe κ F.observable)) :=
    tendsto_const_nhds
  apply hconst.congr'
  exact Filter.Eventually.of_forall fun n => by
    simpa [GibbsStateSequence.expectation,
      GibbsStateSequence.constantCoupling, GibbsStateSequence.state,
      pointCylinderEmbedding] using
      ((integerInfiniteLocalGibbsState μ hpe_meas hpe κ).vadd_invariant
        (latticeAnchor scale n F.point) F.observable).symm

section Transport

variable (T : MinimalTestAlgebra A d)
variable (S : GibbsStateSequence d G)
variable (E : ObservableEmbedding A d G)
variable (h : HasWeakLimit S E)

/-- Normalization is closed under the pointwise weak limit. -/
theorem weakLimitValue_one (C : AlgebraCompatibility T E) :
    weakLimitValue h T.one = 1 := by
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have heq :
      ∀ᶠ n in atTop, (1 : ℝ) = S.expectation E n T.one := by
    exact Filter.Eventually.of_forall fun n => by
      rw [GibbsStateSequence.expectation,
        AlgebraCompatibility.map_one C]
      exact (S.state n).map_one.symm
  exact tendsto_nhds_unique
    (tendsto_weakLimitValue h T.one)
    (hone.congr' heq)

/-- Additivity is closed under the pointwise weak limit. -/
theorem weakLimitValue_add
    (C : AlgebraCompatibility T E) (F H : A) :
    weakLimitValue h (T.add F H) =
      weakLimitValue h F + weakLimitValue h H := by
  have hadd :=
    (tendsto_weakLimitValue h F).add
      (tendsto_weakLimitValue h H)
  have heq : ∀ᶠ n in atTop,
      S.expectation E n F + S.expectation E n H =
        S.expectation E n (T.add F H) := by
    exact Filter.Eventually.of_forall fun n => by
      simp only [GibbsStateSequence.expectation]
      rw [AlgebraCompatibility.map_add C]
      exact (S.state n).map_add _ _ |>.symm
  exact tendsto_nhds_unique
    (tendsto_weakLimitValue h (T.add F H))
    (hadd.congr' heq)

/-- Real scalar linearity is closed under the pointwise weak limit. -/
theorem weakLimitValue_smul
    (C : AlgebraCompatibility T E) (c : ℝ) (F : A) :
    weakLimitValue h (T.smul c F) =
      c * weakLimitValue h F := by
  have hmul :
      Tendsto (fun n => c * S.expectation E n F)
        atTop (𝓝 (c * weakLimitValue h F)) :=
    tendsto_const_nhds.mul (tendsto_weakLimitValue h F)
  have heq : ∀ᶠ n in atTop,
      c * S.expectation E n F =
        S.expectation E n (T.smul c F) := by
    exact Filter.Eventually.of_forall fun n => by
      simp only [GibbsStateSequence.expectation]
      rw [AlgebraCompatibility.map_smul C]
      exact (S.state n).map_smul _ _ |>.symm
  exact tendsto_nhds_unique
    (tendsto_weakLimitValue h (T.smul c F))
    (hmul.congr' heq)

/-- Positivity is closed under the pointwise weak limit whenever the chosen
test positive cone maps to pointwise nonnegative discrete kernels. -/
theorem weakLimitValue_nonneg
    (nonnegative : A → Prop)
    (O : OrderCompatibility nonnegative E)
    (F : A) (hF : nonnegative F) :
    0 ≤ weakLimitValue h F := by
  apply ge_of_tendsto' (tendsto_weakLimitValue h F)
  intro n
  unfold GibbsStateSequence.expectation
  exact (S.state n).nonneg _ (O.map_nonnegative n F hF)

/-- Full integer-translation invariance is closed under the pointwise weak
limit. -/
theorem weakLimitValue_translate
    (C : AlgebraCompatibility T E) (z : Fin d → ℤ) (F : A) :
    weakLimitValue h (T.translate z F) = weakLimitValue h F := by
  have heq : ∀ᶠ n in atTop,
      S.expectation E n F =
        S.expectation E n (T.translate z F) := by
    exact Filter.Eventually.of_forall fun n => by
      simp only [GibbsStateSequence.expectation]
      rw [AlgebraCompatibility.map_translate C]
      exact (S.state n).vadd_invariant z (E.atScale n F) |>.symm
  exact tendsto_nhds_unique
    (tendsto_weakLimitValue h (T.translate z F))
    ((tendsto_weakLimitValue h F).congr' heq)

/-- The genuine discrete truncated correlation of two embedded tests at one
scale. -/
noncomputable def discreteTruncatedCorrelation (F H : A) (n : ℕ) : ℝ :=
  S.state n
      (IntegerLocalObservable.mul
        (E.atScale n F) (E.atScale n H)) -
    S.expectation E n F * S.expectation E n H

/-- If a separately proved geometric/clustering argument makes the actual
scale-indexed truncated correlations tend to zero, the selected two-point
weak limit factorizes.  The premise is deliberately scalar and downstream of
the constructed discrete states; it is not hidden inside a continuum law. -/
theorem weakLimitValue_mul_eq_mul_of_truncated_tendsto_zero
    (C : AlgebraCompatibility T E) (F H : A)
    (htrunc :
      Tendsto
        (discreteTruncatedCorrelation S E F H)
        atTop (𝓝 0)) :
    weakLimitValue h (T.mul F H) =
      weakLimitValue h F * weakLimitValue h H := by
  have hprod :=
    (tendsto_weakLimitValue h F).mul
      (tendsto_weakLimitValue h H)
  have hsum := htrunc.add hprod
  have heq : ∀ᶠ n in atTop,
      discreteTruncatedCorrelation S E F H n +
          S.expectation E n F * S.expectation E n H =
        S.expectation E n (T.mul F H) := by
    exact Filter.Eventually.of_forall fun n => by
      simp only [discreteTruncatedCorrelation,
        GibbsStateSequence.expectation]
      rw [AlgebraCompatibility.map_mul C]
      ring
  exact tendsto_nhds_unique
    (tendsto_weakLimitValue h (T.mul F H))
    (by simpa using hsum.congr' heq)

end Transport

/-! ## Conditional reflection-positivity transport -/

/-- The exact finite-scale RP producer required by the real test interface.
The current complex `Z₂` half-chain theorems do not yet instantiate this
predicate for the thermodynamic SU(2) state. -/
def DiscreteReflectionPositive
    (S : GibbsStateSequence d G)
    (E : ObservableEmbedding A d G)
    (R : ReflectionCompatibility E) : Prop :=
  ∀ n F, R.positiveHalf F → 0 ≤
    S.state n
      (IntegerLocalObservable.mul
        (R.discreteReflect n (E.atScale n F))
        (E.atScale n F))

/-- Reflection positivity on the selected real weak-limit functional. -/
def WeakLimitReflectionPositive
    (T : MinimalTestAlgebra A d)
    {S : GibbsStateSequence d G}
    {E : ObservableEmbedding A d G}
    (R : ReflectionCompatibility E)
    (h : HasWeakLimit S E) : Prop :=
  ∀ F, R.positiveHalf F →
    0 ≤ weakLimitValue h (T.mul (R.reflect F) F)

/-- Finite-scale real reflection positivity passes to the pointwise weak
limit, provided multiplication and reflection commute with the embeddings. -/
theorem weakLimit_reflectionPositive
    (T : MinimalTestAlgebra A d)
    (S : GibbsStateSequence d G)
    (E : ObservableEmbedding A d G)
    (C : AlgebraCompatibility T E)
    (R : ReflectionCompatibility E)
    (h : HasWeakLimit S E)
    (hRP : DiscreteReflectionPositive S E R) :
    WeakLimitReflectionPositive T R h := by
  intro F hF
  apply ge_of_tendsto'
    (tendsto_weakLimitValue h (T.mul (R.reflect F) F))
  intro n
  unfold GibbsStateSequence.expectation
  rw [AlgebraCompatibility.map_mul C, R.map_reflect]
  exact hRP n F hF

/-! ## Explicit open measure-level obligations -/

/-- A candidate realization of the discrete cylinder expectations as laws on
one fixed topological measurable space.  This is data still absent for
four-dimensional continuum Yang--Mills; merely having scalar weak limits does
not construct it. -/
structure CandidateLawRealization
    (S : GibbsStateSequence d G)
    (E : ObservableEmbedding A d G)
    (X : Type*) [TopologicalSpace X] [MeasurableSpace X] where
  law : ℕ → Measure X
  law_probability : ∀ n, IsProbabilityMeasure (law n)
  testFunction : A → X → ℝ
  test_integrable : ∀ n F, Integrable (testFunction F) (law n)
  expectation_matches : ∀ n F,
    ∫ x, testFunction F x ∂(law n) = S.expectation E n F

/-- Uniform tightness of the candidate laws.  This is a real measure-level
condition, not a synonym for convergence of first expectations. -/
def UniformlyTight
    {S : GibbsStateSequence d G}
    {E : ObservableEmbedding A d G}
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (L : CandidateLawRealization S E X) : Prop :=
  ∀ ε : ENNReal, ε ≠ 0 →
    ∃ K : Set X, IsCompact K ∧
      ∀ n, L.law n Kᶜ ≤ ε

/-- A precise nontriviality obligation excluding a deterministic/constant
limit: some declared genuine test must have strictly positive limiting
variance.  CONTINUUM-C0 names this proposition but does not prove it. -/
def HasFluctuatingLimit
    (T : MinimalTestAlgebra A d)
    {S : GibbsStateSequence d G}
    {E : ObservableEmbedding A d G}
    (h : HasWeakLimit S E)
    (isGenuineTest : A → Prop) : Prop :=
  ∃ F, isGenuineTest F ∧
    0 <
      weakLimitValue h (T.mul F F) -
        (weakLimitValue h F) ^ 2

end YangMills.Continuum
