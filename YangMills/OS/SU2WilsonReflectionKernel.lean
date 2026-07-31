/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

Finite-rank and Haar-integral substrate for the SU(2) Wilson crossing kernel.
-/

import Mathlib
import YangMills.L0_Lattice.SU2Basic
import YangMills.P8_PhysicalGap.SUN_StateConstruction
import YangMills.ClayCore.SchurPhysicalBridge

/-!
# SU(2) Wilson crossing kernels

This module is downstream of the finite `YangMills.OS.PSDKernel` idea but not
of its types.  The published OS API sums over a `Fintype` configuration space
hard-coded to `ZMod N`; SU(2) is compact and infinite.  Here the same finite
rank-one algebra is stated over an arbitrary compact space and the quadratic
form is a double Bochner integral.

The physical crossing factor uses the standard Wilson convention

`exp ((β / 2) * Re (trace (x * y⁻¹)))`.

The plus sign is part of the definition.  No continuum or reconstruction
statement is made.
-/

noncomputable section

open scoped BigOperators
open scoped Topology
open Matrix Complex MeasureTheory

namespace YangMills.OS

/-- A finite non-negative combination of rank-one complex kernels on an
arbitrary (not necessarily finite) type. -/
structure IsFiniteRankPositiveKernel {X ι : Type*} [Fintype ι]
    (c : ι → ℝ) (φ : ι → X → ℂ) (K : X → X → ℂ) : Prop where
  coeff_nonneg : ∀ i, 0 ≤ c i
  eq : ∀ x y, K x y =
    ∑ i, (c i : ℂ) * φ i x * (starRingEnd ℂ) (φ i y)

/-- Continuity data for a finite rank-one presentation. -/
structure IsContinuousFiniteRankPositiveKernel
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (c : ι → ℝ) (φ : ι → X → ℂ) (K : X → X → ℂ)
    extends IsFiniteRankPositiveKernel c φ K where
  continuous_feature : ∀ i, Continuous (φ i)

/-- The complex quadratic form of a kernel with respect to a measure. -/
noncomputable def kernelIntegralForm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : X → X → ℂ) (F : X → ℂ) : ℂ :=
  ∫ x, ∫ y, (starRingEnd ℂ) (F x) * K x y * F y ∂μ ∂μ

/-- Positive semidefiniteness tested on continuous complex observables.
Continuity is the explicit integrability gate on the compact SU(2) domain. -/
def IsHaarPSDKernel {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (K : X → X → ℂ) : Prop :=
  ∀ F : X → ℂ, Continuous F →
    ∃ r : ℝ, 0 ≤ r ∧ kernelIntegralForm μ K F = (r : ℂ)

section FiniteRankIntegral

variable {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X] [Fintype ι]
  {c : ι → ℝ} {φ : ι → X → ℂ} {K : X → X → ℂ}
  (μ : Measure X) [IsFiniteMeasure μ]

set_option maxHeartbeats 100000 in
/-- A continuous finite non-negative rank-one combination has a non-negative
complex quadratic form for every continuous observable.  The witness is the
finite sum of coefficient-weighted squared feature moments. -/
theorem isHaarPSDKernel_of_continuousFiniteRank
    (h : IsContinuousFiniteRankPositiveKernel c φ K) :
    IsHaarPSDKernel μ K := by
  intro F hF
  let A : ι → ℂ :=
    fun i => ∫ x, (starRingEnd ℂ) (φ i x) * F x ∂μ
  refine ⟨∑ i : ι, c i * Complex.normSq (A i), ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (h.coeff_nonneg i) (Complex.normSq_nonneg _)
  · have hfeature_integrable (i : ι) :
        Integrable (fun x => (starRingEnd ℂ) (φ i x) * F x) μ := by
      have hc : Continuous (fun x =>
          (starRingEnd ℂ) (φ i x) * F x) :=
        (h.continuous_feature i).star.mul hF
      exact hc.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hconjA (i : ι) :
        (∫ x, (starRingEnd ℂ) (F x) * φ i x ∂μ) =
          (starRingEnd ℂ) (A i) := by
      change
        (∫ x, star (F x) * φ i x ∂μ) =
          star (∫ x, star (φ i x) * F x ∂μ)
      calc
        (∫ x, star (F x) * φ i x ∂μ) =
            ∫ x, star (star (φ i x) * F x) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              simp [mul_comm]
        _ = star (∫ x, star (φ i x) * F x ∂μ) := integral_conj
    have hinner (x : X) :
        (∫ y, (starRingEnd ℂ) (F x) * K x y * F y ∂μ) =
          ∑ i : ι, ((c i : ℂ) * (starRingEnd ℂ) (F x) * φ i x) * A i := by
      simp_rw [h.eq, Finset.mul_sum, Finset.sum_mul]
      rw [integral_finset_sum]
      · exact Finset.sum_congr rfl fun i _ => by
          have heq :
              (fun y =>
                (starRingEnd ℂ) (F x) *
                    ((c i : ℂ) * φ i x * (starRingEnd ℂ) (φ i y)) * F y) =
                fun y =>
                  ((c i : ℂ) * (starRingEnd ℂ) (F x) * φ i x) *
                    ((starRingEnd ℂ) (φ i y) * F y) := by
            funext y
            ring
          rw [heq]
          change
            (∫ y,
              ((c i : ℂ) * star (F x) * φ i x) *
                (star (φ i y) * F y) ∂μ) =
              ((c i : ℂ) * star (F x) * φ i x) *
                (∫ y, star (φ i y) * F y ∂μ)
          exact integral_const_mul _ _
      · intro i _
        have heq :
            (fun y =>
              (starRingEnd ℂ) (F x) *
                  ((c i : ℂ) * φ i x * (starRingEnd ℂ) (φ i y)) * F y) =
              fun y =>
                ((c i : ℂ) * (starRingEnd ℂ) (F x) * φ i x) *
                  ((starRingEnd ℂ) (φ i y) * F y) := by
          funext y
          ring
        rw [heq]
        exact (hfeature_integrable i).const_mul _
    have houter_integrable (i : ι) :
        Integrable (fun x =>
          ((c i : ℂ) * (starRingEnd ℂ) (F x) * φ i x) * A i) μ := by
      have hc : Continuous (fun x =>
          ((c i : ℂ) * (starRingEnd ℂ) (F x) * φ i x) * A i) := by
        exact
          (((continuous_const.mul hF.star).mul
            (h.continuous_feature i)).mul continuous_const)
      exact hc.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    unfold kernelIntegralForm
    rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
    rw [integral_finset_sum]
    · rw [ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ofReal_mul, Complex.normSq_eq_conj_mul_self]
      calc
        (∫ x,
            ((c i : ℂ) * star (F x) * φ i x) * A i ∂μ) =
            (∫ x, (c i : ℂ) * (star (F x) * φ i x) ∂μ) * A i := by
              simpa only [mul_assoc] using
                (integral_mul_const (μ := μ) (A i)
                  (fun x => (c i : ℂ) * (star (F x) * φ i x)))
        _ = (c i : ℂ) *
            (∫ x, star (F x) * φ i x ∂μ) * A i := by
              exact congrArg (fun z : ℂ => z * A i)
                (integral_const_mul (μ := μ) (c i : ℂ)
                  (fun x => star (F x) * φ i x))
        _ = (c i : ℂ) * (star (A i) * A i) := by
              have hc :
                  (∫ x, star (F x) * φ i x ∂μ) = star (A i) :=
                hconjA i
              rw [hc]
              ring
    · intro i _
      exact houter_integrable i

end FiniteRankIntegral

/-! ## Algebra of finite positive presentations -/

set_option maxHeartbeats 20000 in
theorem continuousFiniteRank_mul
    {X ι κ : Type*} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    {c : ι → ℝ} {d : κ → ℝ} {φ : ι → X → ℂ} {ψ : κ → X → ℂ}
    {K L : X → X → ℂ}
    (hK : IsContinuousFiniteRankPositiveKernel c φ K)
    (hL : IsContinuousFiniteRankPositiveKernel d ψ L) :
    IsContinuousFiniteRankPositiveKernel
      (fun p : ι × κ => c p.1 * d p.2)
      (fun p x => φ p.1 x * ψ p.2 x)
      (fun x y => K x y * L x y) where
  coeff_nonneg := fun p =>
    mul_nonneg (hK.coeff_nonneg p.1) (hL.coeff_nonneg p.2)
  eq := by
    intro x y
    rw [hK.eq, hL.eq, Finset.sum_mul_sum]
    rw [← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    push_cast
    simp only [map_mul]
    ring
  continuous_feature := fun p =>
    (hK.continuous_feature p.1).mul (hL.continuous_feature p.2)

set_option maxHeartbeats 20000 in
theorem continuousFiniteRank_scale
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    {c : ι → ℝ} {φ : ι → X → ℂ} {K : X → X → ℂ}
    (a : ℝ) (ha : 0 ≤ a)
    (hK : IsContinuousFiniteRankPositiveKernel c φ K) :
    IsContinuousFiniteRankPositiveKernel
      (fun i => a * c i) φ (fun x y => (a : ℂ) * K x y) where
  coeff_nonneg := fun i => mul_nonneg ha (hK.coeff_nonneg i)
  eq := by
    intro x y
    rw [hK.eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  continuous_feature := hK.continuous_feature

set_option maxHeartbeats 20000 in
theorem continuousFiniteRank_add
    {X ι κ : Type*} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    {c : ι → ℝ} {d : κ → ℝ} {φ : ι → X → ℂ} {ψ : κ → X → ℂ}
    {K L : X → X → ℂ}
    (hK : IsContinuousFiniteRankPositiveKernel c φ K)
    (hL : IsContinuousFiniteRankPositiveKernel d ψ L) :
    IsContinuousFiniteRankPositiveKernel
      (Sum.elim c d) (Sum.elim φ ψ) (fun x y => K x y + L x y) where
  coeff_nonneg := by
    intro i
    cases i with
    | inl i => exact hK.coeff_nonneg i
    | inr j => exact hL.coeff_nonneg j
  eq := by
    intro x y
    rw [hK.eq, hL.eq, Fintype.sum_sum_type]
    rfl
  continuous_feature := by
    intro i
    cases i with
    | inl i => exact hK.continuous_feature i
    | inr j => exact hL.continuous_feature j

set_option maxHeartbeats 20000 in
theorem continuousFiniteRank_one {X : Type*} [TopologicalSpace X] :
    IsContinuousFiniteRankPositiveKernel
      (fun _ : Unit => (1 : ℝ)) (fun _ _ => (1 : ℂ))
      (fun _ _ : X => (1 : ℂ)) where
  coeff_nonneg := fun _ => zero_le_one
  eq := by simp
  continuous_feature := fun _ => continuous_const

/-- Existential packaging used when products and finite sums change the feature
index type. -/
def HasContinuousPositivePresentation
    {X : Type*} [TopologicalSpace X] (K : X → X → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ) (φ : ι → X → ℂ),
    IsContinuousFiniteRankPositiveKernel c φ K

theorem hasContinuousPositivePresentation_one
    {X : Type*} [TopologicalSpace X] :
    HasContinuousPositivePresentation (fun _ _ : X => (1 : ℂ)) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ _ => 1,
    continuousFiniteRank_one⟩

theorem HasContinuousPositivePresentation.mul
    {X : Type*} [TopologicalSpace X] {K L : X → X → ℂ}
    (hK : HasContinuousPositivePresentation K)
    (hL : HasContinuousPositivePresentation L) :
    HasContinuousPositivePresentation (fun x y => K x y * L x y) := by
  rcases hK with ⟨ι, hι, c, φ, hK⟩
  rcases hL with ⟨κ, hκ, d, ψ, hL⟩
  letI : Fintype ι := hι
  letI : Fintype κ := hκ
  exact ⟨ι × κ, inferInstance, fun p => c p.1 * d p.2,
    fun p x => φ p.1 x * ψ p.2 x, continuousFiniteRank_mul hK hL⟩

theorem HasContinuousPositivePresentation.add
    {X : Type*} [TopologicalSpace X] {K L : X → X → ℂ}
    (hK : HasContinuousPositivePresentation K)
    (hL : HasContinuousPositivePresentation L) :
    HasContinuousPositivePresentation (fun x y => K x y + L x y) := by
  rcases hK with ⟨ι, hι, c, φ, hK⟩
  rcases hL with ⟨κ, hκ, d, ψ, hL⟩
  letI : Fintype ι := hι
  letI : Fintype κ := hκ
  exact ⟨ι ⊕ κ, inferInstance, Sum.elim c d, Sum.elim φ ψ,
    continuousFiniteRank_add hK hL⟩

theorem HasContinuousPositivePresentation.scale
    {X : Type*} [TopologicalSpace X] {K : X → X → ℂ}
    (a : ℝ) (ha : 0 ≤ a)
    (hK : HasContinuousPositivePresentation K) :
    HasContinuousPositivePresentation (fun x y => (a : ℂ) * K x y) := by
  rcases hK with ⟨ι, hι, c, φ, hK⟩
  letI : Fintype ι := hι
  exact ⟨ι, inferInstance, fun i => a * c i, φ,
    continuousFiniteRank_scale a ha hK⟩

theorem HasContinuousPositivePresentation.pow
    {X : Type*} [TopologicalSpace X] {K : X → X → ℂ}
    (hK : HasContinuousPositivePresentation K) :
    ∀ n : ℕ, HasContinuousPositivePresentation (fun x y => K x y ^ n)
  | 0 => by simpa using
      (hasContinuousPositivePresentation_one (X := X))
  | n + 1 => by
      simpa only [pow_succ] using (hK.pow n).mul hK

theorem HasContinuousPositivePresentation.finset_sum
    {X α : Type*} [TopologicalSpace X]
    (s : Finset α) (K : α → X → X → ℂ)
    (hK : ∀ a ∈ s, HasContinuousPositivePresentation (K a)) :
    HasContinuousPositivePresentation (fun x y => ∑ a ∈ s, K a x y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (hasContinuousPositivePresentation_one (X := X)).scale 0 le_rfl
  | @insert a s ha ih =>
      have haK := hK a (Finset.mem_insert_self a s)
      have hsK := ih (fun b hb => hK b (Finset.mem_insert_of_mem hb))
      simpa [Finset.sum_insert ha] using haK.add hsK

theorem IsContinuousFiniteRankPositiveKernel.continuous_uncurry
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    {c : ι → ℝ} {φ : ι → X → ℂ} {K : X → X → ℂ}
    (h : IsContinuousFiniteRankPositiveKernel c φ K) :
    Continuous (Function.uncurry K) := by
  have hc : Continuous (fun p : X × X =>
      ∑ i : ι, (c i : ℂ) * φ i p.1 * (starRingEnd ℂ) (φ i p.2)) := by
    refine continuous_finset_sum Finset.univ (fun i _ => ?_)
    exact
      ((continuous_const.mul
        ((h.continuous_feature i).comp continuous_fst)).mul
          (continuous_star.comp
            ((h.continuous_feature i).comp continuous_snd)))
  apply hc.congr
  intro p
  exact (h.eq p.1 p.2).symm

theorem HasContinuousPositivePresentation.continuous_uncurry
    {X : Type*} [TopologicalSpace X] {K : X → X → ℂ}
    (h : HasContinuousPositivePresentation K) :
    Continuous (Function.uncurry K) := by
  rcases h with ⟨ι, hι, c, φ, h⟩
  letI : Fintype ι := hι
  exact h.continuous_uncurry

/-- For unitary matrices, the trace of `x y⁻¹` is the Hermitian dot product
of their matrix-entry vectors. -/
theorem su2_trace_mul_inv_eq_sum_entries (x y : SU2) :
    Matrix.trace (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))
      = ∑ i : Fin 2, ∑ j : Fin 2,
          (x : Matrix (Fin 2) (Fin 2) ℂ) i j *
            star ((y : Matrix (Fin 2) (Fin 2) ℂ) i j) := by
  simp only [Matrix.trace, Matrix.diag]
  change
    (∑ i : Fin 2,
      (((x : Matrix (Fin 2) (Fin 2) ℂ) *
        ((star y : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) i i))
      = ∑ i : Fin 2, ∑ j : Fin 2,
          (x : Matrix (Fin 2) (Fin 2) ℂ) i j *
            star ((y : Matrix (Fin 2) (Fin 2) ℂ) i j)
  simp only [Matrix.specialUnitaryGroup.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.mul_apply]

/-- The eight coordinate/conjugate-coordinate features which present the real
fundamental trace as a positive rank-one kernel. -/
abbrev SU2WilsonFeatureIndex := Fin 2 × Fin 2 × Fin 2

def su2WilsonFeature (p : SU2WilsonFeatureIndex) (x : SU2) : ℂ :=
  if p.2.2 = 0 then
    (x : Matrix (Fin 2) (Fin 2) ℂ) p.1 p.2.1
  else
    star ((x : Matrix (Fin 2) (Fin 2) ℂ) p.1 p.2.1)

def su2WilsonLinearCoeff (β : ℝ) (_ : SU2WilsonFeatureIndex) : ℝ :=
  β / 4

/-- The exponent of the Wilson crossing factor, regarded as a complex-valued
Hermitian kernel. -/
def su2WilsonExponentKernel (β : ℝ) (x y : SU2) : ℂ :=
  ((β / 2) *
    (Matrix.trace (((x * y⁻¹ : SU2) :
      Matrix (Fin 2) (Fin 2) ℂ))).re : ℝ)

set_option maxHeartbeats 10000 in
theorem su2WilsonFeature_sum (x y : SU2) :
    (∑ p : SU2WilsonFeatureIndex,
      su2WilsonFeature p x * star (su2WilsonFeature p y)) =
      Matrix.trace (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) +
        star (Matrix.trace
          (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))) := by
  rw [su2_trace_mul_inv_eq_sum_entries]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_two]
  simp only [su2WilsonFeature, Fin.isValue, one_ne_zero, if_false, if_true,
    star_add]
  simp_rw [StarMul.star_mul]
  simp only [star_star]
  ring

set_option maxHeartbeats 10000 in
/-- The exponent kernel is already a finite non-negative sum of rank-one
coordinate kernels.  This is the elementary Fock-space substitute for invoking
Peter--Weyl or unformalized Bessel coefficients. -/
theorem su2WilsonExponent_finiteRank (β : ℝ) (hβ : 0 ≤ β) :
    IsContinuousFiniteRankPositiveKernel
      (su2WilsonLinearCoeff β) su2WilsonFeature
      (su2WilsonExponentKernel β) := by
  refine
    { coeff_nonneg := fun _ => div_nonneg hβ (by norm_num)
      eq := ?_
      continuous_feature := ?_ }
  · intro x y
    simp only [su2WilsonExponentKernel, su2WilsonLinearCoeff]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    have hs :
        (∑ p : SU2WilsonFeatureIndex,
          su2WilsonFeature p x *
            (starRingEnd ℂ) (su2WilsonFeature p y)) =
          Matrix.trace
              (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) +
            (starRingEnd ℂ)
              (Matrix.trace
                (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))) :=
      su2WilsonFeature_sum x y
    rw [hs]
    push_cast
    rw [Complex.re_eq_add_conj]
    ring
  · intro p
    by_cases hp : p.2.2 = 0
    · unfold su2WilsonFeature
      simp only [hp, if_true]
      exact (continuous_apply p.2.1).comp
        ((continuous_apply p.1).comp continuous_subtype_val)
    · unfold su2WilsonFeature
      simp only [hp]
      exact continuous_star.comp
        ((continuous_apply p.2.1).comp
          ((continuous_apply p.1).comp continuous_subtype_val))

/-- The non-negative Taylor/Fock coefficient. -/
def su2WilsonTaylorCoeff (n : ℕ) : ℝ :=
  ((n.factorial : ℝ)⁻¹)

theorem su2WilsonTaylorCoeff_nonneg (n : ℕ) :
    0 ≤ su2WilsonTaylorCoeff n := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- The first `N` terms of the Taylor expansion of the exact Wilson crossing
factor. -/
def su2WilsonTaylorKernel (β : ℝ) (N : ℕ) (x y : SU2) : ℂ :=
  ∑ n ∈ Finset.range N,
    (su2WilsonTaylorCoeff n : ℂ) * su2WilsonExponentKernel β x y ^ n

/-- Every Taylor truncation has an explicit finite positive presentation. -/
theorem su2WilsonTaylor_hasContinuousPositivePresentation
    (β : ℝ) (hβ : 0 ≤ β) (N : ℕ) :
    HasContinuousPositivePresentation (su2WilsonTaylorKernel β N) := by
  have hbase :
      HasContinuousPositivePresentation (su2WilsonExponentKernel β) :=
    ⟨SU2WilsonFeatureIndex, inferInstance, su2WilsonLinearCoeff β,
      su2WilsonFeature, su2WilsonExponent_finiteRank β hβ⟩
  unfold su2WilsonTaylorKernel
  apply HasContinuousPositivePresentation.finset_sum
  intro n hn
  exact (hbase.pow n).scale (su2WilsonTaylorCoeff n)
    (su2WilsonTaylorCoeff_nonneg n)

/-- Gate (3) for every certified Fock truncation: its complex Haar quadratic
form is exactly a non-negative real number. -/
theorem su2WilsonTaylor_isHaarPSDKernel
    (β : ℝ) (hβ : 0 ≤ β) (N : ℕ) :
    IsHaarPSDKernel (sunHaarProb 2) (su2WilsonTaylorKernel β N) := by
  rcases su2WilsonTaylor_hasContinuousPositivePresentation β hβ N with
    ⟨ι, hι, c, φ, h⟩
  letI : Fintype ι := hι
  exact isHaarPSDKernel_of_continuousFiniteRank (sunHaarProb 2) h

/-- The exact single-plaquette SU(2) Wilson crossing factor. -/
noncomputable def su2WilsonCrossingKernel (β : ℝ) (x y : SU2) : ℂ :=
  Real.exp ((β / 2) *
    (Matrix.trace (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))).re)

/-- Pointwise convergence of the certified Fock truncations to the exact
Wilson factor.  Uniform convergence on the compact SU(2) domain is the
remaining analytic step needed to pass the Haar quadratic inequality to this
limit. -/
theorem su2WilsonTaylor_hasSum (β : ℝ) (x y : SU2) :
    HasSum
      (fun n : ℕ => (su2WilsonTaylorCoeff n : ℂ) *
        su2WilsonExponentKernel β x y ^ n)
      (su2WilsonCrossingKernel β x y) := by
  let z : ℂ := su2WilsonExponentKernel β x y
  have hsum :
      HasSum (fun n : ℕ => (su2WilsonTaylorCoeff n : ℂ) * z ^ n)
        (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    convert NormedSpace.expSeries_div_hasSum_exp z using 1
    funext n
    simp [su2WilsonTaylorCoeff, div_eq_mul_inv, mul_comm]
  simpa [z, su2WilsonExponentKernel, su2WilsonCrossingKernel,
    Complex.ofReal_exp] using hsum

/-- Pointwise convergence of the certified Fock truncations to the exact
Wilson factor. -/
theorem su2WilsonTaylor_tendsto (β : ℝ) (x y : SU2) :
    Filter.Tendsto (fun N => su2WilsonTaylorKernel β N x y) Filter.atTop
      (𝓝 (su2WilsonCrossingKernel β x y)) := by
  simpa [su2WilsonTaylorKernel] using
    (su2WilsonTaylor_hasSum β x y).tendsto_sum_nat

set_option maxHeartbeats 20000 in
theorem su2WilsonExponent_norm_le (β : ℝ) (hβ : 0 ≤ β) (x y : SU2) :
    ‖su2WilsonExponentKernel β x y‖ ≤ β := by
  let U : SU2 := x * y⁻¹
  have hre2 : |U.val.trace.re| ≤ (2 : ℝ) := by
    simpa [fundamentalObservable] using fundamentalObservable_bounded 2 U
  change ‖((β / 2 * U.val.trace.re : ℝ) : ℂ)‖ ≤ β
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hdiv : |β / 2| = β / 2 :=
    abs_of_nonneg (div_nonneg hβ (by norm_num))
  rw [hdiv]
  nlinarith

theorem su2WilsonTaylorCoeff_hasSum (β : ℝ) :
    HasSum (fun n : ℕ => su2WilsonTaylorCoeff n * β ^ n) (Real.exp β) := by
  rw [Real.exp_eq_exp_ℝ]
  convert NormedSpace.expSeries_div_hasSum_exp β using 1
  funext n
  simp [su2WilsonTaylorCoeff, div_eq_mul_inv, mul_comm]

set_option maxHeartbeats 30000 in
theorem su2WilsonTaylorKernel_norm_le (β : ℝ) (hβ : 0 ≤ β)
    (N : ℕ) (x y : SU2) :
    ‖su2WilsonTaylorKernel β N x y‖ ≤ Real.exp β := by
  unfold su2WilsonTaylorKernel
  calc
    ‖∑ n ∈ Finset.range N,
        (su2WilsonTaylorCoeff n : ℂ) *
          su2WilsonExponentKernel β x y ^ n‖
        ≤ ∑ n ∈ Finset.range N,
            ‖(su2WilsonTaylorCoeff n : ℂ) *
              su2WilsonExponentKernel β x y ^ n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N,
          su2WilsonTaylorCoeff n * β ^ n := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (su2WilsonTaylorCoeff_nonneg n)]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _)
          (su2WilsonExponent_norm_le β hβ x y) n)
        (su2WilsonTaylorCoeff_nonneg n)
    _ ≤ ∑' n : ℕ, su2WilsonTaylorCoeff n * β ^ n :=
      (su2WilsonTaylorCoeff_hasSum β).summable.sum_le_tsum (Finset.range N)
        (fun n hn => mul_nonneg (su2WilsonTaylorCoeff_nonneg n)
          (pow_nonneg hβ n))
    _ = Real.exp β := (su2WilsonTaylorCoeff_hasSum β).tsum_eq

set_option maxHeartbeats 30000 in
/-- Uniform (Weierstrass M-test) convergence of the Fock truncations on the
whole compact crossing domain. -/
theorem su2WilsonTaylor_tendstoUniformlyOn (β : ℝ) (hβ : 0 ≤ β) :
    TendstoUniformlyOn
      (fun N (p : SU2 × SU2) => su2WilsonTaylorKernel β N p.1 p.2)
      (fun p : SU2 × SU2 => su2WilsonCrossingKernel β p.1 p.2)
      Filter.atTop Set.univ := by
  let term : ℕ → (SU2 × SU2) → ℂ :=
    fun n p => (su2WilsonTaylorCoeff n : ℂ) *
      su2WilsonExponentKernel β p.1 p.2 ^ n
  let bound : ℕ → ℝ :=
    fun n => su2WilsonTaylorCoeff n * β ^ n
  have hbound_summable : Summable bound := by
    have h := NormedSpace.expSeries_div_summable β
    convert h using 1
    funext n
    simp [bound, su2WilsonTaylorCoeff, div_eq_mul_inv, mul_comm]
  have hterm_bound :
      ∀ n p, p ∈ (Set.univ : Set (SU2 × SU2)) →
        ‖term n p‖ ≤ bound n := by
    intro n p hp
    simp only [term, bound, norm_mul, norm_pow]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (su2WilsonTaylorCoeff_nonneg n)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _)
        (su2WilsonExponent_norm_le β hβ p.1 p.2) n)
      (su2WilsonTaylorCoeff_nonneg n)
  have hu :
      HasSumUniformlyOn term (fun p => ∑' n, term n p) Set.univ :=
    HasSumUniformlyOn.of_norm_le_summable hbound_summable hterm_bound
  have huexact :
      HasSumUniformlyOn term
        (fun p : SU2 × SU2 => su2WilsonCrossingKernel β p.1 p.2)
        Set.univ := by
    apply hu.congr_right
    intro p hp
    exact tendsto_nhds_unique (hu.hasSum hp)
      (su2WilsonTaylor_hasSum β p.1 p.2)
  simpa [term, su2WilsonTaylorKernel] using
    huexact.tendstoUniformlyOn_finsetRange

theorem su2WilsonExponentKernel_continuous (β : ℝ) :
    Continuous (Function.uncurry (su2WilsonExponentKernel β)) := by
  have hmulInv : Continuous (fun p : SU2 × SU2 => p.1 * p.2⁻¹) :=
    continuous_fst.mul (continuous_inv.comp continuous_snd)
  have htrace : Continuous (fun p : SU2 × SU2 =>
      Matrix.trace
        (((p.1 * p.2⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))) :=
    (continuous_trace_sub 2).comp hmulInv
  have hre : Continuous (fun p : SU2 × SU2 =>
      (Matrix.trace
        (((p.1 * p.2⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))).re) :=
    Complex.reCLM.continuous.comp htrace
  exact Complex.continuous_ofReal.comp (continuous_const.mul hre)

theorem su2WilsonTaylorKernel_continuous (β : ℝ) (N : ℕ) :
    Continuous (Function.uncurry (su2WilsonTaylorKernel β N)) := by
  unfold su2WilsonTaylorKernel Function.uncurry
  refine continuous_finset_sum (Finset.range N) (fun n hn => ?_)
  exact continuous_const.mul ((su2WilsonExponentKernel_continuous β).pow n)

theorem su2WilsonExponentKernel_continuous_right (β : ℝ) (x : SU2) :
    Continuous (fun y => su2WilsonExponentKernel β x y) := by
  have hmulInv : Continuous (fun y : SU2 => x * y⁻¹) :=
    continuous_const.mul continuous_inv
  have htrace : Continuous (fun y : SU2 =>
      Matrix.trace
        (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))) :=
    (continuous_trace_sub 2).comp hmulInv
  have hre : Continuous (fun y : SU2 =>
      (Matrix.trace
        (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))).re) :=
    Complex.reCLM.continuous.comp htrace
  exact Complex.continuous_ofReal.comp (continuous_const.mul hre)

theorem su2WilsonTaylorKernel_continuous_right
    (β : ℝ) (N : ℕ) (x : SU2) :
    Continuous (fun y => su2WilsonTaylorKernel β N x y) := by
  unfold su2WilsonTaylorKernel
  refine continuous_finset_sum (Finset.range N) (fun n hn => ?_)
  exact continuous_const.mul
    ((su2WilsonExponentKernel_continuous_right β x).pow n)

theorem su2WilsonCrossingKernel_continuous (β : ℝ) :
    Continuous (Function.uncurry (su2WilsonCrossingKernel β)) := by
  have hmulInv : Continuous (fun p : SU2 × SU2 => p.1 * p.2⁻¹) :=
    continuous_fst.mul (continuous_inv.comp continuous_snd)
  have htrace : Continuous (fun p : SU2 × SU2 =>
      Matrix.trace
        (((p.1 * p.2⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))) :=
    (continuous_trace_sub 2).comp hmulInv
  have hre : Continuous (fun p : SU2 × SU2 =>
      (Matrix.trace
        (((p.1 * p.2⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))).re) :=
    Complex.reCLM.continuous.comp htrace
  have hreal : Continuous (fun p : SU2 × SU2 =>
      Real.exp ((β / 2) *
        (Matrix.trace
          (((p.1 * p.2⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))).re)) :=
    Real.continuous_exp.comp (continuous_const.mul hre)
  exact Complex.continuous_ofReal.comp hreal

theorem su2WilsonCrossingKernel_continuous_right (β : ℝ) (x : SU2) :
    Continuous (fun y => su2WilsonCrossingKernel β x y) := by
  have hreal : Continuous (fun y =>
      Real.exp ((β / 2) *
        (Matrix.trace
          (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))).re)) :=
    Real.continuous_exp.comp
      (continuous_const.mul
        (Complex.reCLM.continuous.comp
          ((continuous_trace_sub 2).comp
            (continuous_const.mul continuous_inv))))
  exact Complex.continuous_ofReal.comp hreal

set_option maxHeartbeats 100000 in
theorem su2WilsonInnerIntegral_tendsto
    (β : ℝ) (hβ : 0 ≤ β) (F : SU2 → ℂ) (hF : Continuous F) (x : SU2) :
    Filter.Tendsto
      (fun N => ∫ y,
        (starRingEnd ℂ) (F x) *
          su2WilsonTaylorKernel β N x y * F y ∂(sunHaarProb 2))
      Filter.atTop
      (𝓝 (∫ y,
        (starRingEnd ℂ) (F x) *
          su2WilsonCrossingKernel β x y * F y ∂(sunHaarProb 2))) := by
  apply tendsto_integral_of_dominated_convergence
    (fun y => ‖F x‖ * Real.exp β * ‖F y‖)
  · intro N
    have hksec : Continuous (fun y =>
        su2WilsonTaylorKernel β N x y) :=
      su2WilsonTaylorKernel_continuous_right β N x
    have hc : Continuous (fun y =>
        (starRingEnd ℂ) (F x) *
          su2WilsonTaylorKernel β N x y * F y) :=
      (continuous_const.mul hksec).mul hF
    exact hc.aestronglyMeasurable
  · have hc : Continuous (fun y => ‖F x‖ * Real.exp β * ‖F y‖) :=
      continuous_const.mul hF.norm
    exact hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro N
    exact Filter.Eventually.of_forall fun y => by
      simp only [norm_mul]
      have hs : ‖(starRingEnd ℂ) (F x)‖ = ‖F x‖ := by
        simpa using norm_star (F x)
      rw [hs]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (su2WilsonTaylorKernel_norm_le β hβ N x y)
          (norm_nonneg _))
        (norm_nonneg _)
  · filter_upwards [] with y
    simpa only [mul_assoc] using
      (tendsto_const_nhds.mul
        ((su2WilsonTaylor_tendsto β x y).mul tendsto_const_nhds))

set_option maxHeartbeats 200000 in
theorem su2WilsonKernelIntegralForm_tendsto
    (β : ℝ) (hβ : 0 ≤ β) (F : SU2 → ℂ) (hF : Continuous F) :
    Filter.Tendsto
      (fun N => kernelIntegralForm (sunHaarProb 2)
        (su2WilsonTaylorKernel β N) F)
      Filter.atTop
      (𝓝 (kernelIntegralForm (sunHaarProb 2)
        (su2WilsonCrossingKernel β) F)) := by
  let μ : Measure SU2 := sunHaarProb 2
  let C : ℝ := ∫ y, ‖F y‖ ∂μ
  have hFnorm_integrable : Integrable (fun y => ‖F y‖) μ :=
    hF.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hTaylor_cont (N : ℕ) :
      Continuous (Function.uncurry (su2WilsonTaylorKernel β N)) :=
    su2WilsonTaylorKernel_continuous β N
  have hinner (x : SU2) :
      Filter.Tendsto
        (fun N => ∫ y,
          (starRingEnd ℂ) (F x) *
            su2WilsonTaylorKernel β N x y * F y ∂μ)
        Filter.atTop
        (𝓝 (∫ y,
          (starRingEnd ℂ) (F x) *
            su2WilsonCrossingKernel β x y * F y ∂μ)) := by
    simpa [μ] using su2WilsonInnerIntegral_tendsto β hβ F hF x
  have houter_measurable (N : ℕ) :
      AEStronglyMeasurable
        (fun x => ∫ y,
          (starRingEnd ℂ) (F x) *
            su2WilsonTaylorKernel β N x y * F y ∂μ) μ := by
    have hc : Continuous (fun p : SU2 × SU2 =>
        (starRingEnd ℂ) (F p.1) *
          su2WilsonTaylorKernel β N p.1 p.2 * F p.2) := by
      exact
        (((hF.star.comp continuous_fst).mul (hTaylor_cont N)).mul
          (hF.comp continuous_snd))
    have hci : ContinuousOn
        (fun x => ∫ y,
          (starRingEnd ℂ) (F x) *
            su2WilsonTaylorKernel β N x y * F y ∂μ)
        Set.univ := by
      refine continuousOn_integral_of_compact_support
        (μ := μ) (s := Set.univ) (k := Set.univ) isCompact_univ
        ?_ ?_
      · simpa [Function.uncurry] using hc
      · intro p x hp hx
        simp at hx
    exact (continuousOn_univ.mp hci).aestronglyMeasurable
  have houter_bound (N : ℕ) :
      ∀ᵐ x ∂μ,
        ‖∫ y,
          (starRingEnd ℂ) (F x) *
            su2WilsonTaylorKernel β N x y * F y ∂μ‖
          ≤ ‖F x‖ * Real.exp β * C := by
    filter_upwards [] with x
    have hg : Integrable (fun y => ‖F x‖ * Real.exp β * ‖F y‖) μ :=
      hFnorm_integrable.const_mul _
    calc
      ‖∫ y,
          (starRingEnd ℂ) (F x) *
            su2WilsonTaylorKernel β N x y * F y ∂μ‖
          ≤ ∫ y, ‖F x‖ * Real.exp β * ‖F y‖ ∂μ := by
        apply norm_integral_le_of_norm_le hg
        filter_upwards [] with y
        simp only [norm_mul]
        have hs : ‖(starRingEnd ℂ) (F x)‖ = ‖F x‖ := by
          simpa using norm_star (F x)
        rw [hs]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (su2WilsonTaylorKernel_norm_le β hβ N x y)
            (norm_nonneg _))
          (norm_nonneg _)
      _ = ‖F x‖ * Real.exp β * C := by
        rw [integral_const_mul]
  have houter_dominator_integrable :
      Integrable (fun x => ‖F x‖ * Real.exp β * C) μ := by
    have hc : Continuous (fun x => ‖F x‖ * Real.exp β * C) := by
      fun_prop
    exact hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold kernelIntegralForm
  exact tendsto_integral_of_dominated_convergence
    (fun x => ‖F x‖ * Real.exp β * C)
    houter_measurable houter_dominator_integrable houter_bound
    (Filter.Eventually.of_forall hinner)

/-- Gate (3), exact version: the physical SU(2) Wilson crossing kernel has a
non-negative complex Haar quadratic form for every continuous observable. -/
theorem su2WilsonCrossing_isHaarPSDKernel
    (β : ℝ) (hβ : 0 ≤ β) :
    IsHaarPSDKernel (sunHaarProb 2) (su2WilsonCrossingKernel β) := by
  intro F hF
  let q : ℕ → ℂ := fun N =>
    kernelIntegralForm (sunHaarProb 2) (su2WilsonTaylorKernel β N) F
  let qLimit : ℂ :=
    kernelIntegralForm (sunHaarProb 2) (su2WilsonCrossingKernel β) F
  have hq : Filter.Tendsto q Filter.atTop (𝓝 qLimit) := by
    simpa [q, qLimit] using su2WilsonKernelIntegralForm_tendsto β hβ F hF
  choose r hr_nonneg hr_eq using fun N =>
    su2WilsonTaylor_isHaarPSDKernel β hβ N F hF
  have hq_re_nonneg (N : ℕ) : 0 ≤ (q N).re := by
    change 0 ≤
      (kernelIntegralForm (sunHaarProb 2)
        (su2WilsonTaylorKernel β N) F).re
    rw [hr_eq N]
    simp only [ofReal_re]
    exact hr_nonneg N
  have hq_im_zero (N : ℕ) : (q N).im = 0 := by
    change
      (kernelIntegralForm (sunHaarProb 2)
        (su2WilsonTaylorKernel β N) F).im = 0
    rw [hr_eq N]
    simp
  have hq_re :
      Filter.Tendsto (fun N => (q N).re) Filter.atTop (𝓝 qLimit.re) :=
    (Complex.continuous_re.tendsto qLimit).comp hq
  have hq_im :
      Filter.Tendsto (fun N => (q N).im) Filter.atTop (𝓝 qLimit.im) :=
    (Complex.continuous_im.tendsto qLimit).comp hq
  have hqLimit_re_nonneg : 0 ≤ qLimit.re :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hq_re
      (Filter.Eventually.of_forall hq_re_nonneg)
  have hqLimit_im_zero : qLimit.im = 0 := by
    have hz :
        Filter.Tendsto (fun N : ℕ => (q N).im) Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa only [hq_im_zero] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
          Filter.atTop (𝓝 0))
    exact tendsto_nhds_unique hq_im hz
  refine ⟨qLimit.re, hqLimit_re_nonneg, ?_⟩
  change qLimit = (qLimit.re : ℂ)
  apply Complex.ext
  · simp
  · simpa using hqLimit_im_zero

theorem su2WilsonCrossingKernel_pos (β : ℝ) (x y : SU2) :
    0 < (su2WilsonCrossingKernel β x y).re := by
  change 0 < Real.exp ((β / 2) *
    (Matrix.trace (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))).re)
  exact Real.exp_pos _

theorem su2WilsonCrossingKernel_re_lower
    (β : ℝ) (hβ : 0 ≤ β) (x y : SU2) :
    Real.exp (-β) ≤ (su2WilsonCrossingKernel β x y).re := by
  let t : ℝ := (β / 2) *
    (Matrix.trace
      (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))).re
  have htAbs : |t| ≤ β := by
    have hn := su2WilsonExponent_norm_le β hβ x y
    change ‖((t : ℝ) : ℂ)‖ ≤ β at hn
    simpa [Complex.norm_real, Real.norm_eq_abs] using hn
  change Real.exp (-β) ≤ Real.exp t
  rw [Real.exp_le_exp]
  exact (neg_le_neg htAbs).trans (neg_abs_le t)

end YangMills.OS
