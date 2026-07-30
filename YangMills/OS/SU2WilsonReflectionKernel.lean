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

/-- The exact single-plaquette SU(2) Wilson crossing factor. -/
noncomputable def su2WilsonCrossingKernel (β : ℝ) (x y : SU2) : ℂ :=
  Real.exp ((β / 2) *
    (Matrix.trace (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))).re)

theorem su2WilsonCrossingKernel_pos (β : ℝ) (x y : SU2) :
    0 < (su2WilsonCrossingKernel β x y).re := by
  change 0 < Real.exp ((β / 2) *
    (Matrix.trace (((x * y⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ))).re)
  exact Real.exp_pos _

end YangMills.OS
