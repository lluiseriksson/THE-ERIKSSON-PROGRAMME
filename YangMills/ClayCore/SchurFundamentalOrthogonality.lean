/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.MeasureTheory.Function.L2Space
import YangMills.ClayCore.SchurEntryOffDiag
import YangMills.ClayCore.SchurNormOne

/-!
# Exact Schur orthogonality for the fundamental representation of SU(N)

This file closes the fundamental-representation case of the matrix-coefficient
`L²` API:

* right multiplication by a traceless diagonal phase separates distinct
  columns, complementing the existing left-phase separation of distinct rows;
* every fundamental matrix coefficient has squared Haar norm `1 / N`;
* consequently

    `∫ Uᵢⱼ * conj(Uₖₗ) dHaar = δᵢₖ δⱼₗ / N`;

* the coefficients are packaged as continuous functions and as vectors in
  `L²(SU(N), Haar)`, with the same orthogonality identity for the Hilbert-space
  inner product.

This is the defining-representation instance of Schur orthogonality. It does
not prove generic Peter-Weyl or orthogonality for arbitrary irreducible
representations.
-/

noncomputable section

open Matrix Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace YangMills.ClayCore

variable {N : ℕ} [NeZero N]

/-- Right multiplication by a diagonal phase scales a matrix column. -/
lemma diagPhaseSU_apply_entry_right (θ : Fin N → ℝ) (hθ : ∑ k, θ k = 0)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (i j : Fin N) :
    ((U * diagPhaseSU θ hθ).val) i j = U.val i j * diagPhaseVec θ j := by
  have hmul : ((U * diagPhaseSU θ hθ).val : Matrix (Fin N) (Fin N) ℂ) =
      U.val * (diagPhaseSU θ hθ).val := rfl
  rw [hmul, diagPhaseSU_val]
  show (U.val * diagPhaseMat θ) i j = U.val i j * diagPhaseVec θ j
  unfold diagPhaseMat
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.diagonal_apply_eq]
  · intro b _ hbj
    rw [Matrix.diagonal_apply_ne _ hbj]
    ring
  · intro h
    exact absurd (Finset.mem_univ j) h

private lemma star_mul_complex (a b : ℂ) :
    star (a * b) = star b * star a := by
  rw [show star (a * b) = (starRingEnd ℂ) (a * b) from rfl,
    (starRingEnd ℂ).map_mul, mul_comm,
    show (starRingEnd ℂ) a = star a from rfl,
    show (starRingEnd ℂ) b = star b from rfl]

/-- Distinct columns acquire a minus sign under a suitable right phase. -/
lemma piAntiSymSU_entry_prod_flip_right (j l : Fin N) (hjl : j ≠ l)
    (i k : Fin N) (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ((U * piAntiSymSU j l).val) i j * star ((U * piAntiSymSU j l).val k l) =
      -(U.val i j * star (U.val k l)) := by
  change ((U * diagPhaseSU (piAntiSymAngle j l) (piAntiSymAngle_sum_zero j l)).val) i j *
      star (((U * diagPhaseSU (piAntiSymAngle j l)
        (piAntiSymAngle_sum_zero j l)).val) k l) = _
  rw [diagPhaseSU_apply_entry_right, diagPhaseSU_apply_entry_right, star_mul_complex]
  have hphase : diagPhaseVec (piAntiSymAngle j l) j *
      star (diagPhaseVec (piAntiSymAngle j l) l) = -1 :=
    piAntiSymSU_phase j l hjl
  linear_combination (U.val i j * star (U.val k l)) * hphase

/-- Column-off-diagonal matrix coefficients are orthogonal under Haar. -/
theorem sunHaarProb_entry_offdiag_right (i k : Fin N) (j l : Fin N) (hjl : j ≠ l) :
    (∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N)) = 0 := by
  set I₀ := ∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) with hI₀
  have hflip := piAntiSymSU_entry_prod_flip_right j l hjl i k
  have heq_fun :
      (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        ((U * piAntiSymSU j l).val) i j * star ((U * piAntiSymSU j l).val k l)) =
      (fun U => -(U.val i j * star (U.val k l))) := by
    funext U
    exact hflip U
  have hinv : I₀ = -I₀ := by
    have hright :
        (∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N)) =
          ∫ U, ((U * piAntiSymSU j l).val) i j *
            star ((U * piAntiSymSU j l).val k l) ∂(sunHaarProb N) :=
      (MeasureTheory.integral_mul_right_eq_self
        (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          U.val i j * star (U.val k l))
        (piAntiSymSU j l)).symm
    calc I₀
        = ∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) := hI₀
      _ = ∫ U, ((U * piAntiSymSU j l).val) i j *
          star ((U * piAntiSymSU j l).val k l) ∂(sunHaarProb N) := hright
      _ = ∫ U, -(U.val i j * star (U.val k l)) ∂(sunHaarProb N) := by
          rw [heq_fun]
      _ = -∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) := integral_neg _
      _ = -I₀ := by rw [← hI₀]
  have h2I : (2 : ℂ) * I₀ = 0 := by
    have hdouble : (2 : ℂ) * I₀ = I₀ + I₀ := by ring
    rw [hdouble]
    nth_rw 2 [hinv]
    ring
  exact (mul_eq_zero.mp h2I).resolve_left (by norm_num)

/-- Exact Haar norm of an arbitrary fundamental matrix coefficient. -/
theorem sunHaarProb_entry_normSq_integral_eq_inv_N (i j : Fin N) :
    (∫ U, U.val i j * star (U.val i j) ∂(sunHaarProb N)) =
      (1 : ℂ) / (N : ℂ) := by
  have hpt : ∀ U : Matrix.specialUnitaryGroup (Fin N) ℂ,
      U.val i j * star (U.val i j) = ((Complex.normSq (U.val i j) : ℝ) : ℂ) :=
    fun U => Complex.mul_conj (U.val i j)
  rw [MeasureTheory.integral_congr_ae (ae_of_all _ hpt)]
  calc
    (∫ U, ((Complex.normSq (U.val i j) : ℝ) : ℂ) ∂(sunHaarProb N))
        = ((∫ U, (Complex.normSq (U.val i j) : ℝ) ∂(sunHaarProb N) : ℝ) : ℂ) :=
          integral_ofReal
    _ = (((1 : ℝ) / N : ℝ) : ℂ) := by
          rw [sunHaarProb_entry_normSq_eq_inv_Nc j i]
    _ = (1 : ℂ) / (N : ℂ) := by norm_num [map_div₀]

/-- **Fundamental Schur orthogonality.**

`∫ Uᵢⱼ conj(Uₖₗ) dHaar = δᵢₖ δⱼₗ / N`.
-/
theorem sunHaarProb_fundamental_entry_orthogonality
    (i j k l : Fin N) :
    (∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N)) =
      if i = k ∧ j = l then (1 : ℂ) / (N : ℂ) else 0 := by
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      rw [if_pos ⟨rfl, rfl⟩]
      exact sunHaarProb_entry_normSq_integral_eq_inv_N i j
    · rw [if_neg (fun h => hjl h.2)]
      exact sunHaarProb_entry_offdiag_right i i j l hjl
  · rw [if_neg (fun h => hik h.1)]
    exact sunHaarProb_entry_offdiag i k hik j l

/-- A fundamental matrix coefficient as a continuous function on `SU(N)`. -/
def fundamentalMatrixCoeff (i j : Fin N) :
    C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℂ) :=
  ⟨fun U => U.val i j, continuous_val_entry i j⟩

/-- A fundamental matrix coefficient as a vector in Haar `L²`. -/
noncomputable def fundamentalMatrixCoeffL2 (i j : Fin N) :
    Lp ℂ 2 (sunHaarProb N) :=
  ContinuousMap.toLp 2 (sunHaarProb N) ℂ (fundamentalMatrixCoeff i j)

/-- Fundamental Schur orthogonality in the Hilbert-space `L²` interface. -/
theorem inner_fundamentalMatrixCoeffL2
    (i j k l : Fin N) :
    inner ℂ (fundamentalMatrixCoeffL2 k l) (fundamentalMatrixCoeffL2 i j) =
      if i = k ∧ j = l then (1 : ℂ) / (N : ℂ) else 0 := by
  rw [fundamentalMatrixCoeffL2, fundamentalMatrixCoeffL2,
    ContinuousMap.inner_toLp]
  exact sunHaarProb_fundamental_entry_orthogonality i j k l

end YangMills.ClayCore
