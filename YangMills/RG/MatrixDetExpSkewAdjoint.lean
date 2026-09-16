/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLogMatrixNoWinding
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Determinant of the exponential on the skew-adjoint matrix sector

This file supplies the finite-dimensional determinant/exponential bridge
needed by the CMP99 principal-logarithm construction.  It is proved from
unitary diagonalization, rather than assumed as a general matrix identity.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

/-- Mathlib exposes the L2-operator-norm matrix ingredients separately; this
local bundle lets the continuous functional calculus consume the same norm. -/
local instance matrixL2CStarAlgebra :
    CStarAlgebra (Matrix (Fin Nc) (Fin Nc) ℂ) where

local instance matrixRealComplexScalarTower :
    IsScalarTower ℝ ℂ (Matrix (Fin Nc) (Fin Nc) ℂ) where
  smul_assoc r c X := by
    ext i j
    exact smul_assoc r c (X i j)

local instance matrixRationalNormedAlgebra :
    NormedAlgebra ℚ (Matrix (Fin Nc) (Fin Nc) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

/-- The determinant/exponential identity for a matrix supplied with an
explicit unitary diagonalization. -/
theorem det_exp_eq_exp_trace_of_unitary_diagonalization
    (X : Matrix (Fin Nc) (Fin Nc) ℂ)
    (U : unitary (Matrix (Fin Nc) (Fin Nc) ℂ))
    (v : Fin Nc → ℂ)
    (hX : X = (U : Matrix (Fin Nc) (Fin Nc) ℂ) * diagonal v *
      star (U : Matrix (Fin Nc) (Fin Nc) ℂ)) :
    Matrix.det (NormedSpace.exp X) = Complex.exp (Matrix.trace X) := by
  let M : Matrix (Fin Nc) (Fin Nc) ℂ := U
  have hM : IsUnit M := Unitary.isUnit_coe
  have hstar : star M = M⁻¹ := by
    apply hM.mul_left_cancel
    have hleft : M * star M = 1 := by
      simpa only [M] using Unitary.coe_mul_star_self U
    have hright : M * M⁻¹ = 1 :=
      Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hM)
    exact hleft.trans hright.symm
  rw [hX, show (U : Matrix (Fin Nc) (Fin Nc) ℂ) * diagonal v *
      star (U : Matrix (Fin Nc) (Fin Nc) ℂ) = M * diagonal v * M⁻¹ by
        simp only [M, hstar]]
  rw [Matrix.exp_conj M (diagonal v) hM, Matrix.det_conj hM,
    Matrix.exp_diagonal, Matrix.det_diagonal, Matrix.trace_conj hM,
    Matrix.trace_diagonal, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Pi.coe_exp]
  exact (congrFun Complex.exp_eq_exp_ℂ (v i)).symm

/-- The determinant/exponential identity on `I` times the Hermitian sector. -/
theorem det_exp_I_smul_eq_exp_trace_of_isHermitian
    (H : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hH : H.IsHermitian) :
    Matrix.det (NormedSpace.exp (Complex.I • H)) =
      Complex.exp (Matrix.trace (Complex.I • H)) := by
  apply det_exp_eq_exp_trace_of_unitary_diagonalization
    (Complex.I • H) hH.eigenvectorUnitary
    (fun i => Complex.I * (hH.eigenvalues i : ℂ))
  have hdiag : Complex.I •
      diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
      diagonal (fun i => Complex.I * (hH.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, smul_eq_mul]
  calc
    Complex.I • H = Complex.I •
        Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
          (diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
      congrArg (Complex.I • ·) hH.spectral_theorem
    _ = Complex.I •
        ((hH.eigenvectorUnitary : Matrix (Fin Nc) (Fin Nc) ℂ) *
          diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
          star (hH.eigenvectorUnitary : Matrix (Fin Nc) (Fin Nc) ℂ)) := by
      rw [Unitary.conjStarAlgAut_apply]
    _ = (hH.eigenvectorUnitary : Matrix (Fin Nc) (Fin Nc) ℂ) *
        (Complex.I • diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *
        star (hH.eigenvectorUnitary : Matrix (Fin Nc) (Fin Nc) ℂ) := by
      symm
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    _ = (hH.eigenvectorUnitary : Matrix (Fin Nc) (Fin Nc) ℂ) *
        diagonal (fun i => Complex.I * (hH.eigenvalues i : ℂ)) *
        star (hH.eigenvectorUnitary : Matrix (Fin Nc) (Fin Nc) ℂ) := by
      rw [hdiag]

/-- **Determinant/exponential bridge on the physical skew-adjoint sector.** -/
theorem Matrix.det_exp_eq_exp_trace_of_mem_skewAdjoint
    (X : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hX : X ∈ skewAdjoint (Matrix (Fin Nc) (Fin Nc) ℂ)) :
    Matrix.det (NormedSpace.exp X) = Complex.exp (Matrix.trace X) := by
  let Xsk : skewAdjoint (Matrix (Fin Nc) (Fin Nc) ℂ) := ⟨X, hX⟩
  let H : selfAdjoint (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    skewAdjoint.negISMul Xsk
  have hrecover : Complex.I •
      (H : Matrix (Fin Nc) (Fin Nc) ℂ) = X := by
    exact skewAdjoint.I_smul_neg_I Xsk
  rw [← hrecover]
  exact det_exp_I_smul_eq_exp_trace_of_isHermitian
    (H : Matrix (Fin Nc) (Fin Nc) ℂ) H.prop.isHermitian

/-- Determinant one quantizes the trace of an exponential in the physical
skew-adjoint matrix sector. -/
theorem matrixTraceQuantized_of_det_exp_eq_one_of_mem_skewAdjoint
    (X : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hX : X ∈ skewAdjoint (Matrix (Fin Nc) (Fin Nc) ℂ))
    (hdet : Matrix.det (NormedSpace.exp X) = 1) :
    MatrixTraceQuantized X := by
  have hexp : Complex.exp (Matrix.trace X) = 1 := by
    rw [← Matrix.det_exp_eq_exp_trace_of_mem_skewAdjoint X hX]
    exact hdet
  rcases Complex.exp_eq_one_iff.mp hexp with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [hk]
  push_cast
  ring

set_option maxHeartbeats 800000 in
/-- A determinant-one unitary in the Mercator ball has a trace-quantized
principal logarithm.  The exponential is recovered from Mathlib's principal
argument construction, so no inverse identity is assumed. -/
theorem matrixTraceQuantized_nearLog_unitary_sub_one_of_det_eq_one
    (D : unitary (Matrix (Fin Nc) (Fin Nc) ℂ))
    (hD : ‖(D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hdet : Matrix.det (D : Matrix (Fin Nc) (Fin Nc) ℂ) = 1) :
    MatrixTraceQuantized
      (nearLog ((D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) := by
  letI : IsScalarTower ℝ ℂ (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    matrixRealComplexScalarTower
  let X : Matrix (Fin Nc) (Fin Nc) ℂ :=
    nearLog ((D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)
  have hX : X ∈ skewAdjoint (Matrix (Fin Nc) (Fin Nc) ℂ) := by
    simpa only [X] using
      (@nearLog_unitary_sub_one_mem_skewAdjoint
        (Matrix (Fin Nc) (Fin Nc) ℂ) matrixL2CStarAlgebra inferInstance
        matrixRealComplexScalarTower inferInstance D hD)
  have hexp : NormedSpace.exp X =
      (D : Matrix (Fin Nc) (Fin Nc) ℂ) := by
    rw [show X = Complex.I •
        (Unitary.argSelfAdjoint D : Matrix (Fin Nc) (Fin Nc) ℂ) by
      exact (@nearLog_unitary_sub_one_eq_cfc_log
        (Matrix (Fin Nc) (Fin Nc) ℂ) matrixL2CStarAlgebra inferInstance
        matrixRealComplexScalarTower inferInstance D hD).trans
        (@cfc_log_unitary_eq_I_smul_argSelfAdjoint
          (Matrix (Fin Nc) (Fin Nc) ℂ) matrixL2CStarAlgebra inferInstance
          matrixRealComplexScalarTower inferInstance D hD)]
    have hunitary := expUnitary_argSelfAdjoint
      (u := D) (hD.trans (by norm_num))
    exact congrArg Subtype.val hunitary
  apply matrixTraceQuantized_of_det_exp_eq_one_of_mem_skewAdjoint X hX
  rw [hexp]
  exact hdet

/-- **Determinant-one no-winding closure.**  The previous quantization
hypothesis is now generated internally from the special-unitary determinant. -/
theorem trace_nearLog_unitary_sub_one_eq_zero_of_det_eq_one_of_noWinding
    (D : unitary (Matrix (Fin Nc) (Fin Nc) ℂ))
    (hD : ‖(D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hdet : Matrix.det (D : Matrix (Fin Nc) (Fin Nc) ℂ) = 1)
    (hnoWinding : (Nc : ℝ) *
      ‖nearLog ((D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    Matrix.trace (nearLog ((D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) = 0 := by
  exact trace_nearLog_unitary_sub_one_eq_zero_of_quantized_of_noWinding D
    (matrixTraceQuantized_nearLog_unitary_sub_one_of_det_eq_one D hD hdet)
    hnoWinding

/-- A skew-adjoint traceless matrix exponentiates into the special unitary
group.  Unitarity and determinant one are generated from the two hypotheses. -/
theorem Matrix.exp_mem_specialUnitaryGroup_of_mem_skewAdjoint_of_trace_eq_zero
    (X : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hX : X ∈ skewAdjoint (Matrix (Fin Nc) (Fin Nc) ℂ))
    (htrace : Matrix.trace X = 0) :
    NormedSpace.exp X ∈ Matrix.specialUnitaryGroup (Fin Nc) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hX
  · rw [Matrix.det_exp_eq_exp_trace_of_mem_skewAdjoint X hX, htrace,
      Complex.exp_zero]

end

end YangMills.RG
