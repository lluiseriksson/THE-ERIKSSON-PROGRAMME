/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLogCFC
import YangMills.RG.BalabanCMP99UbarUnitary
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected

/-!
# The matrix/unitary Mercator logarithm

This file consumes the CFC lift of the Mercator series on a unitary element.
It proves that the near-identity Mercator coordinate is the principal
functional-calculus logarithm and hence is skew-adjoint.  The inverse identity
then follows from the exact algebraic equivalence already isolated by the
CMP99 unitary layer.

No trace conclusion is inferred from determinant one: that requires an
additional no-winding hypothesis in dimensions where a nontrivial central
unitary can still lie in the Mercator ball.
-/

namespace YangMills.RG

noncomputable section

open scoped ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [IsScalarTower ℝ ℂ A]
  [NormedAlgebra ℚ A]

/-- The Mercator coordinate of a near-identity unitary is the principal CFC
logarithm of the unitary itself. -/
theorem nearLog_unitary_sub_one_eq_cfc_log (D : unitary A)
    (hD : ‖(D : A) - 1‖ < 1) :
    nearLog ((D : A) - 1) = cfc Complex.log (D : A) := by
  letI : IsStarNormal ((D : A) - 1) := by
    have hnormal : IsStarNormal (- (1 - (D : A))) := inferInstance
    rw [show (D : A) - 1 = -(1 - (D : A)) by noncomm_ring]
    exact hnormal
  rw [nearLog_eq_cfc_log_one_add ((D : A) - 1) hD]
  have hsub : cfc (fun z : ℂ => z - 1) (D : A) = (D : A) - 1 := by
    calc
      cfc (fun z : ℂ => z - 1) (D : A) =
          cfc (fun z : ℂ => z) (D : A) -
            cfc (fun _ : ℂ => 1) (D : A) :=
        cfc_sub (p := IsStarNormal) (fun z : ℂ => z) (fun _ : ℂ => 1) (D : A)
          (by fun_prop) (by fun_prop)
      _ = (D : A) - 1 := by
        rw [cfc_id' ℂ (D : A), cfc_const_one ℂ (D : A)]
  have hshift : ∀ z ∈ spectrum ℂ (D : A), ‖z - 1‖ < 1 := by
    intro z hz
    have hzle := norm_apply_le_norm_cfc (fun z : ℂ => z - 1) (D : A) hz
    rw [hsub] at hzle
    exact hzle.trans_lt hD
  have houter : ContinuousOn (fun w : ℂ => Complex.log (1 + w))
      ((fun z : ℂ => z - 1) '' spectrum ℂ (D : A)) := by
    apply (show Continuous (fun w : ℂ => (1 : ℂ) + w) by fun_prop).continuousOn.clog
    rintro w ⟨z, hz, rfl⟩
    exact Complex.mem_slitPlane_of_norm_lt_one (hshift z hz)
  rw [← hsub, ← cfc_comp' (p := IsStarNormal)
    (fun w : ℂ => Complex.log (1 + w)) (fun z : ℂ => z - 1) (D : A)
    houter (by fun_prop)]
  apply cfc_congr
  intro z hz
  simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- On the spectrum of a unitary, the principal logarithm is `i` times the
principal argument. -/
theorem cfc_log_unitary_eq_I_smul_argSelfAdjoint (D : unitary A)
    (hD : ‖(D : A) - 1‖ < 1) :
    cfc Complex.log (D : A) =
      Complex.I • (Unitary.argSelfAdjoint D : A) := by
  rw [Unitary.argSelfAdjoint_coe]
  have hslit : spectrum ℂ (D : A) ⊆ Complex.slitPlane :=
    (Unitary.spectrum_subset_slitPlane_iff_norm_lt_two D.property).2
      (hD.trans (by norm_num))
  have hargCont : ContinuousOn (fun z : ℂ => (Complex.arg z : ℂ))
      (spectrum ℂ (D : A)) :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuousOn_arg.mono hslit)
  rw [← cfc_smul (p := IsStarNormal) (s := Complex.I)
    (f := fun z : ℂ => (Complex.arg z : ℂ)) (a := (D : A)) hargCont]
  apply cfc_congr
  intro z hz
  have hnorm : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary D.property hz
  change Complex.log z = Complex.I * (Complex.arg z : ℂ)
  rw [Complex.log, hnorm, Real.log_one]
  norm_num
  ring

/-- **Matrix/unitary skew-adjointness closure.**  The Mercator logarithm of a
unitary in the open unit ball around one is skew-adjoint. -/
theorem nearLog_unitary_sub_one_mem_skewAdjoint (D : unitary A)
    (hD : ‖(D : A) - 1‖ < 1) :
    nearLog ((D : A) - 1) ∈ skewAdjoint A := by
  rw [nearLog_unitary_sub_one_eq_cfc_log D hD,
    cfc_log_unitary_eq_I_smul_argSelfAdjoint D hD]
  exact (Unitary.argSelfAdjoint D).prop.smul_mem_skewAdjoint Complex.conj_I

/-- **Matrix/unitary inverse Mercator identity.**  For a near-identity
unitary, the inverse deviation has the negative Mercator coordinate. -/
theorem nearLog_unitary_star_sub_one_eq_neg (D : unitary A)
    (hD : ‖(D : A) - 1‖ < 1) :
    nearLog (((star D : unitary A) : A) - 1) =
      -nearLog ((D : A) - 1) :=
  (nearLog_unitary_sub_one_mem_skewAdjoint_iff D).mp
    (nearLog_unitary_sub_one_mem_skewAdjoint D hD)

end

end YangMills.RG
