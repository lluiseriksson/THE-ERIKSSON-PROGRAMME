/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLogComplex
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# The Mercator coordinate as a continuous functional calculus

This file lifts the scalar identity

`nearLog z = Complex.log (1 + z)` for `‖z‖ < 1`

to normal elements of a unital complex C⋆-algebra.  It is the analytic
bridge needed to turn the scalar inverse identity on the unit circle into a
matrix/unitary inverse identity without diagonalizing coordinates by hand.

No determinant or trace conclusion is made here.  In particular,
`det D = 1` alone does not select a zero-winding logarithm branch in arbitrary
dimension.
-/

namespace YangMills.RG

noncomputable section

open scoped ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [IsScalarTower ℝ ℂ A]

/-- The spectrum of an element in the open unit ball lies in the scalar open
unit disk.  This is the precise scalar domain on which the Mercator series is
the principal logarithm. -/
theorem spectrum_subset_ball_zero_one {Y : A} (hY : ‖Y‖ < 1) :
    spectrum ℂ Y ⊆ Metric.ball 0 1 := by
  intro z hz
  simp only [Metric.mem_ball, dist_zero_right]
  exact (spectrum.norm_le_norm_of_mem hz).trans_lt hY

/-- The Mercator power series of a normal element is exactly the continuous
functional calculus of the principal scalar logarithm on `1 + spectrum Y`.

The proof maps the absolutely summable series of continuous scalar functions
through the continuous CFC homomorphism.  Thus the equality is not a
coordinatewise matrix postulate. -/
theorem nearLog_eq_cfc_log_one_add (Y : A) [IsStarNormal Y] (hY : ‖Y‖ < 1) :
    nearLog Y = cfc (fun z : ℂ => Complex.log (1 + z)) Y := by
  let F : ℕ → C(spectrum ℂ Y, ℂ) := fun n =>
    ⟨fun z => logCoeff n • (z : ℂ) ^ n, by fun_prop⟩
  have hF_norm (n : ℕ) : ‖F n‖ ≤ ‖Y‖ ^ n := by
    apply (ContinuousMap.norm_le _ (pow_nonneg (norm_nonneg Y) n)).2
    intro z
    dsimp [F]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      |logCoeff n| * ‖(z : ℂ)‖ ^ n
          ≤ 1 * ‖Y‖ ^ n := by
            gcongr
            · exact abs_logCoeff_le_one n
            · exact spectrum.norm_le_norm_of_mem z.property
      _ = ‖Y‖ ^ n := one_mul _
  have hF : Summable F :=
    Summable.of_norm_bounded
      (summable_geometric_of_lt_one (norm_nonneg Y) hY) hF_norm
  have hlogCont : ContinuousOn (fun z : ℂ => Complex.log (1 + z)) (spectrum ℂ Y) :=
    (show Continuous (fun z : ℂ => (1 : ℂ) + z) by fun_prop).continuousOn.clog
      fun z hz => Complex.mem_slitPlane_of_norm_lt_one <|
        (spectrum.norm_le_norm_of_mem hz).trans_lt hY
  let L : C(spectrum ℂ Y, ℂ) :=
    ⟨fun z => Complex.log (1 + (z : ℂ)), hlogCont.restrict⟩
  have hFL : ∑' n, F n = L := by
    ext z
    have heval := (ContinuousMap.evalCLM ℂ z).map_tsum hF
    change (∑' n, F n) z = Complex.log (1 + (z : ℂ))
    change (∑' n, F n) z = ∑' n, F n z at heval
    rw [heval]
    exact nearLog_complex
      ((spectrum.norm_le_norm_of_mem z.property).trans_lt hY)
  let hYn : IsStarNormal Y := inferInstance
  have hmap := (cfcL (R := ℂ) (A := A) (a := Y) hYn).map_tsum hF
  rw [hFL] at hmap
  rw [nearLog]
  calc
    ∑' n : ℕ, logCoeff n • Y ^ n
        = ∑' n : ℕ, (cfcL (R := ℂ) (A := A) (a := Y) hYn) (F n) := by
          apply tsum_congr
          intro n
          rw [cfcL_apply]
          change logCoeff n • Y ^ n =
            cfcHom (R := ℂ) (A := A) (a := Y) hYn (F n)
          calc
            logCoeff n • Y ^ n =
                cfc (fun z : ℂ => logCoeff n • z ^ n) Y := by
                  rw [cfc_smul (p := IsStarNormal) (s := logCoeff n)
                    (f := fun z : ℂ => z ^ n) (a := Y) (hf := by fun_prop),
                    cfc_pow_id (p := IsStarNormal) (R := ℂ) Y n hYn]
            _ = cfcHom (R := ℂ) (A := A) (a := Y) hYn (F n) := by
              rw [cfc_apply (f := fun z : ℂ => logCoeff n • z ^ n)
                (a := Y) (ha := hYn) (hf := by fun_prop)]
              congr
    _ = (cfcL (R := ℂ) (A := A) (a := Y) hYn) L := hmap.symm
    _ = cfc (fun z : ℂ => Complex.log (1 + z)) Y := by
      rw [cfcL_apply]
      change cfcHom (R := ℂ) (A := A) (a := Y) hYn L =
        cfc (fun z : ℂ => Complex.log (1 + z)) Y
      rw [cfc_apply (f := fun z : ℂ => Complex.log (1 + z))
        (a := Y) (ha := hYn) (hf := hlogCont)]
      congr

end

end YangMills.RG
