/-
  YangMills/ClayCore/SchurOffDiagonal.lean

  Off-diagonal vanishing:  ∫ U_{ii} · conj(U_{jj}) dHaar = 0  for i ≠ j.
  Uses left-invariance of the Haar measure on SU(N) together with the
  two-site phase element diag(I at i, -I at j, 1 elsewhere), which flips
  the sign of the integrand.

  Status: no sorry, no new axioms.
  Oracle must remain [propext, Classical.choice, Quot.sound].
-/
import YangMills.ClayCore.SchurTwoSitePhase

noncomputable section
open MeasureTheory Matrix Complex
open scoped BigOperators

namespace YangMills.ClayCore

variable {N : ℕ} [NeZero N]

private lemma star_neg_I' : (star (-Complex.I : ℂ)) = Complex.I := by
  rw [star_neg]
  show -(starRingEnd ℂ) Complex.I = Complex.I
  rw [Complex.conj_I]; ring

/-- Off-diagonal vanishing: `∫ U_{ii} · conj(U_{jj}) dHaar = 0` on SU(N) for `i ≠ j`. -/
theorem sunHaarProb_offdiag_integral_zero {i j : Fin N} (hij : i ≠ j) :
    (∫ U, U.val i i * star (U.val j j) ∂(sunHaarProb N)) = 0 := by
  haveI hinv : (sunHaarProb N).IsMulLeftInvariant := sunHaarProb_isMulLeftInvariant N
  set I0 : ℂ := ∫ U, U.val i i * star (U.val j j) ∂(sunHaarProb N) with hI0
  have hL :
      (∫ U, ((twoSiteSU i j hij) * U).val i i
            * star (((twoSiteSU i j hij) * U).val j j) ∂(sunHaarProb N)) = I0 := by
    rw [hI0]
    exact MeasureTheory.integral_mul_left_eq_self
      (μ := sunHaarProb N)
      (fun U => U.val i i * star (U.val j j)) (twoSiteSU i j hij)
  have hfun :
      (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        ((twoSiteSU i j hij) * U).val i i
          * star (((twoSiteSU i j hij) * U).val j j))
      = fun U => -(U.val i i * star (U.val j j)) := by
    funext U
    rw [twoSiteSU_apply_diag, twoSiteSU_apply_diag,
        twoSiteVec_at_i, twoSiteVec_at_j hij, StarMul.star_mul, star_neg_I']
    linear_combination (U.val i i * star (U.val j j)) * Complex.I_mul_I
  rw [hfun, MeasureTheory.integral_neg] at hL
  linear_combination (-(1 : ℂ) / 2) * hL

end YangMills.ClayCore

end