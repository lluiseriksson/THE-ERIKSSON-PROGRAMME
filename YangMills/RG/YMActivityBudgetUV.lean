/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.SingleScaleUVDecay
import YangMills.RG.YMActivityBudget

/-!
# UV-facing consumers for Yang--Mills activity error budgets

This file connects the source-independent `YMActivityErrorBudget` bookkeeping
to the existing `RawYMActivityDecay` predicate.  It is still entirely
conditional: the source-shaped term, covariance defect, dictionary defect,
support defect, and Jacobian defect estimates remain explicit hypotheses.

Honest scope: this proves no component estimate, no Appendix-F theorem, no
Eq. (2.31) source dictionary, no `hRpoly`, no continuum limit, and no Clay
statement.  It only packages the shared scalar UV profile once those component
estimates are available.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

namespace YMActivityErrorBudget

/-- A source-plus-defects Yang--Mills activity estimate produces the existing
`RawYMActivityDecay` interface.

The common scalar profile is `exp(-c0 t) * g k ^ κ₀`.  The metric decay is
kept in `B.profile (dist Y)` and then compared with the caller's raw weight
`w Y`; the theorem therefore does not assert any new source or analytic
estimate. -/
theorem rawYMActivityDecay_of_source_and_defects {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ) (w : ι → ℝ)
    (Hym Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) (c0 κ₀ : ℝ)
    (hscale :
      ∀ t k : ℕ, 0 ≤ Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀)
    (hprofile_le : ∀ Y, B.profile (dist Y) ≤ w Y)
    (hdecomp :
      ∀ t k Y,
        Hym t k Y = Hsource t k Y + Dcov t k Y + Ddict t k Y +
          Dsupport t k Y + Djac t k Y)
    (hsource :
      ∀ t k Y,
        ‖Hsource t k Y‖ ≤
          B.sourceAmp * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            Real.exp (-(B.sourceEta * (dist Y : ℝ))))
    (hcov :
      ∀ t k Y,
        ‖Dcov t k Y‖ ≤
          B.covarianceDefectAmp *
            (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
              Real.exp (-(B.covarianceEta * (dist Y : ℝ))))
    (hdict :
      ∀ t k Y,
        ‖Ddict t k Y‖ ≤
          B.dictionaryDefectAmp *
            (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
              Real.exp (-(B.dictionaryEta * (dist Y : ℝ))))
    (hsupport :
      ∀ t k Y,
        ‖Dsupport t k Y‖ ≤
          B.supportDefectAmp *
            (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
              Real.exp (-(B.supportEta * (dist Y : ℝ))))
    (hjac :
      ∀ t k Y,
        ‖Djac t k Y‖ ≤
          B.jacobianDefectAmp *
            (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
              Real.exp (-(B.jacobianEta * (dist Y : ℝ)))) :
    RawYMActivityDecay Hym w g B.totalAmp c0 κ₀ := by
  intro t k Y
  let scale : ℕ × ℕ → ℝ :=
    fun tk => Real.exp (-(c0 * (tk.1 : ℝ))) * g tk.2 ^ κ₀
  have hbudget :
      ‖Hym t k Y‖ ≤ B.totalAmp *
          (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            B.profile (dist Y) := by
    have h :=
      B.activity_decay_with_common_scale_of_source_and_defects
        dist scale
        (fun tk Y => Hym tk.1 tk.2 Y)
        (fun tk Y => Hsource tk.1 tk.2 Y)
        (fun tk Y => Dcov tk.1 tk.2 Y)
        (fun tk Y => Ddict tk.1 tk.2 Y)
        (fun tk Y => Dsupport tk.1 tk.2 Y)
        (fun tk Y => Djac tk.1 tk.2 Y)
        (fun tk => hscale tk.1 tk.2)
        (fun tk Y => hdecomp tk.1 tk.2 Y)
        (fun tk Y => hsource tk.1 tk.2 Y)
        (fun tk Y => hcov tk.1 tk.2 Y)
        (fun tk Y => hdict tk.1 tk.2 Y)
        (fun tk Y => hsupport tk.1 tk.2 Y)
        (fun tk Y => hjac tk.1 tk.2 Y)
        (t, k) Y
    simpa [scale] using h
  have hweight :
      B.totalAmp * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
          B.profile (dist Y)
        ≤
      B.totalAmp * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) * w Y := by
    exact mul_le_mul_of_nonneg_left (hprofile_le Y)
      (mul_nonneg B.totalAmp_nonneg (hscale t k))
  calc
    |Hym t k Y| = ‖Hym t k Y‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ B.totalAmp * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
          B.profile (dist Y) := hbudget
    _ ≤ B.totalAmp * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) * w Y :=
        hweight
    _ = B.totalAmp * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀ * w Y := by
        ring

end YMActivityErrorBudget

end YangMills.RG
