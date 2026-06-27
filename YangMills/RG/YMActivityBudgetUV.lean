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

/-- Named raw Yang--Mills activity decomposition consumed by the activity-budget
UV adapter.

The record is intentionally only a packaging boundary.  It stores the exact
decomposition of a raw activity into a source-shaped term plus covariance,
dictionary, support, and Jacobian defects, together with the five component
decay estimates and the metric-profile comparison to the caller's raw weight.
It does not prove any of those estimates. -/
structure RawYMActivityDecomposition {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ) (w : ι → ℝ)
    (Hym Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) (c0 κ₀ : ℝ) : Prop where
  scale_nonneg :
    ∀ t k : ℕ, 0 ≤ Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀
  profile_le_weight :
    ∀ Y, B.profile (dist Y) ≤ w Y
  decomposes :
    ∀ t k Y,
      Hym t k Y = Hsource t k Y + Dcov t k Y + Ddict t k Y +
        Dsupport t k Y + Djac t k Y
  source_bound :
    ∀ t k Y,
      ‖Hsource t k Y‖ ≤
        B.sourceAmp * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
          Real.exp (-(B.sourceEta * (dist Y : ℝ)))
  covariance_defect_bound :
    ∀ t k Y,
      ‖Dcov t k Y‖ ≤
        B.covarianceDefectAmp *
          (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            Real.exp (-(B.covarianceEta * (dist Y : ℝ)))
  dictionary_defect_bound :
    ∀ t k Y,
      ‖Ddict t k Y‖ ≤
        B.dictionaryDefectAmp *
          (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            Real.exp (-(B.dictionaryEta * (dist Y : ℝ)))
  support_defect_bound :
    ∀ t k Y,
      ‖Dsupport t k Y‖ ≤
        B.supportDefectAmp *
          (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            Real.exp (-(B.supportEta * (dist Y : ℝ)))
  jacobian_defect_bound :
    ∀ t k Y,
      ‖Djac t k Y‖ ≤
        B.jacobianDefectAmp *
          (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            Real.exp (-(B.jacobianEta * (dist Y : ℝ)))

/-- The common UV scale is nonnegative when the coupling profile is
nonnegative.  This supplies the bookkeeping field of
`RawYMActivityDecomposition` without introducing any component estimate. -/
theorem rawYMActivityScale_nonneg (g : ℕ → ℝ) (c0 κ₀ : ℝ)
    (hg : ∀ k, 0 ≤ g k) :
    ∀ t k : ℕ, 0 ≤ Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀ := by
  intro t k
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hg k) κ₀)

/-- Constructor for the named raw activity decomposition when nonnegativity of
the shared UV scale comes from the coupling profile.  The analytic component
bounds and the exact source-plus-defects decomposition remain explicit. -/
theorem RawYMActivityDecomposition.of_components {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ) (w : ι → ℝ)
    (Hym Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) (c0 κ₀ : ℝ)
    (hg : ∀ k, 0 ≤ g k)
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
    RawYMActivityDecomposition B dist w Hym Hsource Dcov Ddict Dsupport
      Djac g c0 κ₀ where
  scale_nonneg := rawYMActivityScale_nonneg g c0 κ₀ hg
  profile_le_weight := hprofile_le
  decomposes := hdecomp
  source_bound := hsource
  covariance_defect_bound := hcov
  dictionary_defect_bound := hdict
  support_defect_bound := hsupport
  jacobian_defect_bound := hjac

/-- Canonical constructor for the exact raw sum over the five component
channels, using the budget profile itself as the raw weight.

This discharges only definitional bookkeeping: the raw activity is definitionally
the source term plus the four defect terms, and the profile-to-weight comparison
is reflexive.  The five analytic component estimates remain explicit. -/
theorem RawYMActivityDecomposition.of_sum_components_profile {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ)
    (Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) (c0 κ₀ : ℝ)
    (hg : ∀ k, 0 ≤ g k)
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
    RawYMActivityDecomposition B dist (fun Y => B.profile (dist Y))
      (fun t k Y => Hsource t k Y + Dcov t k Y + Ddict t k Y +
        Dsupport t k Y + Djac t k Y)
      Hsource Dcov Ddict Dsupport Djac g c0 κ₀ where
  scale_nonneg := rawYMActivityScale_nonneg g c0 κ₀ hg
  profile_le_weight := fun _ => le_rfl
  decomposes := by
    intro t k Y
    rfl
  source_bound := hsource
  covariance_defect_bound := hcov
  dictionary_defect_bound := hdict
  support_defect_bound := hsupport
  jacobian_defect_bound := hjac

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

/-- Projection from the named raw activity decomposition record to the existing
`RawYMActivityDecay` predicate. -/
theorem RawYMActivityDecomposition.rawYMActivityDecay {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ) (w : ι → ℝ)
    (Hym Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) (c0 κ₀ : ℝ)
    (D : RawYMActivityDecomposition B dist w Hym Hsource Dcov Ddict Dsupport
      Djac g c0 κ₀) :
    RawYMActivityDecay Hym w g B.totalAmp c0 κ₀ :=
  rawYMActivityDecay_of_source_and_defects B dist w
    Hym Hsource Dcov Ddict Dsupport Djac g c0 κ₀
    D.scale_nonneg D.profile_le_weight D.decomposes D.source_bound
    D.covariance_defect_bound D.dictionary_defect_bound D.support_defect_bound
    D.jacobian_defect_bound

/-- Canonical exact-sum/profile route to the existing `RawYMActivityDecay`
predicate.

This composes `RawYMActivityDecomposition.of_sum_components_profile` with the
record projection.  It still assumes all five component estimates explicitly. -/
theorem rawYMActivityDecay_of_sum_components_profile {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ)
    (Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) (c0 κ₀ : ℝ)
    (hg : ∀ k, 0 ≤ g k)
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
    RawYMActivityDecay
      (fun t k Y => Hsource t k Y + Dcov t k Y + Ddict t k Y +
        Dsupport t k Y + Djac t k Y)
      (fun Y => B.profile (dist Y)) g B.totalAmp c0 κ₀ :=
  (RawYMActivityDecomposition.of_sum_components_profile B dist Hsource Dcov
      Ddict Dsupport Djac g c0 κ₀ hg hsource hcov hdict hsupport hjac)
    |>.rawYMActivityDecay B dist (fun Y => B.profile (dist Y))
      (fun t k Y => Hsource t k Y + Dcov t k Y + Ddict t k Y +
        Dsupport t k Y + Djac t k Y)
      Hsource Dcov Ddict Dsupport Djac g c0 κ₀

/-- A direct raw-activity scalar sum feeds the `SingleScaleUVDecay` consumer.

This is only the direct-sum case: the exact identity `Rsc = tsum Hraw`,
absolute summability, and the weight-sum bound are all explicit hypotheses.
It does not replace the Appendix-F/H# renormalization step, where the scalar
remainder is a sum of renormalized with-holes activities. -/
theorem singleScaleUVDecay_of_rawYMActivityDecay {ι : Type*}
    (Rsc : ℕ → ℕ → ℝ) (Hraw : ℕ → ℕ → ι → ℝ) (w : ι → ℝ) (g : ℕ → ℝ)
    {A K₀ c0 κ₀ : ℝ}
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hraw t k Y)
    (hHsummable : ∀ t k, Summable (fun Y => |Hraw t k Y|))
    (hraw : RawYMActivityDecay Hraw w g A c0 κ₀)
    (hwsum : Summable w) (hwK : ∑' Y, w Y ≤ K₀) :
    SingleScaleUVDecay Rsc g (A * K₀) c0 κ₀ := by
  have hren :
      RenormalizedHoleActivityDecay Hraw w g A c0 κ₀ := by
    intro t k Y
    exact hraw t k Y
  exact
    singleScaleUVDecay_of_renormalizedHoleActivities
      Rsc Hraw w g hA hg hR hHsummable hren hwsum hwK

/-- Projection from a named raw activity decomposition record to the scalar UV
consumer in the direct raw-sum case. -/
theorem RawYMActivityDecomposition.singleScaleUVDecay_of_tsum {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ) (w : ι → ℝ)
    (Rsc : ℕ → ℕ → ℝ)
    (Hym Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) (c0 κ₀ K₀ : ℝ)
    (D : RawYMActivityDecomposition B dist w Hym Hsource Dcov Ddict Dsupport
      Djac g c0 κ₀)
    (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hym t k Y)
    (hHsummable : ∀ t k, Summable (fun Y => |Hym t k Y|))
    (hwsum : Summable w) (hwK : ∑' Y, w Y ≤ K₀) :
    SingleScaleUVDecay Rsc g (B.totalAmp * K₀) c0 κ₀ :=
  singleScaleUVDecay_of_rawYMActivityDecay Rsc Hym w g
    B.totalAmp_nonneg hg hR hHsummable
    (D.rawYMActivityDecay B dist w Hym Hsource Dcov Ddict Dsupport Djac
      g c0 κ₀)
    hwsum hwK

/-- Canonical exact-sum/profile route to the scalar UV consumer in the direct
raw-sum case.

The scalar identity, absolute summability, and profile summability/bound remain
explicit hypotheses.  This does not replace any Appendix-F/H# renormalized
activity estimate. -/
theorem singleScaleUVDecay_of_sum_components_profile_tsum {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ)
    (Rsc : ℕ → ℕ → ℝ)
    (Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) (c0 κ₀ K₀ : ℝ)
    (hg : ∀ k, 0 ≤ g k)
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
              Real.exp (-(B.jacobianEta * (dist Y : ℝ))))
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' (Y : ι), (Hsource t k Y + Dcov t k Y + Ddict t k Y +
            Dsupport t k Y + Djac t k Y))
    (hHsummable :
      ∀ t k,
        Summable (fun Y : ι =>
          |Hsource t k Y + Dcov t k Y + Ddict t k Y +
            Dsupport t k Y + Djac t k Y|))
    (hwsum : Summable (fun Y : ι => B.profile (dist Y)))
    (hwK : ∑' (Y : ι), B.profile (dist Y) ≤ K₀) :
    SingleScaleUVDecay Rsc g (B.totalAmp * K₀) c0 κ₀ :=
  singleScaleUVDecay_of_rawYMActivityDecay Rsc
    (fun t k Y => Hsource t k Y + Dcov t k Y + Ddict t k Y +
      Dsupport t k Y + Djac t k Y)
    (fun Y => B.profile (dist Y)) g
    B.totalAmp_nonneg hg hR hHsummable
    (rawYMActivityDecay_of_sum_components_profile B dist Hsource Dcov Ddict
      Dsupport Djac g c0 κ₀ hg hsource hcov hdict hsupport hjac)
    hwsum hwK

end YMActivityErrorBudget

end YangMills.RG
