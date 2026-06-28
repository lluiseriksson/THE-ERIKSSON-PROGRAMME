/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.SingleScaleUVDecay
import YangMills.RG.YMActivityBudget
import YangMills.RG.MarginalUVMassGap

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

/-- The raw weight in a decomposition record is nonnegative.  This is not an
extra analytic input: it follows because the record compares the strictly
positive budget profile to the caller's weight. -/
theorem RawYMActivityDecomposition.weight_nonneg {ι : Type*}
    {B : YMActivityErrorBudget} {dist : ι → ℕ} {w : ι → ℝ}
    {Hym Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ}
    {g : ℕ → ℝ} {c0 κ₀ : ℝ}
    (D : RawYMActivityDecomposition B dist w Hym Hsource Dcov Ddict
      Dsupport Djac g c0 κ₀) :
    ∀ Y, 0 ≤ w Y := by
  intro Y
  exact (le_of_lt (B.profile_pos (dist Y))).trans (D.profile_le_weight Y)

/-- The total raw-weight mass is nonnegative for any decomposition record. -/
theorem RawYMActivityDecomposition.weight_tsum_nonneg {ι : Type*}
    {B : YMActivityErrorBudget} {dist : ι → ℕ} {w : ι → ℝ}
    {Hym Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ}
    {g : ℕ → ℝ} {c0 κ₀ : ℝ}
    (D : RawYMActivityDecomposition B dist w Hym Hsource Dcov Ddict
      Dsupport Djac g c0 κ₀) :
    0 ≤ ∑' Y, w Y := by
  exact tsum_nonneg D.weight_nonneg

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

/-- Absolute summability of a raw activity follows from its pointwise decay
against a summable raw weight.

This discharges only the summability side condition used by the scalar UV
consumer.  It does not prove the pointwise raw decay or the weight-sum bound. -/
theorem summable_abs_of_rawYMActivityDecay {ι : Type*}
    (Hraw : ℕ → ℕ → ι → ℝ) (w : ι → ℝ) (g : ℕ → ℝ)
    {A c0 κ₀ : ℝ}
    (hraw : RawYMActivityDecay Hraw w g A c0 κ₀)
    (hwsum : Summable w) :
    ∀ t k, Summable (fun Y => |Hraw t k Y|) := by
  intro t k
  have hmajor :
      Summable
        (fun Y => (A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) * w Y) :=
    hwsum.mul_left _
  exact hmajor.of_nonneg_of_le
    (fun Y => abs_nonneg (Hraw t k Y))
    (fun Y => by
      have hY := hraw t k Y
      simpa [mul_assoc] using hY)

/-- Finite-carrier absolute summability for a raw activity decay estimate.

This is the finite-volume specialization of
`summable_abs_of_rawYMActivityDecay`: no separate raw-weight summability
hypothesis is needed when the activity carrier is finite. -/
theorem summable_abs_of_rawYMActivityDecay_fintype {ι : Type*} [Fintype ι]
    (Hraw : ℕ → ℕ → ι → ℝ) (w : ι → ℝ) (g : ℕ → ℝ)
    {A c0 κ₀ : ℝ}
    (hraw : RawYMActivityDecay Hraw w g A c0 κ₀) :
    ∀ t k, Summable (fun Y => |Hraw t k Y|) :=
  summable_abs_of_rawYMActivityDecay Hraw w g hraw Summable.of_finite

/-- Direct raw-activity scalar UV consumer with absolute summability derived
from the same pointwise raw decay and summable raw weight.

The exact scalar identity `Rsc = tsum Hraw`, weight summability, and weight-sum
bound remain explicit hypotheses. -/
theorem singleScaleUVDecay_of_rawYMActivityDecay_summableWeight {ι : Type*}
    (Rsc : ℕ → ℕ → ℝ) (Hraw : ℕ → ℕ → ι → ℝ) (w : ι → ℝ) (g : ℕ → ℝ)
    {A K₀ c0 κ₀ : ℝ}
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hraw t k Y)
    (hraw : RawYMActivityDecay Hraw w g A c0 κ₀)
    (hwsum : Summable w) (hwK : ∑' Y, w Y ≤ K₀) :
    SingleScaleUVDecay Rsc g (A * K₀) c0 κ₀ :=
  singleScaleUVDecay_of_rawYMActivityDecay Rsc Hraw w g
    hA hg hR (summable_abs_of_rawYMActivityDecay Hraw w g hraw hwsum)
    hraw hwsum hwK

/-- Finite-carrier direct raw-activity scalar UV consumer.

For finite-volume raw activity carriers, the raw weight is automatically
summable and the bookkeeping constant can be the finite raw-weight sum.  The
exact scalar identity and the pointwise `RawYMActivityDecay` estimate remain
explicit. -/
theorem singleScaleUVDecay_of_rawYMActivityDecay_fintype {ι : Type*}
    [Fintype ι]
    (Rsc : ℕ → ℕ → ℝ) (Hraw : ℕ → ℕ → ι → ℝ) (w : ι → ℝ) (g : ℕ → ℝ)
    {A c0 κ₀ : ℝ}
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hraw t k Y)
    (hraw : RawYMActivityDecay Hraw w g A c0 κ₀) :
    SingleScaleUVDecay Rsc g (A * ∑ Y : ι, w Y) c0 κ₀ := by
  exact
    singleScaleUVDecay_of_rawYMActivityDecay_summableWeight
      Rsc Hraw w g hA hg hR hraw
      Summable.of_finite
      (by simp [tsum_fintype])

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

/-- Projection from a named raw activity decomposition record to the scalar UV
consumer, deriving absolute summability from the record's raw decay estimate
and the summable raw weight. -/
theorem RawYMActivityDecomposition.singleScaleUVDecay_of_tsum_summableWeight
    {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ) (w : ι → ℝ)
    (Rsc : ℕ → ℕ → ℝ)
    (Hym Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) (c0 κ₀ K₀ : ℝ)
    (D : RawYMActivityDecomposition B dist w Hym Hsource Dcov Ddict Dsupport
      Djac g c0 κ₀)
    (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hym t k Y)
    (hwsum : Summable w) (hwK : ∑' Y, w Y ≤ K₀) :
    SingleScaleUVDecay Rsc g (B.totalAmp * K₀) c0 κ₀ :=
  singleScaleUVDecay_of_rawYMActivityDecay_summableWeight Rsc Hym w g
    B.totalAmp_nonneg hg hR
    (D.rawYMActivityDecay B dist w Hym Hsource Dcov Ddict Dsupport Djac
      g c0 κ₀)
    hwsum hwK

/-- Finite-carrier projection from a named raw activity decomposition to the
scalar UV consumer.

For finite-volume raw decompositions, the raw weight is automatically summable
and the scalar bookkeeping constant can be the finite raw-weight sum.  The
record still carries the exact source-plus-defects decomposition and all
component estimates. -/
theorem RawYMActivityDecomposition.singleScaleUVDecay_of_tsum_fintype
    {ι : Type*} [Fintype ι]
    (B : YMActivityErrorBudget) (dist : ι → ℕ) (w : ι → ℝ)
    (Rsc : ℕ → ℕ → ℝ)
    (Hym Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) (c0 κ₀ : ℝ)
    (D : RawYMActivityDecomposition B dist w Hym Hsource Dcov Ddict Dsupport
      Djac g c0 κ₀)
    (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hym t k Y) :
    SingleScaleUVDecay Rsc g (B.totalAmp * ∑ Y : ι, w Y) c0 κ₀ := by
  exact
    RawYMActivityDecomposition.singleScaleUVDecay_of_tsum_summableWeight
      B dist w Rsc Hym Hsource Dcov Ddict Dsupport Djac
      g c0 κ₀ (∑ Y : ι, w Y) D hg hR
      Summable.of_finite
      (by simp [tsum_fintype])

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

/-- Canonical exact-sum/profile scalar UV route with absolute summability
derived from the canonical raw decay estimate and profile summability.

The scalar identity and profile-sum bound remain explicit hypotheses. -/
theorem singleScaleUVDecay_of_sum_components_profile_tsum_summableWeight
    {ι : Type*}
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
    (hwsum : Summable (fun Y : ι => B.profile (dist Y)))
    (hwK : ∑' (Y : ι), B.profile (dist Y) ≤ K₀) :
    SingleScaleUVDecay Rsc g (B.totalAmp * K₀) c0 κ₀ :=
  singleScaleUVDecay_of_rawYMActivityDecay_summableWeight Rsc
    (fun t k Y => Hsource t k Y + Dcov t k Y + Ddict t k Y +
      Dsupport t k Y + Djac t k Y)
    (fun Y => B.profile (dist Y)) g
    B.totalAmp_nonneg hg hR
    (rawYMActivityDecay_of_sum_components_profile B dist Hsource Dcov Ddict
      Dsupport Djac g c0 κ₀ hg hsource hcov hdict hsupport hjac)
    hwsum hwK

/-- Finite-carrier exact-sum/profile scalar UV route.

For finite-volume activity carriers the profile weight is automatically
summable and the best bookkeeping constant is its finite sum.  This lemma
removes the explicit `Summable`/`tsum ≤ K₀` side conditions from the canonical
profile route; it still assumes all five component estimates and the exact
scalar decomposition. -/
theorem singleScaleUVDecay_of_sum_components_profile_fintype {ι : Type*}
    [Fintype ι]
    (B : YMActivityErrorBudget) (dist : ι → ℕ)
    (Rsc : ℕ → ℕ → ℝ)
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
              Real.exp (-(B.jacobianEta * (dist Y : ℝ))))
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' (Y : ι), (Hsource t k Y + Dcov t k Y + Ddict t k Y +
            Dsupport t k Y + Djac t k Y)) :
    SingleScaleUVDecay Rsc g
      (B.totalAmp * ∑ Y : ι, B.profile (dist Y)) c0 κ₀ := by
  exact
    singleScaleUVDecay_of_sum_components_profile_tsum_summableWeight
      B dist Rsc Hsource Dcov Ddict Dsupport Djac
      g c0 κ₀ (∑ Y : ι, B.profile (dist Y)) hg
      hsource hcov hdict hsupport hjac hR
      Summable.of_finite
      (by simp [tsum_fintype])

/-- End-to-end marginal-coupling mass-gap assembly from a named raw
source-plus-defects activity decomposition.

This is only theorem composition: the decomposition record supplies the
single-scale UV predicate through
`RawYMActivityDecomposition.singleScaleUVDecay_of_tsum_summableWeight`, and
the existing marginal-coupling consumer performs the scale summation.  The
exact scalar identity, raw-weight summability, weight-sum bound, IR estimate,
and marginal coupling hypotheses remain explicit. -/
theorem RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_summableWeight
    {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ) (w : ι → ℝ)
    (covIR : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ)
    (Hym Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) {C1 ε c0 β κ₀ K₀ : ℝ}
    (D : RawYMActivityDecomposition B dist w Hym Hsource Dcov Ddict
      Dsupport Djac g c0 κ₀)
    (hK₀ : 0 ≤ K₀)
    (hε : 0 < ε) (hc0 : 0 < c0) (hκ : 1 < κ₀)
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k)
    (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k))
    (hIRbound :
      ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
    (hR : ∀ t k, Rsc t k = ∑' Y, Hym t k Y)
    (hwsum : Summable w) (hwK : ∑' Y, w Y ≤ K₀) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t|
        ≤ (C1 + (B.totalAmp * K₀) * ∑' k, g k ^ κ₀) *
            Real.exp (-(gap * (t : ℝ))) := by
  exact
    lattice_mass_gap_of_singleScaleUVDecay_marginal
      covIR Rsc nsc g
      (C2 := B.totalAmp * K₀)
      hε hc0
      (mul_nonneg B.totalAmp_nonneg hK₀)
      hκ hβ hpos hsmall hrec hIRbound
      (RawYMActivityDecomposition.singleScaleUVDecay_of_tsum_summableWeight
        B dist w Rsc Hym Hsource Dcov Ddict Dsupport Djac
        g c0 κ₀ K₀ D (fun k => (hpos k).le) hR hwsum hwK)

/-- Same marginal-coupling assembly as
`RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_summableWeight`,
but the scalar side condition `0 ≤ K₀` is derived from the decomposition
record and the weight-sum bound. -/
theorem RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_summableWeight_of_bound
    {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ) (w : ι → ℝ)
    (covIR : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ)
    (Hym Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) {C1 ε c0 β κ₀ K₀ : ℝ}
    (D : RawYMActivityDecomposition B dist w Hym Hsource Dcov Ddict
      Dsupport Djac g c0 κ₀)
    (hε : 0 < ε) (hc0 : 0 < c0) (hκ : 1 < κ₀)
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k)
    (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k))
    (hIRbound :
      ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
    (hR : ∀ t k, Rsc t k = ∑' Y, Hym t k Y)
    (hwsum : Summable w) (hwK : ∑' Y, w Y ≤ K₀) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t|
        ≤ (C1 + (B.totalAmp * K₀) * ∑' k, g k ^ κ₀) *
            Real.exp (-(gap * (t : ℝ))) := by
  have hK₀ : 0 ≤ K₀ := D.weight_tsum_nonneg.trans hwK
  exact
    RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_summableWeight
      B dist w covIR Rsc nsc Hym Hsource Dcov Ddict Dsupport Djac g
      D hK₀ hε hc0 hκ hβ hpos hsmall hrec hIRbound hR hwsum hwK

/-- Finite-carrier marginal-coupling assembly from a named raw activity
decomposition.

This is the record-level finite-volume version of
`RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_summableWeight`.
The finite raw-weight sum supplies the scalar UV amplitude, while the
decomposition record supplies raw-weight nonnegativity. -/
theorem RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_fintype
    {ι : Type*} [Fintype ι]
    (B : YMActivityErrorBudget) (dist : ι → ℕ) (w : ι → ℝ)
    (covIR : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ)
    (Hym Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) {C1 ε c0 β κ₀ : ℝ}
    (D : RawYMActivityDecomposition B dist w Hym Hsource Dcov Ddict
      Dsupport Djac g c0 κ₀)
    (hε : 0 < ε) (hc0 : 0 < c0) (hκ : 1 < κ₀)
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k)
    (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k))
    (hIRbound :
      ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
    (hR : ∀ t k, Rsc t k = ∑' Y, Hym t k Y) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t|
        ≤ (C1 + (B.totalAmp * ∑ Y : ι, w Y) * ∑' k, g k ^ κ₀) *
            Real.exp (-(gap * (t : ℝ))) := by
  have hK₀ : 0 ≤ ∑ Y : ι, w Y := by
    exact Finset.sum_nonneg fun Y _ => D.weight_nonneg Y
  exact
    RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_summableWeight
      B dist w covIR Rsc nsc Hym Hsource Dcov Ddict Dsupport Djac g
      D hK₀ hε hc0 hκ hβ hpos hsmall hrec hIRbound hR
      Summable.of_finite
      (by simp [tsum_fintype])

/-- Canonical exact-sum/profile route from five source/defect component
estimates directly to the marginal-coupling mass-gap assembly.

This is the profile-weight specialization of
`RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_summableWeight`.
It discharges only bookkeeping: the raw activity is definitionally the sum of
the five channels and the raw weight is `B.profile (dist Y)`.  Component
estimates, the scalar identity, profile summability, profile-sum bound, IR
estimate, and marginal coupling hypotheses are still supplied by the caller. -/
theorem lattice_mass_gap_marginal_of_sum_components_profile_tsum_summableWeight
    {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ)
    (covIR : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ)
    (Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) {C1 ε c0 β κ₀ K₀ : ℝ}
    (hK₀ : 0 ≤ K₀)
    (hε : 0 < ε) (hc0 : 0 < c0) (hκ : 1 < κ₀)
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k)
    (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k))
    (hIRbound :
      ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
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
    (hwsum : Summable (fun Y : ι => B.profile (dist Y)))
    (hwK : ∑' (Y : ι), B.profile (dist Y) ≤ K₀) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t|
        ≤ (C1 + (B.totalAmp * K₀) * ∑' k, g k ^ κ₀) *
            Real.exp (-(gap * (t : ℝ))) := by
  exact
    lattice_mass_gap_of_singleScaleUVDecay_marginal
      covIR Rsc nsc g
      (C2 := B.totalAmp * K₀)
      hε hc0
      (mul_nonneg B.totalAmp_nonneg hK₀)
      hκ hβ hpos hsmall hrec hIRbound
      (singleScaleUVDecay_of_sum_components_profile_tsum_summableWeight
        B dist Rsc Hsource Dcov Ddict Dsupport Djac
        g c0 κ₀ K₀ (fun k => (hpos k).le)
        hsource hcov hdict hsupport hjac hR hwsum hwK)

/-- Same canonical exact-sum/profile marginal assembly, deriving `0 ≤ K₀`
from the nonnegative profile and the supplied profile-sum bound. -/
theorem lattice_mass_gap_marginal_of_sum_components_profile_tsum_summableWeight_of_bound
    {ι : Type*}
    (B : YMActivityErrorBudget) (dist : ι → ℕ)
    (covIR : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ)
    (Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) {C1 ε c0 β κ₀ K₀ : ℝ}
    (hε : 0 < ε) (hc0 : 0 < c0) (hκ : 1 < κ₀)
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k)
    (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k))
    (hIRbound :
      ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
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
    (hwsum : Summable (fun Y : ι => B.profile (dist Y)))
    (hwK : ∑' (Y : ι), B.profile (dist Y) ≤ K₀) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t|
        ≤ (C1 + (B.totalAmp * K₀) * ∑' k, g k ^ κ₀) *
            Real.exp (-(gap * (t : ℝ))) := by
  have hK₀ : 0 ≤ K₀ := by
    exact (tsum_nonneg fun Y => (B.profile_pos (dist Y)).le).trans hwK
  exact
    lattice_mass_gap_marginal_of_sum_components_profile_tsum_summableWeight
      B dist covIR Rsc nsc Hsource Dcov Ddict Dsupport Djac g
      hK₀ hε hc0 hκ hβ hpos hsmall hrec hIRbound
      hsource hcov hdict hsupport hjac hR hwsum hwK

/-- Finite-carrier exact-sum/profile marginal assembly.

This specializes the canonical source-plus-defects marginal route to finite
activity carriers.  The profile summability and profile-sum bound are
discharged by finiteness, leaving the component estimates, exact scalar
identity, IR estimate, and marginal coupling hypotheses explicit. -/
theorem lattice_mass_gap_marginal_of_sum_components_profile_fintype
    {ι : Type*} [Fintype ι]
    (B : YMActivityErrorBudget) (dist : ι → ℕ)
    (covIR : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ)
    (Hsource Dcov Ddict Dsupport Djac : ℕ → ℕ → ι → ℝ)
    (g : ℕ → ℝ) {C1 ε c0 β κ₀ : ℝ}
    (hε : 0 < ε) (hc0 : 0 < c0) (hκ : 1 < κ₀)
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k)
    (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k))
    (hIRbound :
      ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
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
            Dsupport t k Y + Djac t k Y)) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t|
        ≤ (C1 + (B.totalAmp * ∑ Y : ι, B.profile (dist Y)) *
              ∑' k, g k ^ κ₀) *
            Real.exp (-(gap * (t : ℝ))) := by
  have hK₀ : 0 ≤ ∑ Y : ι, B.profile (dist Y) := by
    exact Finset.sum_nonneg fun Y _ => (B.profile_pos (dist Y)).le
  exact
    lattice_mass_gap_marginal_of_sum_components_profile_tsum_summableWeight
      B dist covIR Rsc nsc Hsource Dcov Ddict Dsupport Djac g
      hK₀ hε hc0 hκ hβ hpos hsmall hrec hIRbound
      hsource hcov hdict hsupport hjac hR
      Summable.of_finite
      (by simp [tsum_fintype])

end YMActivityErrorBudget

end YangMills.RG
