/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib

/-!
# Yang--Mills activity error budgets

This file isolates a source-independent bookkeeping pattern for the `hRpoly`
frontier.  A physical Yang--Mills activity can be compared to a source-shaped
activity plus named covariance, dictionary, support, and Jacobian defects; if
each component has exponential decay, then the whole activity has exponential
decay with the summed amplitude and the minimum decay rate.

Honest scope: this proves no covariance-root localization, Gaussian
pushforward, Wilson-Hessian identification, source dictionary, Ward
cancellation, Eq. (2.31), Appendix F, `hRpoly`, continuum limit, or Clay
statement.  It is only the finite triangle-inequality landing pad for those
future estimates.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

/-- Scalar bookkeeping for a five-part activity comparison:

* source-shaped activity,
* covariance/root defect,
* dictionary or coordinate-identification defect,
* support/locality defect,
* Jacobian/normalization defect.

The amplitudes are nonnegative and each component carries a positive decay
rate.  `minEta` is the common decay rate that can be safely exposed to a
consumer after all five bounds are combined. -/
structure YMActivityErrorBudget where
  sourceAmp : ℝ
  covarianceDefectAmp : ℝ
  dictionaryDefectAmp : ℝ
  supportDefectAmp : ℝ
  jacobianDefectAmp : ℝ
  sourceEta : ℝ
  covarianceEta : ℝ
  dictionaryEta : ℝ
  supportEta : ℝ
  jacobianEta : ℝ
  sourceAmp_nonneg : 0 ≤ sourceAmp
  covarianceDefectAmp_nonneg : 0 ≤ covarianceDefectAmp
  dictionaryDefectAmp_nonneg : 0 ≤ dictionaryDefectAmp
  supportDefectAmp_nonneg : 0 ≤ supportDefectAmp
  jacobianDefectAmp_nonneg : 0 ≤ jacobianDefectAmp
  sourceEta_pos : 0 < sourceEta
  covarianceEta_pos : 0 < covarianceEta
  dictionaryEta_pos : 0 < dictionaryEta
  supportEta_pos : 0 < supportEta
  jacobianEta_pos : 0 < jacobianEta

namespace YMActivityErrorBudget

/-- Total amplitude after adding the source contribution and all named
defects. -/
noncomputable def totalAmp (B : YMActivityErrorBudget) : ℝ :=
  B.sourceAmp + B.covarianceDefectAmp + B.dictionaryDefectAmp +
    B.supportDefectAmp + B.jacobianDefectAmp

/-- Minimum decay rate among the source term and four defect terms. -/
noncomputable def minEta (B : YMActivityErrorBudget) : ℝ :=
  min B.sourceEta
    (min B.covarianceEta
      (min B.dictionaryEta (min B.supportEta B.jacobianEta)))

theorem totalAmp_nonneg (B : YMActivityErrorBudget) : 0 ≤ B.totalAmp := by
  dsimp [totalAmp]
  nlinarith [B.sourceAmp_nonneg, B.covarianceDefectAmp_nonneg,
    B.dictionaryDefectAmp_nonneg, B.supportDefectAmp_nonneg,
    B.jacobianDefectAmp_nonneg]

theorem minEta_pos (B : YMActivityErrorBudget) : 0 < B.minEta := by
  dsimp [minEta]
  exact lt_min B.sourceEta_pos
    (lt_min B.covarianceEta_pos
      (lt_min B.dictionaryEta_pos
        (lt_min B.supportEta_pos B.jacobianEta_pos)))

theorem minEta_le_sourceEta (B : YMActivityErrorBudget) :
    B.minEta ≤ B.sourceEta := by
  dsimp [minEta]
  exact min_le_left _ _

theorem minEta_le_covarianceEta (B : YMActivityErrorBudget) :
    B.minEta ≤ B.covarianceEta := by
  dsimp [minEta]
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem minEta_le_dictionaryEta (B : YMActivityErrorBudget) :
    B.minEta ≤ B.dictionaryEta := by
  dsimp [minEta]
  exact ((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_left _ _)

theorem minEta_le_supportEta (B : YMActivityErrorBudget) :
    B.minEta ≤ B.supportEta := by
  dsimp [minEta]
  exact (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)

theorem minEta_le_jacobianEta (B : YMActivityErrorBudget) :
    B.minEta ≤ B.jacobianEta := by
  dsimp [minEta]
  exact (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)

/-- The common exponential profile associated to the minimum decay rate. -/
noncomputable def profile (B : YMActivityErrorBudget) (n : ℕ) : ℝ :=
  Real.exp (-(B.minEta * (n : ℝ)))

theorem profile_pos (B : YMActivityErrorBudget) (n : ℕ) :
    0 < B.profile n := by
  exact Real.exp_pos _

/-- If `etaCommon ≤ eta`, then a positive exponential-decay bound with rate
`eta` is also a bound with rate `etaCommon`. -/
theorem exp_decay_mono_of_rate_le
    {amp etaCommon eta : ℝ} (hamp : 0 ≤ amp) (heta : etaCommon ≤ eta)
    (n : ℕ) :
    amp * Real.exp (-(eta * (n : ℝ))) ≤
      amp * Real.exp (-(etaCommon * (n : ℝ))) := by
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hmul : etaCommon * (n : ℝ) ≤ eta * (n : ℝ) :=
    mul_le_mul_of_nonneg_right heta hn
  have hneg : -(eta * (n : ℝ)) ≤ -(etaCommon * (n : ℝ)) :=
    neg_le_neg hmul
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg) hamp

/-- Triangle inequality for a source term and four named defects. -/
theorem norm_source_add_four_defects_le
    {E : Type*} [SeminormedAddCommGroup E] (source cov dict support jac : E) :
    ‖source + cov + dict + support + jac‖ ≤
      ‖source‖ + ‖cov‖ + ‖dict‖ + ‖support‖ + ‖jac‖ := by
  calc
    ‖source + cov + dict + support + jac‖
        = ‖(((source + cov) + dict) + support) + jac‖ := by
            rfl
    _ ≤ ‖((source + cov) + dict) + support‖ + ‖jac‖ := norm_add_le _ _
    _ ≤ (‖(source + cov) + dict‖ + ‖support‖) + ‖jac‖ := by
        exact add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖source + cov‖ + ‖dict‖) + ‖support‖) + ‖jac‖ := by
        exact add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ (((‖source‖ + ‖cov‖) + ‖dict‖) + ‖support‖) + ‖jac‖ := by
        exact add_le_add
          (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl
    _ = ‖source‖ + ‖cov‖ + ‖dict‖ + ‖support‖ + ‖jac‖ := by
        ring

/-- Main activity-budget theorem.

If the physical activity is exactly a source-shaped activity plus four named
defects, and every component has an exponential decay bound with the amplitudes
and rates recorded in `B`, then the physical activity has the summed amplitude
and the minimum decay rate.

The theorem is deliberately codomain-generic: it applies to real, complex, or
other seminormed additive activity values. -/
theorem activity_decay_of_source_and_defects
    {Y E : Type*} [SeminormedAddCommGroup E]
    (B : YMActivityErrorBudget) (dist : Y → ℕ)
    (Hym Hsource Dcov Ddict Dsupport Djac : Y → E)
    (hdecomp :
      ∀ Y,
        Hym Y = Hsource Y + Dcov Y + Ddict Y + Dsupport Y + Djac Y)
    (hsource :
      ∀ Y,
        ‖Hsource Y‖ ≤
          B.sourceAmp * Real.exp (-(B.sourceEta * (dist Y : ℝ))))
    (hcov :
      ∀ Y,
        ‖Dcov Y‖ ≤
          B.covarianceDefectAmp *
            Real.exp (-(B.covarianceEta * (dist Y : ℝ))))
    (hdict :
      ∀ Y,
        ‖Ddict Y‖ ≤
          B.dictionaryDefectAmp *
            Real.exp (-(B.dictionaryEta * (dist Y : ℝ))))
    (hsupport :
      ∀ Y,
        ‖Dsupport Y‖ ≤
          B.supportDefectAmp *
            Real.exp (-(B.supportEta * (dist Y : ℝ))))
    (hjac :
      ∀ Y,
        ‖Djac Y‖ ≤
          B.jacobianDefectAmp *
            Real.exp (-(B.jacobianEta * (dist Y : ℝ)))) :
    ∀ Y,
      ‖Hym Y‖ ≤ B.totalAmp * B.profile (dist Y) := by
  intro Y
  let p := B.profile (dist Y)
  have hsource_common :
      ‖Hsource Y‖ ≤ B.sourceAmp * p := by
    exact (hsource Y).trans
      (exp_decay_mono_of_rate_le B.sourceAmp_nonneg
        (B.minEta_le_sourceEta) (dist Y))
  have hcov_common :
      ‖Dcov Y‖ ≤ B.covarianceDefectAmp * p := by
    exact (hcov Y).trans
      (exp_decay_mono_of_rate_le B.covarianceDefectAmp_nonneg
        (B.minEta_le_covarianceEta) (dist Y))
  have hdict_common :
      ‖Ddict Y‖ ≤ B.dictionaryDefectAmp * p := by
    exact (hdict Y).trans
      (exp_decay_mono_of_rate_le B.dictionaryDefectAmp_nonneg
        (B.minEta_le_dictionaryEta) (dist Y))
  have hsupport_common :
      ‖Dsupport Y‖ ≤ B.supportDefectAmp * p := by
    exact (hsupport Y).trans
      (exp_decay_mono_of_rate_le B.supportDefectAmp_nonneg
        (B.minEta_le_supportEta) (dist Y))
  have hjac_common :
      ‖Djac Y‖ ≤ B.jacobianDefectAmp * p := by
    exact (hjac Y).trans
      (exp_decay_mono_of_rate_le B.jacobianDefectAmp_nonneg
        (B.minEta_le_jacobianEta) (dist Y))
  calc
    ‖Hym Y‖
        = ‖Hsource Y + Dcov Y + Ddict Y + Dsupport Y + Djac Y‖ := by
            rw [hdecomp Y]
    _ ≤ ‖Hsource Y‖ + ‖Dcov Y‖ + ‖Ddict Y‖ + ‖Dsupport Y‖ + ‖Djac Y‖ :=
        norm_source_add_four_defects_le _ _ _ _ _
    _ ≤ B.sourceAmp * p + B.covarianceDefectAmp * p +
          B.dictionaryDefectAmp * p + B.supportDefectAmp * p +
            B.jacobianDefectAmp * p := by
        linarith [hsource_common, hcov_common, hdict_common, hsupport_common,
          hjac_common]
    _ = B.totalAmp * B.profile (dist Y) := by
        dsimp [totalAmp, p]
        ring

/-- Common-scale version of `activity_decay_of_source_and_defects`.

This is the shape used by UV estimates: the metric profile is multiplied by a
nonnegative scale factor, such as `exp(-c0 t) * g k ^ κ₀`, shared by the source
term and all defect terms. -/
theorem activity_decay_with_common_scale_of_source_and_defects
    {S Y E : Type*} [SeminormedAddCommGroup E]
    (B : YMActivityErrorBudget) (dist : Y → ℕ) (scale : S → ℝ)
    (Hym Hsource Dcov Ddict Dsupport Djac : S → Y → E)
    (hscale : ∀ s, 0 ≤ scale s)
    (hdecomp :
      ∀ s Y,
        Hym s Y = Hsource s Y + Dcov s Y + Ddict s Y +
          Dsupport s Y + Djac s Y)
    (hsource :
      ∀ s Y,
        ‖Hsource s Y‖ ≤
          B.sourceAmp * scale s *
            Real.exp (-(B.sourceEta * (dist Y : ℝ))))
    (hcov :
      ∀ s Y,
        ‖Dcov s Y‖ ≤
          B.covarianceDefectAmp * scale s *
            Real.exp (-(B.covarianceEta * (dist Y : ℝ))))
    (hdict :
      ∀ s Y,
        ‖Ddict s Y‖ ≤
          B.dictionaryDefectAmp * scale s *
            Real.exp (-(B.dictionaryEta * (dist Y : ℝ))))
    (hsupport :
      ∀ s Y,
        ‖Dsupport s Y‖ ≤
          B.supportDefectAmp * scale s *
            Real.exp (-(B.supportEta * (dist Y : ℝ))))
    (hjac :
      ∀ s Y,
        ‖Djac s Y‖ ≤
          B.jacobianDefectAmp * scale s *
            Real.exp (-(B.jacobianEta * (dist Y : ℝ)))) :
    ∀ s Y,
      ‖Hym s Y‖ ≤ B.totalAmp * scale s * B.profile (dist Y) := by
  intro s Y
  let p := B.profile (dist Y)
  have hsource_common :
      ‖Hsource s Y‖ ≤ B.sourceAmp * scale s * p := by
    exact (hsource s Y).trans
      (exp_decay_mono_of_rate_le
        (mul_nonneg B.sourceAmp_nonneg (hscale s))
        (B.minEta_le_sourceEta) (dist Y))
  have hcov_common :
      ‖Dcov s Y‖ ≤ B.covarianceDefectAmp * scale s * p := by
    exact (hcov s Y).trans
      (exp_decay_mono_of_rate_le
        (mul_nonneg B.covarianceDefectAmp_nonneg (hscale s))
        (B.minEta_le_covarianceEta) (dist Y))
  have hdict_common :
      ‖Ddict s Y‖ ≤ B.dictionaryDefectAmp * scale s * p := by
    exact (hdict s Y).trans
      (exp_decay_mono_of_rate_le
        (mul_nonneg B.dictionaryDefectAmp_nonneg (hscale s))
        (B.minEta_le_dictionaryEta) (dist Y))
  have hsupport_common :
      ‖Dsupport s Y‖ ≤ B.supportDefectAmp * scale s * p := by
    exact (hsupport s Y).trans
      (exp_decay_mono_of_rate_le
        (mul_nonneg B.supportDefectAmp_nonneg (hscale s))
        (B.minEta_le_supportEta) (dist Y))
  have hjac_common :
      ‖Djac s Y‖ ≤ B.jacobianDefectAmp * scale s * p := by
    exact (hjac s Y).trans
      (exp_decay_mono_of_rate_le
        (mul_nonneg B.jacobianDefectAmp_nonneg (hscale s))
        (B.minEta_le_jacobianEta) (dist Y))
  calc
    ‖Hym s Y‖
        = ‖Hsource s Y + Dcov s Y + Ddict s Y + Dsupport s Y +
            Djac s Y‖ := by
            rw [hdecomp s Y]
    _ ≤ ‖Hsource s Y‖ + ‖Dcov s Y‖ + ‖Ddict s Y‖ +
          ‖Dsupport s Y‖ + ‖Djac s Y‖ :=
        norm_source_add_four_defects_le _ _ _ _ _
    _ ≤ B.sourceAmp * scale s * p +
          B.covarianceDefectAmp * scale s * p +
          B.dictionaryDefectAmp * scale s * p +
          B.supportDefectAmp * scale s * p +
          B.jacobianDefectAmp * scale s * p := by
        linarith [hsource_common, hcov_common, hdict_common, hsupport_common,
          hjac_common]
    _ = B.totalAmp * scale s * B.profile (dist Y) := by
        dsimp [totalAmp, p]
        ring

end YMActivityErrorBudget

end YangMills.RG
