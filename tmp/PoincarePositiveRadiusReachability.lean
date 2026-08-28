/- PRE-VALIDATION scratch source.
Source is present; no `.olean` has been materialized and no declaration below
has been verified by the Lean compiler. -/

import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreen
import YangMills.RG.BalabanCMP109PhysicalPivotSmallnessCompatibility

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The energy ledger only threads the radius argument; its value is exactly
independent of that argument. -/
theorem scratch_cmp99SourcePoincareEnergyCoeff_eq_zeroRadius
    (depth : ℕ) (spacing epsilon : ℝ) :
    cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon =
      cmp99SourcePoincareEnergyCoeff d M depth spacing 0 := by
  induction depth generalizing spacing epsilon with
  | zero => rfl
  | succ depth ih =>
      simp only [cmp99SourcePoincareEnergyCoeff]
      rw [ih ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon),
        ih ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M 0)]

/-- The exact rational one-step source radius is continuous at the flat
radius; both denominators specialize to one there. -/
theorem scratch_continuousAt_cmp99SourceUbarNextFineRadius_zero :
    ContinuousAt (fun epsilon : ℝ =>
      cmp99SourceUbarNextFineRadius d M epsilon) 0 := by
  let delta : ℝ → ℝ := fun epsilon =>
    ((3 * d * (M - 1) + M : ℕ) : ℝ) * epsilon
  let theta : ℝ → ℝ := fun epsilon =>
    delta epsilon / (1 - delta epsilon)
  have hdelta : ContinuousAt delta 0 := by
    dsimp only [delta]
    fun_prop
  have hdelta_zero : delta 0 = 0 := by simp [delta]
  have htheta : ContinuousAt theta 0 := by
    dsimp only [theta]
    exact hdelta.div (continuousAt_const.sub hdelta) (by simp [hdelta_zero])
  have htheta_zero : theta 0 = 0 := by simp [theta, hdelta_zero]
  unfold cmp99SourceUbarNextFineRadius cmp99SourceUbarFineDeviationRadius
  change ContinuousAt (fun epsilon : ℝ =>
    theta epsilon + theta epsilon ^ 2 / (1 - theta epsilon) +
      (M : ℝ) * epsilon) 0
  exact
    (htheta.add
      ((htheta.pow 2).div (continuousAt_const.sub htheta)
        (by simp [htheta_zero]))).add
      (continuousAt_const.mul continuousAt_id)

/-- The literal scaled-gradient error is continuous at the flat radius. -/
theorem scratch_continuousAt_cmp99SourceScaledGradientStepError_zero
    (spacing : ℝ) :
    ContinuousAt (fun epsilon : ℝ =>
      cmp99SourceScaledGradientStepError d M epsilon spacing) 0 := by
  let triple : ℝ → ℝ := fun epsilon =>
    ((2 * d * (M - 1) + M : ℕ) : ℝ) * epsilon
  let next : ℝ → ℝ := fun epsilon =>
    cmp99SourceUbarNextFineRadius d M epsilon
  have htriple : ContinuousAt triple 0 := by
    dsimp only [triple]
    fun_prop
  have hnext : ContinuousAt next 0 := by
    simpa only [next] using
      (scratch_continuousAt_cmp99SourceUbarNextFineRadius_zero
        (d := d) (M := M))
  have hsum : ContinuousAt (fun epsilon => triple epsilon + next epsilon) 0 :=
    htriple.add hnext
  have hnum : ContinuousAt (fun epsilon : ℝ =>
      2 * cmp99SourceBlockAverageWeight M d *
        (2 * (triple epsilon + next epsilon)) ^ 2 * (d : ℝ)) 0 :=
    (continuousAt_const.mul
      ((continuousAt_const.mul hsum).pow 2)).mul continuousAt_const
  unfold cmp99SourceScaledGradientStepError cmp99SourceTripleHolonomyRadius
  change ContinuousAt (fun epsilon : ℝ =>
    2 * cmp99SourceBlockAverageWeight M d *
      (2 * (triple epsilon + next epsilon)) ^ 2 * (d : ℝ) /
        (((M : ℝ) * spacing) ^ 2)) 0
  exact hnum.div_const _

/-- At every fixed finite depth and spacing, the recursively accumulated
Poincare error is continuous at the flat radius. -/
theorem scratch_continuousAt_cmp99SourcePoincareErrorCoeff_zero
    (depth : ℕ) (spacing : ℝ) :
    ContinuousAt (fun epsilon : ℝ =>
      cmp99SourcePoincareErrorCoeff d M depth spacing epsilon) 0 := by
  induction depth generalizing spacing with
  | zero =>
      simp only [cmp99SourcePoincareErrorCoeff]
      fun_prop
  | succ depth ih =>
      let next : ℝ → ℝ := fun epsilon =>
        cmp99SourceUbarNextFineRadius d M epsilon
      have hnext : ContinuousAt next 0 := by
        simpa only [next] using
          (scratch_continuousAt_cmp99SourceUbarNextFineRadius_zero
            (d := d) (M := M))
      have herrorBase :
          ContinuousAt
            (fun epsilon : ℝ =>
              cmp99SourcePoincareErrorCoeff d M depth
                ((M : ℝ) * spacing) epsilon)
            (next 0) := by
        simpa only [next, cmp99SourceUbarNextFineRadius_zero] using
          (ih ((M : ℝ) * spacing))
      have herror :
          ContinuousAt
            (fun epsilon : ℝ =>
              cmp99SourcePoincareErrorCoeff d M depth
                ((M : ℝ) * spacing) (next epsilon)) 0 :=
        herrorBase.comp 0 hnext
      have henergy :
          ContinuousAt
            (fun epsilon : ℝ =>
              cmp99SourcePoincareEnergyCoeff d M depth
                ((M : ℝ) * spacing) (next epsilon)) 0 := by
        have heq :
            (fun epsilon : ℝ =>
              cmp99SourcePoincareEnergyCoeff d M depth
                ((M : ℝ) * spacing) (next epsilon)) =
              fun _ : ℝ =>
                cmp99SourcePoincareEnergyCoeff d M depth
                  ((M : ℝ) * spacing) 0 := by
          funext epsilon
          exact scratch_cmp99SourcePoincareEnergyCoeff_eq_zeroRadius
            (d := d) (M := M) depth ((M : ℝ) * spacing) (next epsilon)
        rw [heq]
        fun_prop
      have hstep :=
        scratch_continuousAt_cmp99SourceScaledGradientStepError_zero
          (d := d) (M := M) spacing
      simp only [cmp99SourcePoincareErrorCoeff]
      exact continuousAt_const.mul
        ((henergy.mul hstep).add (herror.mul continuousAt_const))

/-- For every fixed finite tower and spacing there is one open
positive-radius interval on which the closed `Ubar` budget and terminal
Poincare absorption inequality hold simultaneously. -/
theorem scratch_exists_pos_poincare_admissibleRadius
    (depth : ℕ) (spacing : ℝ) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ {epsilon : ℝ}, 0 ≤ epsilon → epsilon < radius →
        CMP99SourceUbarClosedBudget d M Nc depth epsilon ∧
        cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1 := by
  have hPcont :=
    scratch_continuousAt_cmp99SourcePoincareErrorCoeff_zero
      (d := d) (M := M) depth spacing
  have hPevent :
      {epsilon : ℝ |
        cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1} ∈
        𝓝 0 := by
    have h := hPcont.eventually_lt_const (by
      simpa using (show (0 : ℝ) < 1 by norm_num))
    simpa only [cmp99SourcePoincareErrorCoeff_zero] using h
  obtain ⟨rP, hrP, hPball⟩ := Metric.mem_nhds_iff.mp hPevent

  let target : ℝ := min (cmp99UbarNoWindingThreshold Nc) (1 / 4 : ℝ)
  let coeff : ℝ :=
    cmp99SourceUbarDeviationCoefficient d M *
      cmp99SourceUbarRadiusGrowthFactor d M ^ depth
  have htarget : 0 < target := by
    dsimp only [target]
    exact lt_min cmp99UbarNoWindingThreshold_pos (by norm_num)
  have hUcont : ContinuousAt (fun epsilon : ℝ => coeff * epsilon) 0 := by
    fun_prop
  have hUevent : {epsilon : ℝ | coeff * epsilon < target} ∈ 𝓝 0 := by
    have h := hUcont.eventually_lt_const (by
      simpa using htarget)
    simpa using h
  obtain ⟨rU, hrU, hUball⟩ := Metric.mem_nhds_iff.mp hUevent

  let radius : ℝ := min rP rU
  have hradius : 0 < radius := by
    exact lt_min hrP hrU
  refine ⟨radius, hradius, ?_⟩
  intro epsilon hepsilon_nonneg hepsilon_lt
  have hepsilonP : epsilon ∈ Metric.ball (0 : ℝ) rP := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_nonneg hepsilon_nonneg]
    exact hepsilon_lt.trans_le (min_le_left rP rU)
  have hepsilonU : epsilon ∈ Metric.ball (0 : ℝ) rU := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_nonneg hepsilon_nonneg]
    exact hepsilon_lt.trans_le (min_le_right rP rU)
  refine ⟨?_, hPball hepsilonP⟩
  · refine
      { epsilon_nonneg := hepsilon_nonneg
        terminal_small := ?_ }
    simpa only [coeff, target, mul_assoc] using hUball hepsilonU

/-- A concrete positive-radius inhabitant of the preceding interval.  The
literal flat background witnesses that the physical small-field ball is
nonempty at the same radius. -/
theorem scratch_exists_pos_poincare_closedBudget
    (depth : ℕ) (spacing : ℝ) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧
      CMP99SourceUbarClosedBudget d M Nc depth epsilon ∧
      cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1 ∧
      (∀ e : ConcreteEdge d N,
        ‖(cmp99SourceFlatGaugeConfig d N Nc e :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) := by
  obtain ⟨radius, hradius, hrange⟩ :=
    scratch_exists_pos_poincare_admissibleRadius
      (d := d) (M := M) (Nc := Nc) depth spacing
  let epsilon : ℝ := radius / 2
  have hepsilon : 0 < epsilon := div_pos hradius (by norm_num)
  have hepsilon_lt : epsilon < radius := by
    dsimp only [epsilon]
    linarith
  obtain ⟨hbudget, hsmall⟩ :=
    hrange hepsilon.le hepsilon_lt
  refine ⟨epsilon, hepsilon, hbudget, hsmall, ?_⟩
  · intro e
    exact (cmp99SourceFlatGaugeConfig_zero_small
      (d := d) (Nc := Nc) (N := N) e).trans hepsilon.le

/-- One common strictly positive source radius simultaneously inhabits the
closed `Ubar` tower budget, terminal Poincare absorption and the two literal
CMP109 pivot conditions.  The pivot witness is restricted monotonically; no
new scalar target is introduced. -/
theorem scratch_exists_pos_poincare_pivot_closedBudget
    (depth : ℕ) (spacing : ℝ) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧
      CMP99SourceUbarClosedBudget d M Nc depth epsilon ∧
      cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1 ∧
      cmp99SourceUbarFineDeviationRadius d M epsilon ≤ 1 / 3 ∧
      cmp109PhysicalPivotBackgroundBudget d M Nc epsilon < 1 ∧
      (∀ e : ConcreteEdge d N,
        ‖(cmp99SourceFlatGaugeConfig d N Nc e :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) := by
  obtain ⟨radius, hradius, hrange⟩ :=
    scratch_exists_pos_poincare_admissibleRadius
      (d := d) (M := M) (Nc := Nc) depth spacing
  let pivot := cmp109PhysicalPivotSmallnessRegimeWitness d M Nc
  let epsilon : ℝ := min radius pivot.epsilon0 / 2
  have hpivot_pos : 0 < pivot.epsilon0 := pivot.epsilon0_pos
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    exact div_pos (lt_min hradius hpivot_pos) (by norm_num)
  have hepsilon_radius : epsilon < radius := by
    dsimp only [epsilon]
    have hmin := min_le_left radius pivot.epsilon0
    linarith
  have hepsilon_pivot : epsilon ≤ pivot.epsilon0 := by
    dsimp only [epsilon]
    have hmin := min_le_right radius pivot.epsilon0
    linarith
  obtain ⟨hbudget, hsmall⟩ :=
    hrange hepsilon.le hepsilon_radius
  have hpivot_radius :
      cmp99SourceUbarFineDeviationRadius d M epsilon ≤ 1 / 3 := by
    rw [cmp99SourceUbarFineDeviationRadius_eq_coefficient_mul]
    calc
      cmp99SourceUbarDeviationCoefficient d M * epsilon ≤
          cmp99SourceUbarDeviationCoefficient d M * pivot.epsilon0 :=
        mul_le_mul_of_nonneg_left hepsilon_pivot
          (cmp99SourceUbarDeviationCoefficient_nonneg d M)
      _ ≤ 1 / 3 := by
        simpa only [cmp99SourceUbarFineDeviationRadius_eq_coefficient_mul]
          using pivot.background_radius
  have hpivot_budget :
      cmp109PhysicalPivotBackgroundBudget d M Nc epsilon < 1 := by
    rw [cmp109PhysicalPivotBackgroundBudget_eq_at_one_mul]
    calc
      cmp109PhysicalPivotBackgroundBudget d M Nc 1 * epsilon ≤
          cmp109PhysicalPivotBackgroundBudget d M Nc 1 * pivot.epsilon0 :=
        mul_le_mul_of_nonneg_left hepsilon_pivot
          (cmp109PhysicalPivotBackgroundBudget_nonneg (by norm_num))
      _ < 1 := by
        simpa only [cmp109PhysicalPivotBackgroundBudget_eq_at_one_mul]
          using pivot.pivot_budget
  refine ⟨epsilon, hepsilon, hbudget, hsmall, hpivot_radius,
    hpivot_budget, ?_⟩
  intro e
  exact (cmp99SourceFlatGaugeConfig_zero_small
    (d := d) (Nc := Nc) (N := N) e).trans hepsilon.le

end

end YangMills.RG
