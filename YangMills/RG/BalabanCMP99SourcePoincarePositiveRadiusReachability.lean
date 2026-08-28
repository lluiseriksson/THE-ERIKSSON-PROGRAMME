import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreen
import YangMills.RG.BalabanCMP109PhysicalPivotSmallnessCompatibility
import YangMills.RG.BalabanCMP99Eq335PhysicalRetainedNearIdentity


/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/
namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The energy ledger only threads the radius argument; its value is exactly
independent of that argument. -/
theorem cmp99SourcePoincareEnergyCoeff_eq_zeroRadius
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
theorem continuousAt_cmp99SourceUbarNextFineRadius_zero :
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
theorem continuousAt_cmp99SourceScaledGradientStepError_zero
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
      (continuousAt_cmp99SourceUbarNextFineRadius_zero
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
theorem continuousAt_cmp99SourcePoincareErrorCoeff_zero
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
          (continuousAt_cmp99SourceUbarNextFineRadius_zero
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
          exact cmp99SourcePoincareEnergyCoeff_eq_zeroRadius
            (d := d) (M := M) depth ((M : ℝ) * spacing) (next epsilon)
        rw [heq]
        fun_prop
      have hstep :=
        continuousAt_cmp99SourceScaledGradientStepError_zero
          (d := d) (M := M) spacing
      simp only [cmp99SourcePoincareErrorCoeff]
      exact continuousAt_const.mul
        ((henergy.mul hstep).add (herror.mul continuousAt_const))

/-- For every fixed finite tower and spacing there is one open
positive-radius interval on which the closed `Ubar` budget and terminal
Poincare absorption inequality hold simultaneously. -/
theorem exists_pos_poincare_admissibleRadius
    (depth : ℕ) (spacing : ℝ) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ {epsilon : ℝ}, 0 ≤ epsilon → epsilon < radius →
        CMP99SourceUbarClosedBudget d M Nc depth epsilon ∧
        cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1 := by
  have hPcont :=
    continuousAt_cmp99SourcePoincareErrorCoeff_zero
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
theorem exists_pos_poincare_closedBudget
    (depth : ℕ) (spacing : ℝ) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧
      CMP99SourceUbarClosedBudget d M Nc depth epsilon ∧
      cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1 ∧
      (∀ e : ConcreteEdge d N,
        ‖(cmp99SourceFlatGaugeConfig d N Nc e :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) := by
  obtain ⟨radius, hradius, hrange⟩ :=
    exists_pos_poincare_admissibleRadius
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
theorem exists_pos_poincare_pivot_closedBudget
    (depth : ℕ) (spacing : ℝ) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧
      epsilon ≤ 1 ∧
      CMP99SourceUbarClosedBudget d M Nc depth epsilon ∧
      cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1 ∧
      cmp99SourceUbarFineDeviationRadius d M epsilon ≤ 1 / 3 ∧
      cmp109PhysicalPivotBackgroundBudget d M Nc epsilon < 1 ∧
      (∀ e : ConcreteEdge d N,
        ‖(cmp99SourceFlatGaugeConfig d N Nc e :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) := by
  obtain ⟨radius, hradius, hrange⟩ :=
    exists_pos_poincare_admissibleRadius
      (d := d) (M := M) (Nc := Nc) depth spacing
  let pivot := cmp109PhysicalPivotSmallnessRegimeWitness d M Nc
  let epsilon : ℝ := min radius (min pivot.epsilon0 1) / 2
  have hpivot_pos : 0 < pivot.epsilon0 := pivot.epsilon0_pos
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    exact div_pos (lt_min hradius (lt_min hpivot_pos (by norm_num)))
      (by norm_num)
  have hepsilon_one : epsilon ≤ 1 := by
    dsimp only [epsilon]
    have hmin : min radius (min pivot.epsilon0 1) ≤ 1 :=
      (min_le_right radius (min pivot.epsilon0 1)).trans
        (min_le_right pivot.epsilon0 1)
    linarith
  have hepsilon_radius : epsilon < radius := by
    dsimp only [epsilon]
    have hmin := min_le_left radius (min pivot.epsilon0 1)
    linarith
  have hepsilon_pivot : epsilon ≤ pivot.epsilon0 := by
    dsimp only [epsilon]
    have hmin : min radius (min pivot.epsilon0 1) ≤ pivot.epsilon0 :=
      (min_le_right radius (min pivot.epsilon0 1)).trans
        (min_le_left pivot.epsilon0 1)
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
  refine ⟨epsilon, hepsilon, hepsilon_one, hbudget, hsmall, hpivot_radius,
    hpivot_budget, ?_⟩
  intro e
  exact (cmp99SourceFlatGaugeConfig_zero_small
    (d := d) (Nc := Nc) (N := N) e).trans hepsilon.le

/-- The common positive source radius can be expressed in the literal
Corollary-3.6 convention `epsilon = 2 * alpha1`.  Thus `alpha1` is constructed,
is bounded by the half-unit chart window, and all radius-dependent conclusions
refer definitionally to the same retained near-identity radius. -/
theorem exists_pos_poincare_pivot_alpha1_closedBudget
    (depth : ℕ) (spacing : ℝ) :
    ∃ alpha1 : ℝ,
      0 < alpha1 ∧
      alpha1 ≤ 1 / 2 ∧
      CMP99SourceUbarClosedBudget d M Nc depth
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) ∧
      cmp99SourcePoincareErrorCoeff d M depth spacing
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1 ∧
      cmp99SourceUbarFineDeviationRadius d M
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) ≤ 1 / 3 ∧
      cmp109PhysicalPivotBackgroundBudget d M Nc
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1 ∧
      (∀ e : ConcreteEdge d N,
        ‖(cmp99SourceFlatGaugeConfig d N Nc e :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
          cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) := by
  obtain ⟨epsilon, hepsilon, hepsilon_one, hbudget, hsmall,
      hpivot_radius, hpivot_budget, hflat⟩ :=
    exists_pos_poincare_pivot_closedBudget
      (d := d) (M := M) (N := N) (Nc := Nc) depth spacing
  let alpha1 : ℝ := epsilon / 2
  have halpha1 : 0 < alpha1 := div_pos hepsilon (by norm_num)
  have halpha1_half : alpha1 ≤ 1 / 2 := by
    dsimp only [alpha1]
    linarith
  have hradius : cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1 =
      epsilon := by
    dsimp only [alpha1, cmp99Eq335PhysicalRetainedNearIdentityRadius]
    ring
  refine ⟨alpha1, halpha1, halpha1_half, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hradius] using hbudget
  · simpa only [hradius] using hsmall
  · simpa only [hradius] using hpivot_radius
  · simpa only [hradius] using hpivot_budget
  · intro e
    simpa only [hradius] using hflat e

/-- The constructed `alpha1` determines a nonempty interval of source
regularity radii `alpha0` on which the Corollary-3.6 scale gate is derived.
The cube coefficient is positive by the printed `geometryFactor ≥ 10` law;
neither `hscale` nor the terminal Poincare inequality is caller data. -/
theorem exists_pos_poincare_sourceAlphaInterval
    {FineSite : Type*} [DecidableEq FineSite]
    {n Mlarge : ℕ} [NeZero Mlarge]
    {scaleExtent : Fin n → ℕ}
    {S : CMP99SourceScaledStratification FineSite n
      (fun r => FinBox 4 (scaleExtent r))}
    {scaleExtent_pos : ∀ r, 0 < scaleExtent r}
    (C : CMP99SourceRegularCube FineSite n Mlarge scaleExtent S
      scaleExtent_pos)
    (depth : ℕ) (spacing : ℝ) :
    ∃ alpha1 alpha0Radius : ℝ,
      0 < alpha1 ∧
      alpha1 ≤ 1 / 2 ∧
      0 < alpha0Radius ∧
      CMP99SourceUbarClosedBudget d M Nc depth
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) ∧
      cmp99SourcePoincareErrorCoeff d M depth spacing
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1 ∧
      cmp99SourceUbarFineDeviationRadius d M
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) ≤ 1 / 3 ∧
      cmp109PhysicalPivotBackgroundBudget d M Nc
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1 ∧
      (∀ e : ConcreteEdge d N,
        ‖(cmp99SourceFlatGaugeConfig d N Nc e :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
          cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) ∧
      (∀ {alpha0 : ℝ}, 0 ≤ alpha0 → alpha0 ≤ alpha0Radius →
        (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1) := by
  obtain ⟨alpha1, halpha1, halpha1_half, hbudget, hsmall,
      hpivot_radius, hpivot_budget, hflat⟩ :=
    exists_pos_poincare_pivot_alpha1_closedBudget
      (d := d) (M := M) (N := N) (Nc := Nc) depth spacing
  let coeff : ℝ := (C.geometryFactor : ℝ) * (Mlarge : ℝ)
  have hgeometry_nat : 0 < C.geometryFactor :=
    lt_of_lt_of_le (by norm_num) C.geometryFactor_ge_ten
  have hgeometry : 0 < (C.geometryFactor : ℝ) := by
    exact_mod_cast hgeometry_nat
  have hMlarge_nat : 0 < Mlarge := NeZero.pos Mlarge
  have hMlarge : 0 < (Mlarge : ℝ) := by
    exact_mod_cast hMlarge_nat
  have hcoeff : 0 < coeff := mul_pos hgeometry hMlarge
  let alpha0Radius : ℝ := alpha1 / coeff
  have halpha0Radius : 0 < alpha0Radius := div_pos halpha1 hcoeff
  refine ⟨alpha1, alpha0Radius, halpha1, halpha1_half,
    halpha0Radius, hbudget, hsmall, hpivot_radius, hpivot_budget, hflat, ?_⟩
  intro alpha0 halpha0_nonneg halpha0_le
  calc
    (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 = coeff * alpha0 := by
      rfl
    _ ≤ coeff * alpha0Radius :=
      mul_le_mul_of_nonneg_left halpha0_le hcoeff.le
    _ = alpha1 := by
      dsimp only [alpha0Radius]
      field_simp [hcoeff.ne']

end

end YangMills.RG
