import YangMills.RG.BalabanCMP89SourceNeumannPhysicalGateMonotonicity
import YangMills.RG.BalabanCMP99SourcePoincarePositiveRadiusReachability

/-!
# Positive-radius reachability of the two-scale physical Neumann gate

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

At fixed positive physical spacing, continuity of the literal first `Ubar`
radius at zero and the existing closed-budget neighborhood produce one common
positive radius satisfying both source-ratio targets of the `27/512` gate.
No background family, regional Green or depth-uniform radius is constructed.
-/

namespace YangMills.RG

open scoped Topology

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

/-- The source dimension/block witness is attained by a nonempty interval of
literal two-step `Ubar` radii at every fixed positive spacing. -/
theorem exists_pos_cmp89SourceNeumann_twoScale_physical_gate_radius
    (spacing : ℝ) (hspacing : 0 < spacing) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧
      CMP99SourceUbarClosedBudget 4 4 Nc 2 epsilon ∧
      cmp99OneScaleBlockPoincareConstant 4 4 *
          cmp89SourceNeumannPhysicalOneStepDefectCoefficient 4 4
            (epsilon / spacing)
            (cmp99SourceUbarNextFineRadius 4 4 epsilon /
              ((4 : ℝ) * spacing)) < 1 := by
  let q : ℝ := ((4 : ℝ)⁻¹) ^ 8
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  obtain ⟨radius, hradius, hrange⟩ :=
    exists_pos_poincare_admissibleRadius
      (d := 4) (M := 4) (Nc := Nc) 2 spacing
  have htarget : 0 < (4 : ℝ) * spacing * q := by positivity
  have hnextEvent :
      {epsilon : ℝ |
        cmp99SourceUbarNextFineRadius 4 4 epsilon <
          (4 : ℝ) * spacing * q} ∈ 𝓝 0 := by
    have hcont :=
      continuousAt_cmp99SourceUbarNextFineRadius_zero
        (d := 4) (M := 4)
    have h := hcont.eventually_lt_const (by
      simpa only [cmp99SourceUbarNextFineRadius_zero] using htarget)
    simpa only [cmp99SourceUbarNextFineRadius_zero] using h
  obtain ⟨rNext, hrNext, hNextBall⟩ := Metric.mem_nhds_iff.mp hnextEvent
  let epsilon : ℝ := min radius (min rNext (spacing * q)) / 2
  have hmin_pos : 0 < min radius (min rNext (spacing * q)) :=
    lt_min hradius (lt_min hrNext (mul_pos hspacing hq))
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    exact div_pos hmin_pos (by norm_num)
  have hepsilon_radius : epsilon < radius := by
    dsimp only [epsilon]
    calc
      min radius (min rNext (spacing * q)) / 2 <
          min radius (min rNext (spacing * q)) := by linarith
      _ ≤ radius := min_le_left _ _
  have hepsilon_next : epsilon < rNext := by
    dsimp only [epsilon]
    calc
      min radius (min rNext (spacing * q)) / 2 <
          min radius (min rNext (spacing * q)) := by linarith
      _ ≤ rNext := (min_le_right _ _).trans (min_le_left _ _)
  have hepsilon_fine : epsilon ≤ spacing * q := by
    dsimp only [epsilon]
    calc
      min radius (min rNext (spacing * q)) / 2 ≤
          min radius (min rNext (spacing * q)) := by linarith
      _ ≤ spacing * q := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hbudget, _hPoincare⟩ :=
    hrange hepsilon.le hepsilon_radius
  have hepsilon_mem : epsilon ∈ Metric.ball (0 : ℝ) rNext := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hepsilon.le]
    exact hepsilon_next
  have hnext : cmp99SourceUbarNextFineRadius 4 4 epsilon ≤
      ((4 : ℝ) * spacing) * q := by
    exact (hNextBall hepsilon_mem).le
  refine ⟨epsilon, hepsilon, hbudget, ?_⟩
  exact cmp89SourceNeumannPhysicalOneStepGate_lt_one_of_radius_bounds_d4_M4
    hspacing hepsilon.le
    (hbudget.toScalarBudget.radiusAt_nonneg (k := 1) (by norm_num))
    hepsilon_fine hnext

end

end YangMills.RG
