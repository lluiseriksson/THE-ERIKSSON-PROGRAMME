import YangMills.RG.BalabanCMP85SourceMassParameterUniformComplexWindow
import YangMills.RG.BalabanCMP89Eq249CentralAveragePairComplexNonzero
import YangMills.RG.BalabanCMP89Eq246FinePointSourceMomentBound

/-!
# PRE-VALIDATION: scalar source-flow inputs for full G

Source is present; the `.olean` is not materialized and this result is not
verified by the compiler. This source is not yet imported by the root aggregator.

Only the literal recurrence, the equality of two scalar budget expressions,
and a joint strip choice are composed here. Equality of scalar budgets does
not identify G and G Q'^*. No full amplitude, physical rescaling, regional
bound or window-15 attainment follows from these scalar statements alone.
-/

namespace YangMills.RG

noncomputable section

/-- Every literal source coefficient is at most the initial coefficient.
This follows from its defining positive denominator, not a flow hypothesis. -/
theorem cmp85SourceFullGreen_massParameter_le_initial
    {a L : ℝ} (ha : 0 < a) (hL : 0 < L) (j : ℕ) :
    cmp99SourceMassParameter a L j ≤ a := by
  cases j with
  | zero => simp
  | succ j =>
      rw [cmp99SourceMassParameter_succ]
      have hm := cmp99SourceMassParameter_pos ha hL j
      have hb : 0 ≤ a * (L ^ 2)⁻¹ :=
        mul_nonneg ha.le (inv_nonneg.mpr (sq_nonneg L))
      apply (div_le_iff₀ (add_pos_of_nonneg_of_pos hb hm)).2
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hb) ha.le

/-- The full-source moment uses the same scalar numerator/reciprocal budget
as the already sealed particular-solution amplitude. No operator identity. -/
theorem cmp85SourceFullGreen_momentBudget_eq_scalarAmplitude (a rho : ℝ) :
    cmp89Eq246FinePointSourceMomentAmplitudeBound a rho =
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho := rfl

/-- The moment budget alone is antitone in the positive source coefficient;
the complete full-G budget also has positive coefficient factors. -/
theorem cmp85SourceFullGreen_momentBudget_antitone
    {a b rho : ℝ} (ha : 0 < a) (hab : a ≤ b) (hrho : 0 ≤ rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho) :
    cmp89Eq246FinePointSourceMomentAmplitudeBound b rho ≤
      cmp89Eq246FinePointSourceMomentAmplitudeBound a rho := by
  rw [cmp85SourceFullGreen_momentBudget_eq_scalarAmplitude,
    cmp85SourceFullGreen_momentBudget_eq_scalarAmplitude]
  exact cmp89Eq248ComplexStabilizedGreenAmplitudeBound_antitone
    ha hab hrho hwindow

/-- One radius satisfies the full-source pair gate and every source-flow
denominator gate, and bounds every moment by the value at the CMP85 floor.
The extra pair gate is constructed with the same radius, not assumed later. -/
theorem exists_cmp85SourceFullGreen_uniformRadiusAndMoment
    {a : ℝ} {L : ℕ} (ha : 0 < a) (hL : 2 ≤ L) :
    ∃ rho : ℝ, 0 < rho ∧
      rho * Real.exp rho ≤ 1 / 6 ∧
      CMP89Eq249UniformNoncentralComplexRadiusCondition rho ∧
      CMP89Eq249CentralAveragePairComplexWindow rho ∧
      CMP89Eq249CentralStabilizedComplexWindow
        (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) rho ∧
      ∀ j,
        CMP89Eq249CentralStabilizedComplexWindow
            (cmp99SourceMassParameter a (L : ℝ) j) rho ∧
          cmp89Eq246FinePointSourceMomentAmplitudeBound
              (cmp99SourceMassParameter a (L : ℝ) j) rho ≤
            cmp89Eq246FinePointSourceMomentAmplitudeBound
              (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) rho := by
  have hLnat : 1 < L := lt_of_lt_of_le (by omega) hL
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hLnat
  let floor := cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)
  have hfloor : 0 < floor :=
    cmp85Eq215SourceAveragingCoefficientFloor_pos ha hLreal
  obtain ⟨rho, hrho, hamp, hrad, hwindow, hpair⟩ :=
    exists_cmp89Eq249CentralStabilizedComplexRadius_with_pair hfloor
  refine ⟨rho, hrho, hamp, hrad, hpair, hwindow, ?_⟩
  intro j
  have hfloorLe : floor ≤ cmp99SourceMassParameter a (L : ℝ) j :=
    cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter ha hLreal j
  exact ⟨CMP89Eq249CentralStabilizedComplexWindow_mono
      hfloor hfloorLe hrho.le hwindow,
    cmp85SourceFullGreen_momentBudget_antitone hfloor hfloorLe hrho.le hwindow⟩

end

end YangMills.RG
