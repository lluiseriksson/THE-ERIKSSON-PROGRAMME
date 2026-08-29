/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP85SourceMassParameterUniformComplexWindow
import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0

namespace YangMills.RG

noncomputable section

/-- The common physical point-source coefficient obtained by evaluating the
complete Fourier amplitude at the positive CMP85 source-flow floor. -/
def cmp99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0
    (a : ℝ) (L : ℕ) (rho : ℝ) : ℝ :=
  cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
      (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) rho *
    (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho)

/-- On a nonnegative strip, the complete Green numerator is strictly positive:
its central `exp(rho)^4` summand is positive and the noncentral summand is
nonnegative. -/
theorem cmp89Eq248ComplexGreenNumeratorBound_pos (rho : ℝ) (hrho : 0 ≤ rho) :
    0 < cmp89Eq248ComplexGreenNumeratorBound_draft rho := by
  have hfine :
      0 ≤ cmp89Eq251CentralFineSymbolStripUpperBound rho := by
    rw [cmp89Eq251CentralFineSymbolStripUpperBound,
      cmp89Eq249CentralFineSymbolVerticalBound,
      cmp89Eq249CentralFineSymbolRealBound]
    positivity
  have hsum :
      0 ≤ cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
    rw [cmp89Eq248ComplexNoncentralGreenSumBound_draft,
      cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft,
      cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  rw [cmp89Eq248ComplexGreenNumeratorBound_draft]
  exact add_pos_of_pos_of_nonneg (pow_pos (Real.exp_pos rho) 4)
    (mul_nonneg hfine hsum)

/-- The common coefficient is strictly positive whenever the floor itself
has the scalar complex window.  Positivity is derived from that strict
margin; it is not a caller-supplied property of `B0`. -/
theorem cmp99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0_pos
    {a rho : ℝ} {L : ℕ} (hrho : 0 < rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) rho) :
    0 < cmp99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0
      a L rho := by
  have hmargin :
      0 < cmp89Eq249CentralStabilizedLowerConstant 4
          (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) -
        cmp89Eq249CentralStabilizedDenominatorVariationBound
          (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) rho := by
    simpa [CMP89Eq249CentralStabilizedComplexWindow] using hwindow
  have hreciprocal :
      0 < cmp89Eq249CentralStabilizedComplexReciprocalBound
        (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) rho := by
    rw [cmp89Eq249CentralStabilizedComplexReciprocalBound]
    exact inv_pos.mpr hmargin
  have hamplitude :
      0 < cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
        (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) rho := by
    rw [cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft]
    exact mul_pos
      (cmp89Eq248ComplexGreenNumeratorBound_pos rho hrho.le) hreciprocal
  have hden : 0 < 1 - Real.exp (-rho) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hgeom : 0 < (2 / (1 - Real.exp (-rho))) ^ 4 :=
    pow_pos (div_pos (by norm_num) hden) 4
  rw [cmp99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0]
  exact mul_pos (mul_pos hamplitude hgeom) (Real.exp_pos _)

/-- At every depth, the literal C6a coefficient is bounded by the single
coefficient evaluated at the CMP85 source-flow floor. -/
theorem
    cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0_le_uniform
    {a rho : ℝ} {L : ℕ} (ha : 0 < a) (hL : 2 ≤ L)
    (depth : ℕ) (hrho : 0 < rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) rho) :
    cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0
        a L depth rho ≤
      cmp99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0
        a L rho := by
  have hLnat : 1 < L := lt_of_lt_of_le (by omega) hL
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hLnat
  have hfloor :
      0 < cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ) :=
    cmp85Eq215SourceAveragingCoefficientFloor_pos ha hLreal
  have hfloorLe :
      cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ) ≤
        cmp99SourceMassParameter a (L : ℝ) depth :=
    cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter
      ha hLreal depth
  have hamp :
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
          (cmp99SourceMassParameter a (L : ℝ) depth) rho ≤
        cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
          (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) rho :=
    cmp89Eq248ComplexStabilizedGreenAmplitudeBound_antitone
      hfloor hfloorLe hrho.le hwindow
  rw [cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0,
    cmp99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0,
    cmp99SourceFlowFlatFullComplexA]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hamp (by positivity))
    (Real.exp_pos _).le

/-- A single positive radius and a single positive point-source coefficient
work simultaneously for every coefficient in the literal CMP85 source flow.
The floor window and positivity of `B0` are built internally. -/
theorem
    exists_cmp99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0
    {a : ℝ} {L : ℕ} (ha : 0 < a) (hL : 2 ≤ L) :
    ∃ rho B0 : ℝ, 0 < rho ∧ 0 < B0 ∧
      rho * Real.exp rho ≤ 1 / 6 ∧
      CMP89Eq249UniformNoncentralComplexRadiusCondition rho ∧
      ∀ depth,
        CMP89Eq249CentralStabilizedComplexWindow
            (cmp99SourceFlowFlatFullComplexA a L depth) rho ∧
          cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0
              a L depth rho ≤ B0 := by
  have hLnat : 1 < L := lt_of_lt_of_le (by omega) hL
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hLnat
  let floor := cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)
  have hfloor : 0 < floor :=
    cmp85Eq215SourceAveragingCoefficientFloor_pos ha hLreal
  obtain ⟨rho, hrho, hamplitude, hradius, hwindow⟩ :=
    exists_cmp89Eq249CentralStabilizedComplexRadius hfloor
  let B0 :=
    cmp99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0 a L rho
  have hB0 : 0 < B0 := by
    dsimp [B0]
    exact
      cmp99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0_pos
        hrho (by simpa [floor] using hwindow)
  refine ⟨rho, B0, hrho, hB0, hamplitude, hradius, ?_⟩
  intro depth
  have hfloorLe :
      floor ≤ cmp99SourceMassParameter a (L : ℝ) depth :=
    cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter
      ha hLreal depth
  have hdepthWindow :
      CMP89Eq249CentralStabilizedComplexWindow
        (cmp99SourceFlowFlatFullComplexA a L depth) rho := by
    rw [cmp99SourceFlowFlatFullComplexA]
    exact CMP89Eq249CentralStabilizedComplexWindow_mono
      hfloor hfloorLe hrho.le hwindow
  refine ⟨hdepthWindow, ?_⟩
  dsimp [B0]
  exact
    cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0_le_uniform
      ha hL depth hrho (by simpa [floor] using hwindow)

end

end YangMills.RG
