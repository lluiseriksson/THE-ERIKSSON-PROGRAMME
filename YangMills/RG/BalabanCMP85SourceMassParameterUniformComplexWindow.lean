import YangMills.RG.BalabanCMP85SourceAveragingCoefficientFloor
import YangMills.RG.BalabanCMP89Eq249CentralStabilizedComplexRadius
import YangMills.RG.BalabanCMP89Eq248MassUniformGreenBound

/-!
# PRE-VALIDATION: one complex strip for every source averaging coefficient

Source is present, its `.olean` has not been materialized, and the result has
not yet been verified by the compiler.

This is the scalar bridge that the generated-coefficient no-go leaves open.
The radius is chosen once at the positive CMP85 floor and then transported
to every source coefficient `a_j`.  It does not identify `a_j` with the
Poincare-generated full-complex coefficient and does not construct a
regional Green operator or a uniform physical `B0`.
-/

namespace YangMills.RG

noncomputable section

/-- Coefficient of the source parameter in the complete vertical variation
budget. -/
def cmp89Eq249CentralStabilizedDenominatorVariationSlope
    (rho : ℝ) : ℝ :=
  cmp89Eq249CentralAveragePairVerticalBound rho +
    (cmp89Eq249CentralFineSymbolVerticalBound rho *
        cmp89Eq249ComplexNoncentralAliasSumBound rho +
      cmp89Eq249CentralFineSymbolRealBound *
        cmp89Eq249ComplexNoncentralAliasSumVariationBound rho)

theorem cmp89Eq249CentralStabilizedDenominatorVariationBound_eq
    (a rho : ℝ) :
    cmp89Eq249CentralStabilizedDenominatorVariationBound a rho =
      cmp89Eq249CentralFineSymbolVerticalBound rho +
        a * cmp89Eq249CentralStabilizedDenominatorVariationSlope rho := by
  unfold cmp89Eq249CentralStabilizedDenominatorVariationBound
    cmp89Eq249CentralStabilizedDenominatorVariationSlope
  ring

/-- Once the conservative stabilized window holds at one positive source
coefficient, it keeps holding at every larger coefficient. -/
theorem CMP89Eq249CentralStabilizedComplexWindow_mono
    {a b rho : ℝ} (ha : 0 < a) (hab : a ≤ b) (hrho : 0 ≤ rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho) :
    CMP89Eq249CentralStabilizedComplexWindow b rho := by
  let fine := cmp89Eq249CentralFineSymbolVerticalBound rho
  let slope := cmp89Eq249CentralStabilizedDenominatorVariationSlope rho
  let central := ((2 / Real.pi) ^ (4 : ℕ)) ^ 2
  have hfine : 0 ≤ fine := by
    dsimp [fine, cmp89Eq249CentralFineSymbolVerticalBound]
    have heps : 0 ≤ rho * Real.exp rho :=
      mul_nonneg hrho (Real.exp_pos rho).le
    exact mul_nonneg (mul_nonneg (by norm_num) heps)
      (add_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) heps)
  have hwindow' : fine + a * slope < a * central := by
    simpa only [CMP89Eq249CentralStabilizedComplexWindow,
      cmp89Eq249CentralStabilizedDenominatorVariationBound_eq,
      cmp89Eq249CentralStabilizedLowerConstant, fine, slope, central]
      using hwindow
  have hslope : slope < central := by
    by_contra h
    have hcs : central ≤ slope := le_of_not_gt h
    have hmul : a * central ≤ a * slope :=
      mul_le_mul_of_nonneg_left hcs ha.le
    linarith
  have hdelta : 0 ≤ b - a := sub_nonneg.mpr hab
  have htransport : (b - a) * slope ≤ (b - a) * central :=
    mul_le_mul_of_nonneg_left hslope.le hdelta
  rw [CMP89Eq249CentralStabilizedComplexWindow,
    cmp89Eq249CentralStabilizedDenominatorVariationBound_eq,
    cmp89Eq249CentralStabilizedLowerConstant]
  change fine + b * slope < b * central
  calc
    fine + b * slope = (fine + a * slope) + (b - a) * slope := by ring
    _ < a * central + (b - a) * slope :=
      add_lt_add_right hwindow' _
    _ ≤ a * central + (b - a) * central :=
      by linarith
    _ = b * central := by ring

/-- The explicit reciprocal majorant improves when the positive source
coefficient grows.  Thus its value at the CMP85 floor is a common bound for
the whole source flow. -/
theorem cmp89Eq249CentralStabilizedComplexReciprocalBound_antitone
    {a b rho : ℝ} (ha : 0 < a) (hab : a ≤ b) (hrho : 0 ≤ rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho) :
    cmp89Eq249CentralStabilizedComplexReciprocalBound b rho ≤
      cmp89Eq249CentralStabilizedComplexReciprocalBound a rho := by
  let fine := cmp89Eq249CentralFineSymbolVerticalBound rho
  let slope := cmp89Eq249CentralStabilizedDenominatorVariationSlope rho
  let central := ((2 / Real.pi) ^ (4 : ℕ)) ^ 2
  let marginA := a * central - (fine + a * slope)
  let marginB := b * central - (fine + b * slope)
  have hfine : 0 ≤ fine := by
    dsimp [fine, cmp89Eq249CentralFineSymbolVerticalBound]
    have heps : 0 ≤ rho * Real.exp rho :=
      mul_nonneg hrho (Real.exp_pos rho).le
    exact mul_nonneg (mul_nonneg (by norm_num) heps)
      (add_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) heps)
  have hwindow' : fine + a * slope < a * central := by
    simpa only [CMP89Eq249CentralStabilizedComplexWindow,
      cmp89Eq249CentralStabilizedDenominatorVariationBound_eq,
      cmp89Eq249CentralStabilizedLowerConstant, fine, slope, central]
      using hwindow
  have hslope : slope < central := by
    by_contra h
    have hcs : central ≤ slope := le_of_not_gt h
    have hmul : a * central ≤ a * slope :=
      mul_le_mul_of_nonneg_left hcs ha.le
    linarith
  have hmarginA : 0 < marginA := by
    dsimp [marginA]
    linarith
  have hdelta : 0 ≤ b - a := sub_nonneg.mpr hab
  have hgain : 0 ≤ (b - a) * (central - slope) :=
    mul_nonneg hdelta (sub_nonneg.mpr hslope.le)
  have hmargins : marginA ≤ marginB := by
    dsimp [marginA, marginB]
    nlinarith
  have hmarginB : 0 < marginB := hmarginA.trans_le hmargins
  simpa only [cmp89Eq249CentralStabilizedComplexReciprocalBound,
    cmp89Eq249CentralStabilizedLowerConstant,
    cmp89Eq249CentralStabilizedDenominatorVariationBound_eq,
    marginA, marginB, fine, slope, central] using
      ((inv_le_inv₀ hmarginB hmarginA).2 hmargins)

theorem cmp89Eq248ComplexGreenNumeratorBound_nonneg
    {rho : ℝ} (hrho : 0 ≤ rho) :
    0 ≤ cmp89Eq248ComplexGreenNumeratorBound_draft rho := by
  rw [cmp89Eq248ComplexGreenNumeratorBound_draft]
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
  exact add_nonneg (by positivity) (mul_nonneg hfine hsum)

/-- The complete explicit Fourier amplitude is bounded by its value at the
smallest admissible source coefficient. -/
theorem cmp89Eq248ComplexStabilizedGreenAmplitudeBound_antitone
    {a b rho : ℝ} (ha : 0 < a) (hab : a ≤ b) (hrho : 0 ≤ rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho) :
    cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft b rho ≤
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho := by
  rw [cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft,
    cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft]
  exact mul_le_mul_of_nonneg_left
    (cmp89Eq249CentralStabilizedComplexReciprocalBound_antitone
      ha hab hrho hwindow)
    (cmp89Eq248ComplexGreenNumeratorBound_nonneg hrho)

/-- One radius simultaneously satisfies the three scalar strip conditions
for every coefficient in the literal CMP85 source flow. -/
theorem exists_cmp85SourceMassParameter_uniformComplexRadius
    {a : ℝ} {L : ℕ} (ha : 0 < a) (hL : 2 ≤ L) :
    ∃ rho : ℝ, 0 < rho ∧
      rho * Real.exp rho ≤ 1 / 6 ∧
      CMP89Eq249UniformNoncentralComplexRadiusCondition rho ∧
      ∀ j, CMP89Eq249CentralStabilizedComplexWindow
        (cmp99SourceMassParameter a (L : ℝ) j) rho := by
  have hLnat : 1 < L := lt_of_lt_of_le (by omega) hL
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hLnat
  let floor := cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)
  have hfloor : 0 < floor :=
    cmp85Eq215SourceAveragingCoefficientFloor_pos ha hLreal
  obtain ⟨rho, hrho, hamplitude, hradius, hwindow⟩ :=
    exists_cmp89Eq249CentralStabilizedComplexRadius hfloor
  refine ⟨rho, hrho, hamplitude, hradius, ?_⟩
  intro j
  exact CMP89Eq249CentralStabilizedComplexWindow_mono hfloor
    (cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter
      ha hLreal j)
    hrho.le
    hwindow

/-- The same source-floor choice supplies one explicit amplitude majorant for
every depth.  This remains a Fourier scalar statement; the operator and
regional dictionaries are separate obligations. -/
theorem exists_cmp85SourceMassParameter_uniformComplexRadiusAndAmplitude
    {a : ℝ} {L : ℕ} (ha : 0 < a) (hL : 2 ≤ L) :
    ∃ rho : ℝ, 0 < rho ∧
      rho * Real.exp rho ≤ 1 / 6 ∧
      CMP89Eq249UniformNoncentralComplexRadiusCondition rho ∧
      ∀ j,
        CMP89Eq249CentralStabilizedComplexWindow
            (cmp99SourceMassParameter a (L : ℝ) j) rho ∧
          cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
              (cmp99SourceMassParameter a (L : ℝ) j) rho ≤
            cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
              (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) rho := by
  have hLnat : 1 < L := lt_of_lt_of_le (by omega) hL
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hLnat
  let floor := cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)
  have hfloor : 0 < floor :=
    cmp85Eq215SourceAveragingCoefficientFloor_pos ha hLreal
  obtain ⟨rho, hrho, hamplitude, hradius, hwindow⟩ :=
    exists_cmp89Eq249CentralStabilizedComplexRadius hfloor
  refine ⟨rho, hrho, hamplitude, hradius, ?_⟩
  intro j
  have hfloorLe : floor ≤ cmp99SourceMassParameter a (L : ℝ) j :=
    cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter
      ha hLreal j
  refine ⟨CMP89Eq249CentralStabilizedComplexWindow_mono
    hfloor hfloorLe hrho.le hwindow, ?_⟩
  exact cmp89Eq248ComplexStabilizedGreenAmplitudeBound_antitone
    hfloor hfloorLe hrho.le hwindow

end

end YangMills.RG
