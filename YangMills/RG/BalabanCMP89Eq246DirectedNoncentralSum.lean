import YangMills.RG.BalabanCMP89Eq246DirectedNoncentralComponent
import YangMills.RG.BalabanCMP89Eq251CenteredHalfAliasSum

/-!
# Directed noncentral alias sum below CMP89 (2.46)

The target phase remains inside every summand.  The bare inverse-Laplacian
half-weight and the strictly summable rank-one weight are accumulated
separately, so the visible quadratic alias-size loss cannot be confused with
the scale-uniform correction budget.

This module and its audit were cold-verified from exact source checkpoint
`1f3bc9b0bb85016d1ebb96514b4da54f5e32b754` in a fresh Colab Pro+ checkout.
-/

namespace YangMills.RG

noncomputable section

/-- The literal directed noncentral alias sum, with one common source and
target endpoint but the target phase evaluated at each alias momentum. -/
def cmp89Eq246DirectedNoncentralSolutionSum
    (L j : ℕ) [NeZero L] (mass a rho : ℝ)
    (p targetEndpoint sourceEndpoint : Fin 4 → ℝ) : ℂ :=
  let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
  let z := cmp89Eq251SignedContourMomentum rho p displacement
  let central := cmp89Eq249CentralAliasIndex 4 L j
  ∑ m ∈ (Finset.univ : Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
    Complex.exp
        (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint) *
      cmp89Eq246StabilizedFinePointSourceSolution
        4 L j mass a z sourceEndpoint m

/-- Explicit directed budget for the full noncentral fibre.  The first term
is the unavoidable four-dimensional half-weight loss; the second remains
uniform in the alias count. -/
def cmp89Eq246DirectedNoncentralSolutionSumBound
    (L j : ℕ) (a rho : ℝ) : ℝ :=
  cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound *
      (256 * ((L ^ j + 1 : ℕ) : ℝ) ^ 2) +
    cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound a rho *
      (∑' n : ℤ,
        cmp89Eq251OneDimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4

/-- Summing the target-phased noncentral components preserves their common
relative endpoint decay.  The two alias weights are summed by their own
certificates before the budgets are combined. -/
theorem norm_cmp89Eq246DirectedNoncentralSolutionSum_signedContour_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (targetEndpoint sourceEndpoint : Fin 4 → ℝ) :
    let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
    ‖cmp89Eq246DirectedNoncentralSolutionSum
        L j mass a rho p targetEndpoint sourceEndpoint‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        cmp89Eq246DirectedNoncentralSolutionSumBound L j a rho := by
  classical
  dsimp only
  let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
  let z := cmp89Eq251SignedContourMomentum rho p displacement
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let targetPhase : CMP89Eq246AliasIndex 4 L j → ℂ := fun m =>
    Complex.exp
      (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint)
  let solution := cmp89Eq246StabilizedFinePointSourceSolution
    4 L j mass a z sourceEndpoint
  let term : CMP89Eq246AliasIndex 4 L j → ℂ := fun m =>
    targetPhase m * solution m
  let decay := Real.exp
    (-(rho * cmp89Eq251DisplacementL1 displacement))
  let bareCoefficient := cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound
  let correctionCoefficient :=
    cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound a rho
  let bareWeight : CMP89Eq246AliasIndex 4 L j → ℝ := fun m =>
    cmp89Eq251MultidimensionalAliasWeight (1 / 2 : ℝ) m.1
  let correctionWeight : CMP89Eq246AliasIndex 4 L j → ℝ := fun m =>
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 (-1)) m.1
  let bareSeries := 256 * ((L ^ j + 1 : ℕ) : ℝ) ^ 2
  let correctionSeries :=
    (∑' n : ℤ,
      cmp89Eq251OneDimensionalAliasWeight
        (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4
  have hdecay : 0 ≤ decay := by
    dsimp [decay]
    positivity
  have hbareCoefficient : 0 ≤ bareCoefficient := by
    dsimp [bareCoefficient,
      cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound]
    positivity
  have hcorrectionCoefficient : 0 ≤ correctionCoefficient := by
    have hquotient :
        0 ≤ cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho := by
      dsimp [cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft,
        cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
        cmp89Eq245EntireAverageAliasStripConstant]
      positivity
    have hseries :
        0 ≤ ∑' n : ℤ, cmp89Eq251OneDimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) n := by
      exact tsum_nonneg fun n =>
        cmp89Eq251OneDimensionalAliasWeight_nonneg _ n
    have hgreenSum :
        0 ≤ cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
      rw [cmp89Eq248ComplexNoncentralGreenSumBound_draft]
      exact mul_nonneg hquotient (pow_nonneg hseries 4)
    have hstrip : 0 ≤ cmp89Eq251CentralFineSymbolStripUpperBound rho := by
      dsimp [cmp89Eq251CentralFineSymbolStripUpperBound,
        cmp89Eq249CentralFineSymbolVerticalBound,
        cmp89Eq249CentralFineSymbolRealBound]
      positivity
    have hreciprocal :
        0 ≤ cmp89Eq249CentralStabilizedComplexReciprocalBound a rho := by
      rw [cmp89Eq249CentralStabilizedComplexReciprocalBound]
      exact inv_nonneg.mpr (sub_nonneg.mpr hwindow.le)
    have hmoment :
        0 ≤ cmp89Eq246FinePointSourceMomentAmplitudeBound a rho := by
      rw [cmp89Eq246FinePointSourceMomentAmplitudeBound]
      exact mul_nonneg
        (add_nonneg (pow_nonneg (Real.exp_pos rho).le 4)
          (mul_nonneg hstrip hgreenSum))
        hreciprocal
    dsimp [correctionCoefficient,
      cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound]
    exact mul_nonneg (mul_nonneg (abs_nonneg a) hquotient) hmoment
  have hpoint : ∀ m ∈ (Finset.univ :
      Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
      ‖term m‖ ≤ decay *
        (bareCoefficient * bareWeight m +
          correctionCoefficient * correctionWeight m) := by
    intro m hm
    have hmne : m ≠ central := (Finset.mem_erase.mp hm).1
    simpa [term, targetPhase, solution, decay, bareCoefficient,
      correctionCoefficient, bareWeight, correctionWeight, z, displacement,
      central] using
      (norm_cmp89Eq246TargetPhase_mul_noncentralSolution_signedContour_le
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hradius hmass hwindow hamplitude hp
        targetEndpoint sourceEndpoint m hmne)
  have heraseBare :
      (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
        bareWeight m) ≤ ∑ m, bareWeight m := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset central Finset.univ)
      (fun m _ _ => cmp89Eq251MultidimensionalAliasWeight_nonneg _ m.1)
  have hsubtypeBare :
      (∑ m : CMP89Eq246AliasIndex 4 L j, bareWeight m) =
        cmp89Eq251CenteredMultidimensionalAliasSum 4 (L ^ j)
          (1 / 2 : ℝ) := by
    simpa [bareWeight, CMP89Eq246AliasIndex,
      cmp89Eq251CenteredMultidimensionalAliasSum] using
      (Finset.sum_attach (cmp89Eq245CenteredAliasVectors 4 (L ^ j))
        (fun m => cmp89Eq251MultidimensionalAliasWeight (1 / 2 : ℝ) m))
  have hbareSum :
      (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
        bareWeight m) ≤ bareSeries := by
    calc
      _ ≤ ∑ m, bareWeight m := heraseBare
      _ = cmp89Eq251CenteredMultidimensionalAliasSum 4 (L ^ j)
          (1 / 2 : ℝ) := hsubtypeBare
      _ ≤ 256 * ((L ^ j + 1 : ℕ) : ℝ) ^ 2 := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          cmp89Eq251CenteredFourDimensionalAliasSum_half_le (L ^ j)
      _ = bareSeries := rfl
  have heraseCorrection :
      (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
        correctionWeight m) ≤ ∑ m, correctionWeight m := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset central Finset.univ)
      (fun m _ _ => cmp89Eq251MultidimensionalAliasWeight_nonneg _ m.1)
  have hsubtypeCorrection :
      (∑ m : CMP89Eq246AliasIndex 4 L j, correctionWeight m) =
        cmp89Eq251CenteredMultidimensionalAliasSum 4 (L ^ j)
          (cmp89Eq251AliasSeriesExponent 4 (-1)) := by
    simpa [correctionWeight, CMP89Eq246AliasIndex,
      cmp89Eq251CenteredMultidimensionalAliasSum] using
      (Finset.sum_attach (cmp89Eq245CenteredAliasVectors 4 (L ^ j))
        (fun m => cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m))
  have hcorrectionSum :
      (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
        correctionWeight m) ≤ correctionSeries := by
    calc
      _ ≤ ∑ m, correctionWeight m := heraseCorrection
      _ = cmp89Eq251CenteredMultidimensionalAliasSum 4 (L ^ j)
          (cmp89Eq251AliasSeriesExponent 4 (-1)) := hsubtypeCorrection
      _ ≤ (∑' n : ℤ,
          cmp89Eq251OneDimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4 :=
        cmp89Eq251CenteredMultidimensionalAliasSum_source_le_tsum_pow
          (d := 4) (L ^ j) (alpha := (-1 : ℝ)) (by norm_num) (by norm_num)
      _ = correctionSeries := rfl
  have hbareWeighted :
      (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
        bareCoefficient * bareWeight m) ≤
          bareCoefficient * bareSeries := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hbareSum hbareCoefficient
  have hcorrectionWeighted :
      (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
        correctionCoefficient * correctionWeight m) ≤
          correctionCoefficient * correctionSeries := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hcorrectionSum hcorrectionCoefficient
  have hweightSum :
      (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
        (bareCoefficient * bareWeight m +
          correctionCoefficient * correctionWeight m)) ≤
        bareCoefficient * bareSeries +
          correctionCoefficient * correctionSeries := by
    rw [Finset.sum_add_distrib]
    exact add_le_add hbareWeighted hcorrectionWeighted
  rw [cmp89Eq246DirectedNoncentralSolutionSum]
  change ‖∑ m ∈ (Finset.univ :
      Finset (CMP89Eq246AliasIndex 4 L j)).erase central, term m‖ ≤ _
  calc
    _ ≤ ∑ m ∈ (Finset.univ :
        Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
        ‖term m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ (Finset.univ :
        Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
        decay * (bareCoefficient * bareWeight m +
          correctionCoefficient * correctionWeight m) :=
      Finset.sum_le_sum hpoint
    _ = decay *
        (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
          (bareCoefficient * bareWeight m +
            correctionCoefficient * correctionWeight m)) := by
      rw [Finset.mul_sum]
    _ ≤ decay * (bareCoefficient * bareSeries +
        correctionCoefficient * correctionSeries) :=
      mul_le_mul_of_nonneg_left hweightSum hdecay
    _ = Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        cmp89Eq246DirectedNoncentralSolutionSumBound L j a rho := rfl

end

end YangMills.RG
