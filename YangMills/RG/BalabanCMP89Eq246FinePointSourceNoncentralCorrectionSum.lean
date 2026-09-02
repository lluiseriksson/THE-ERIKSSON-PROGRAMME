import YangMills.RG.BalabanCMP89Eq246FinePointSourceNoncentralCorrectionBound

/-!
# PRE-VALIDATION: uniformly summable noncentral rank-one correction

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.

Unlike the unsmoothed bare diagonal branch, the rank-one correction contains
the averaging-column quotient and therefore uses the already sealed strictly
summable `alpha = -1` alias weight.
-/

namespace YangMills.RG

noncomputable section

/-- Scale-uniform budget for the sum of noncentral rank-one corrections. -/
def cmp89Eq246FinePointSourceNoncentralCorrectionSumBound
    (a rho : ℝ) (sourceEndpoint : Fin 4 → ℝ) : ℝ :=
  cmp89Eq251ContourPhaseGrowth rho sourceEndpoint *
    (cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound a rho *
      (∑' n : ℤ,
        cmp89Eq251OneDimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4)

/-- The complete noncentral rank-one correction sum is uniform in the alias
window. -/
theorem sum_norm_cmp89Eq246FinePointSourceNoncentralCorrection_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (sourceEndpoint : Fin 4 → ℝ) :
    (∑ m ∈ (Finset.univ : Finset (CMP89Eq246AliasIndex 4 L j)).erase
        (cmp89Eq249CentralAliasIndex 4 L j),
      ‖(a : ℂ) * cmp89Eq246EntireAliasAverageColumn 4 L j z m *
            cmp89Eq246StabilizedFinePointSourceSolutionMoment
              4 L j mass a sourceEndpoint z /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z m‖) ≤
      cmp89Eq246FinePointSourceNoncentralCorrectionSumBound
        a rho sourceEndpoint := by
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let growth := cmp89Eq251ContourPhaseGrowth rho sourceEndpoint
  let coefficient :=
    cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound a rho
  let weight : CMP89Eq246AliasIndex 4 L j → ℝ := fun m =>
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 (-1)) m.1
  have hgrowth : 0 ≤ growth := by
    dsimp [growth, cmp89Eq251ContourPhaseGrowth]
    positivity
  have hcoefficient : 0 ≤ coefficient := by
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
    dsimp [coefficient,
      cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound]
    apply mul_nonneg
    · exact mul_nonneg (abs_nonneg a) hquotient
    · exact hmoment
  have hpoint : ∀ m ∈ (Finset.univ :
      Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
      ‖(a : ℂ) * cmp89Eq246EntireAliasAverageColumn 4 L j z m *
            cmp89Eq246StabilizedFinePointSourceSolutionMoment
              4 L j mass a sourceEndpoint z /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z m‖ ≤
        growth * (coefficient * weight m) := by
    intro m hm
    have hmne : m ≠ central := (Finset.mem_erase.mp hm).1
    simpa [central, growth, coefficient, weight] using
      norm_cmp89Eq246FinePointSourceNoncentralCorrection_le
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hradius hmass hwindow hamplitude hp hreal himag
        sourceEndpoint m hmne
  have heraseWeight :
      (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central, weight m) ≤
        ∑ m, weight m := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset central Finset.univ)
      (fun m _ _ => cmp89Eq251MultidimensionalAliasWeight_nonneg _ m.1)
  have hsubtype :
      (∑ m : CMP89Eq246AliasIndex 4 L j, weight m) =
        cmp89Eq251CenteredMultidimensionalAliasSum 4 (L ^ j)
          (cmp89Eq251AliasSeriesExponent 4 (-1)) := by
    simpa [weight, CMP89Eq246AliasIndex,
      cmp89Eq251CenteredMultidimensionalAliasSum] using
      (Finset.sum_attach (cmp89Eq245CenteredAliasVectors 4 (L ^ j))
        (fun m => cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m))
  have hfinite :=
    cmp89Eq251CenteredOneDimensionalAliasSum_source_le_tsum
      (d := 4) (L ^ j) (alpha := (-1 : ℝ)) (by norm_num) (by norm_num)
  have hfiniteNonneg :
      0 ≤ cmp89Eq251CenteredOneDimensionalAliasSum (L ^ j)
        (cmp89Eq251AliasSeriesExponent 4 (-1)) := by
    exact Finset.sum_nonneg fun n _ =>
      cmp89Eq251OneDimensionalAliasWeight_nonneg _ n
  have hpow := pow_le_pow_left₀ hfiniteNonneg hfinite 4
  calc
    _ ≤ ∑ m ∈ (Finset.univ :
        Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
        growth * (coefficient * weight m) :=
      Finset.sum_le_sum hpoint
    _ = growth * (coefficient *
        (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central,
          weight m)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ growth * (coefficient * ∑ m, weight m) := by
      gcongr
    _ = growth * (coefficient *
        cmp89Eq251CenteredMultidimensionalAliasSum 4 (L ^ j)
          (cmp89Eq251AliasSeriesExponent 4 (-1))) := by rw [hsubtype]
    _ = growth * (coefficient *
        cmp89Eq251CenteredOneDimensionalAliasSum (L ^ j)
          (cmp89Eq251AliasSeriesExponent 4 (-1)) ^ 4) := by
      rw [cmp89Eq251CenteredMultidimensionalAliasSum_eq_pow]
    _ ≤ growth * (coefficient *
        (∑' n : ℤ,
          cmp89Eq251OneDimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4) := by
      gcongr
    _ = cmp89Eq246FinePointSourceNoncentralCorrectionSumBound
        a rho sourceEndpoint := rfl

end

end YangMills.RG
