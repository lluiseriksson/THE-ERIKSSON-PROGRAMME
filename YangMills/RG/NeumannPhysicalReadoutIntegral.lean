import YangMills.RG.NeumannAliasPrecisionReadout
import YangMills.RG.NeumannAliasPhysicalIntegral
import YangMills.RG.BalabanCMP89Eq246MassUniformAnalyticDomain

/-!
PRE-VALIDATION: production source present, .olean not materialized and this
production module not compiler verified. Exact proof bodies from HOT source
f308441f2, independently preserved603a6771a. The actual alias-precision
readout integrates to (L^j)^4 times the equality delta using the internally
produced a.e. domain, including mass=0. This is not physical operator/integral
interchange, the finite regional inverse, uniform B0, or window15.
-/

namespace YangMills.RG
open MeasureTheory
noncomputable section

theorem neumannPhysicalEndpoint_aliasPhase
    (L j : ℕ) (z : Fin 4 → ℂ) (m target source : Fin 4 → ℤ) :
    Complex.I *
      (cmp89Eq251EntirePhase (cmp89Eq248EntireAliasMomentum z m)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) target) -
       cmp89Eq251EntirePhase (cmp89Eq248EntireAliasMomentum z m)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) source)) =
      ∑ i, Complex.I * (z i + 2 * Real.pi * (m i : ℂ)) *
        ((target - source) i : ℂ) / ((L ^ j : ℕ) : ℂ) := by
  unfold cmp89Eq251EntirePhase cmp89Eq248EntireAliasMomentum
    cmp89Eq245AliasShift cmp89Eq249PhysicalFineLatticeDisplacement
    cmp89Eq249FineLatticeSpacing
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  push_cast
  ring

theorem neumannPhysicalEndpoint_aliasPrecision_readout
    (L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin 4 → ℂ)
    (target source : Fin 4 → ℤ)
    (domain : CMP89Eq246FullSolutionDomain 4 L j mass a z) :
    (∑ m : CMP89Eq246AliasIndex 4 L j,
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m.1)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) target)) *
      ((cmp89Eq246EntireAliasPrecisionMatrix 4 L j mass a z).mulVec
        (cmp89Eq246StabilizedFinePointSourceSolution 4 L j mass a z
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) source))) m) =
      ∑ m : CMP89Eq246AliasIndex 4 L j,
        Complex.exp (∑ i, Complex.I * (z i + 2 * Real.pi * (m.1 i : ℂ)) *
          ((target - source) i : ℂ) / ((L ^ j : ℕ) : ℂ)) := by
  rw [neumannAliasPrecision_finePointSource_readout 4 L j mass a z _ _ domain]
  apply Finset.sum_congr rfl
  intro m _
  rw [neumannPhysicalEndpoint_aliasPhase]


theorem neumannPhysicalBrillouinParameter_ae_bound :
    ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure,
      ∀ mu, |cmp89Eq251PhysicalBrillouinParameter x mu| ≤ Real.pi := by
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  let cube : Set (Fin 4 → ℝ) :=
    Set.univ.pi fun _ : Fin 4 => Set.Ioc 0 (2 * Real.pi)
  have hmeasure : cmp89Eq249FourDimensionalBrillouinMeasure =
      (volume : Measure (Fin 4 → ℝ)).restrict cube := by
    dsimp [cmp89Eq249FourDimensionalBrillouinMeasure, cube]
    rw [volume_pi, Measure.restrict_pi_pi]
    simp [Set.uIoc_of_le htwoPi]
  have hcube : MeasurableSet cube :=
    MeasurableSet.pi (Set.to_countable Set.univ) fun _ _ => measurableSet_Ioc
  have hmem : ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure, x ∈ cube := by
    rw [hmeasure]
    exact ae_restrict_mem hcube
  filter_upwards [hmem] with x hx
  intro mu
  have hxmu : x mu ∈ Set.Ioc 0 (2 * Real.pi) := hx mu (by simp)
  rw [abs_le]
  simp only [cmp89Eq251PhysicalBrillouinParameter]
  constructor <;> linarith [Real.pi_pos, hxmu.1, hxmu.2]

theorem neumannPhysicalBrillouin_fullSolutionDomain_ae
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass) :
    ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure,
      CMP89Eq246FullSolutionDomain 4 L j mass a
        (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ)) := by
  filter_upwards [neumannPhysicalBrillouinParameter_ae_bound] with x hx
  exact cmp89Eq246FullSolutionDomain_of_commonRadius_massUniform
    ha hrho hamplitude hradius hdenWindow hpairWindow hmass hx
    (by intro mu; simp) (by intro mu; simpa using hrho)

/-- Literal precision readout, not the finite regional operator action. -/
def neumannPhysicalAliasPrecisionReadout
    (L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin 4 → ℂ)
    (target source : Fin 4 → ℤ) : ℂ :=
  ∑ m : CMP89Eq246AliasIndex 4 L j,
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z m.1)
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) target)) *
    ((cmp89Eq246EntireAliasPrecisionMatrix 4 L j mass a z).mulVec
      (cmp89Eq246StabilizedFinePointSourceSolution 4 L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) source))) m

theorem neumannPhysicalAliasPrecisionReadout_integral
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
      (fun x => neumannPhysicalAliasPrecisionReadout L j mass a
        (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
        target source) =
      if target = source then (((L ^ j : ℕ) : ℂ)^4) else 0 := by
  classical
  letI : NeZero (L ^ j) := ⟨pow_ne_zero _ (NeZero.ne L)⟩
  have hdomain := neumannPhysicalBrillouin_fullSolutionDomain_ae
    (L := L) (j := j) ha hrho hamplitude hradius hdenWindow hpairWindow hmass
  calc
    _ = cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x => ∑ m : CMP89Eq246AliasIndex 4 L j,
          Complex.exp (∑ i, Complex.I *
            ((cmp89Eq251PhysicalBrillouinParameter x i : ℂ) +
              2 * Real.pi * (m.1 i : ℂ)) *
            ((target - source) i : ℂ) / ((L ^ j : ℕ) : ℂ))) := by
      unfold cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
      congr 1
      apply integral_congr_ae
      filter_upwards [hdomain] with x hx
      exact neumannPhysicalEndpoint_aliasPrecision_readout L j mass a _ target source hx
    _ = _ := by
      simpa only [sub_eq_zero] using
        neumannCenteredAlias_physicalIntegral (L ^ j) (target - source)

end
end YangMills.RG
