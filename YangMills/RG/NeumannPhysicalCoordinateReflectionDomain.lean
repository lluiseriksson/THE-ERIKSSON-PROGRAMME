import YangMills.RG.NeumannActualCoordinateGreenIntegrand
import YangMills.RG.BalabanCMP89Eq246MassUniformAnalyticDomain

/-!
# PRE-VALIDATION: physical common-strip production for coordinate reflection
Source present; .olean not materialized; result not compiler-verified.
Both finite-solver domains are constructed from the existing mass-uniform
windows. Neither domain nor Green covariance is supplied by the caller.
This is still an integrand identity, not a normalized integral theorem.
-/

namespace YangMills.RG
noncomputable section

theorem neumannCoordinateReflectedDomain_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (z : Fin 4 → ℂ)
    (hreal : ∀ k, |(z k).re| ≤ Real.pi)
    (himag : ∀ k, |(z k).im| ≤ rho) :
    CMP89Eq246FullSolutionDomain 4 L j mass a
      (neumannMomentumCoordinateReflection 4 mu z) := by
  apply cmp89Eq246FullSolutionDomain_of_commonRadius_massUniform
    ha hrho hamplitude hradius hdenWindow hpairWindow hmass
    (p := fun k => (neumannMomentumCoordinateReflection 4 mu z k).re)
  · intro k
    by_cases h : k = mu <;>
      simpa [neumannMomentumCoordinateReflection, h] using hreal k
  · intro k
    rfl
  · intro k
    by_cases h : k = mu <;>
      simpa [neumannMomentumCoordinateReflection, h] using himag k

theorem neumannPhysicalFineGreenIntegrand_coordinateReflection_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (z : Fin 4 → ℂ)
    (hreal : ∀ k, |(z k).re| ≤ Real.pi)
    (himag : ∀ k, |(z k).im| ≤ rho)
    (target source : Fin 4 → ℤ) :
    cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
      (neumannMomentumCoordinateReflection 4 mu z)
      (neumannFineEndpointCoordinateReflection 4 (L ^ j) mu target)
      (neumannFineEndpointCoordinateReflection 4 (L ^ j) mu source) =
    cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a z target source := by
  have hb : CMP89Eq246FullSolutionDomain 4 L j mass a z :=
    cmp89Eq246FullSolutionDomain_of_commonRadius_massUniform
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      hreal (fun _ => rfl) himag
  have hr := neumannCoordinateReflectedDomain_massUniform
    (L := L) (j := j)
    ha hrho hamplitude hradius hdenWindow hpairWindow hmass mu z hreal himag
  simpa only [cmp89Eq246PhysicalFineToFineGreenIntegrand,
    cmp89Eq249FineLatticeSpacing] using
    neumannActualFineGreenIntegrand_coordinateReflection
      4 L j mu mass a z target source hb hr


end
end YangMills.RG

