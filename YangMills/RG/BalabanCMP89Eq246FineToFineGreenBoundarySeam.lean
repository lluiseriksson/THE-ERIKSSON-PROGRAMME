import YangMills.RG.BalabanCMP89Eq246FineToFineGreenIntegrandPeriodicity
import YangMills.RG.BalabanCMP89Eq246FullSolutionDomain

/-!
# Boundary seam for the complete CMP89 (2.46) point-source integrand

Only the two opposite Brillouin faces are compared.  The common-polistrip
windows construct the finite-solver domain independently at the lower and
upper face, and the alias-cycle theorem then identifies the two values.  No
global periodicity of the rational extension is assumed.
-/

namespace YangMills.RG

noncomputable section

/-- The complete point-source integrand agrees on the two vertical faces of
one physical Brillouin rectangle. -/
theorem cmp89Eq246PhysicalFineToFineGreenIntegrand_boundarySeam
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (nu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho)
    (target source : Fin 4 → ℤ) :
    cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) target source =
      cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        z target source := by
  let pShift : Fin 4 → ℝ := fun k => if k = nu then Real.pi else p k
  have hpShift : ∀ k, |pShift k| ≤ Real.pi := by
    intro k
    by_cases hk : k = nu
    · subst k
      simp [pShift, abs_of_pos Real.pi_pos]
    · simpa [pShift, hk] using hp k
  have hrealShift : ∀ k,
      (cmp89Eq248PhysicalCoordinatePeriodShift nu z k).re = pShift k := by
    intro k
    by_cases hk : k = nu
    · subst k
      simp [cmp89Eq248PhysicalCoordinatePeriodShift, Pi.single_apply,
        pShift, hreal nu, hface]
      ring
    · simp [cmp89Eq248PhysicalCoordinatePeriodShift, Pi.single_apply,
        pShift, hk, hreal k]
  have himagShift : ∀ k,
      |(cmp89Eq248PhysicalCoordinatePeriodShift nu z k).im| ≤ rho := by
    intro k
    by_cases hk : k = nu
    · subst k
      simpa [cmp89Eq248PhysicalCoordinatePeriodShift, Pi.single_apply]
        using himag nu
    · simpa [cmp89Eq248PhysicalCoordinatePeriodShift, Pi.single_apply, hk]
        using himag k
  have baseDomain : CMP89Eq246FullSolutionDomain 4 L j mass a z :=
    cmp89Eq246FullSolutionDomain_of_commonRadius
      ha hmassPos hrho hamplitude hradius hdenWindow hpairWindow hmass
        hp hreal himag
  have shiftedDomain : CMP89Eq246FullSolutionDomain 4 L j mass a
      (cmp89Eq248PhysicalCoordinatePeriodShift nu z) :=
    cmp89Eq246FullSolutionDomain_of_commonRadius
      ha hmassPos hrho hamplitude hradius hdenWindow hpairWindow hmass
        hpShift hrealShift himagShift
  exact cmp89Eq246PhysicalFineToFineGreenIntegrand_periodShift
    L j mass a nu z target source baseDomain shiftedDomain

end

end YangMills.RG
