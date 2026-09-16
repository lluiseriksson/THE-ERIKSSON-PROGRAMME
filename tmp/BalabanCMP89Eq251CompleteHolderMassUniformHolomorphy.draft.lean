/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Mass-uniform holomorphy and physical boundary seam for the complete CMP89
Holder integrand.  This is the H3a replacement for the historical route whose
signature required `0 < mass`; it specializes literally to `mass = 0`.
No contour integral, bound, owner dictionary, regional B0, window-15 claim or
terminal field is asserted here.
-/

import YangMills.RG.BalabanCMP89Eq248GreenMassUniformHolomorphy
import YangMills.RG.BalabanCMP89Eq251StabilizedIntegrandHolomorphy
import YangMills.RG.BalabanCMP89Eq251DisplayedIntegrandPeriodicity
import YangMills.RG.BalabanCMP89Eq249FineLatticeCompleteHolderPeriodicity

namespace YangMills.RG

noncomputable section

/-- The complete literal stabilized Holder integrand is holomorphic throughout
the common polydisc under the mass-uniform denominator window.  No positive
mass premise survives. -/
theorem
    differentiableAt_cmp89Eq251ComplexStabilizedIntegrand_of_commonRadius_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    {mu : Fin 4}
    (holderDisplacement transportDisplacement : Fin 4 → ℝ) :
    DifferentiableAt ℂ (fun w : Fin 4 → ℂ =>
      cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha w mu
        holderDisplacement transportDisplacement) z := by
  have hfine : ∀ m ∈
      (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
        (cmp89Eq249ZeroAlias 4),
      cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0 := by
    intro m hm
    exact cmp89Eq251NoncentralFineSymbol_ne_zero_of_commonRadius
      hrho hradius hm hp hreal himag
  have hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z ≠ 0 :=
    cmp89Eq249CentralStabilizedAliasDenominator_ne_zero_massUniform
      ha hrho hradius hmass hwindow hp hreal himag hamplitude
  exact differentiableAt_cmp89Eq251ComplexStabilizedIntegrand
    hfine hstabilized

/-- The two vertical Brillouin faces agree for the complete stabilized Holder
integrand under the same mass-uniform window.  The full displayed rational
domain is constructed on the lower face before periodicity is used. -/
theorem cmp89Eq251ComplexStabilizedIntegrand_physicalFineHolder_boundarySeam_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (nu mu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho)
    (holderU transportU : Fin 4 → ℤ) :
    cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) transportU) =
      cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha z mu
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) transportU) := by
  rcases cmp89Eq251DisplayedDomain_of_boundaryFace_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass nu hp hface hreal himag with
    ⟨hunit, hreduced, hfine⟩
  exact
    cmp89Eq251ComplexStabilizedIntegrand_physicalFineHolderPeriodShift_of_nonzero_draft
      nu mu holderU transportU hunit hreduced hfine

end

end YangMills.RG
