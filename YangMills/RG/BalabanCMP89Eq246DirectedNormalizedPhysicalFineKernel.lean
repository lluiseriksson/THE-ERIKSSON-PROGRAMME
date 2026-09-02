import YangMills.RG.BalabanCMP89Eq246DirectedFullSolutionIntegralDictionary
import YangMills.RG.BalabanCMP89Eq249FineLatticeNormalizedStabilizedEndpointIntegral

/-!
# PRE-VALIDATION: physical fine-site specialization of directed CMP89 (2.46)

Source is present, its promoted `.olean` has not yet been materialized in a
fresh checkout, and the result has not yet been cold-verified by the compiler.

This wrapper inserts the literal fine-lattice spacing at both endpoints and
keeps the conversion from physical displacement to integer lattice distance
explicit.  It does not identify the resulting scalar kernel with the finite
periodic/generated Green, prove the point-source inverse equation, periodize
the infinite-lattice synthesis, or prove CMP89 (2.42).
-/

namespace YangMills.RG

noncomputable section

/-- The normalized directed Fourier synthesis evaluated at two literal sites
of the fine lattice `xi * Z^4`, where `xi = (L^j)^(-1)`. -/
def cmp89Eq246DirectedNormalizedPhysicalFineKernel
    (L j : ℕ) [NeZero L] (mass a rho : ℝ)
    (target source : Fin 4 → ℤ) : ℂ :=
  let xi := cmp89Eq249FineLatticeSpacing L j
  cmp89Eq246DirectedNormalizedFullSolutionIntegral L j mass a rho
    (cmp89Eq249PhysicalFineLatticeDisplacement xi target)
    (cmp89Eq249PhysicalFineLatticeDisplacement xi source)

/-- Subtracting the two physical endpoints is exactly scaling their integer
difference by the fine-lattice spacing. -/
theorem cmp89Eq246PhysicalFineEndpointDifference_eq
    (xi : ℝ) (target source : Fin 4 → ℤ) :
    (fun mu =>
      cmp89Eq249PhysicalFineLatticeDisplacement xi target mu -
        cmp89Eq249PhysicalFineLatticeDisplacement xi source mu) =
      cmp89Eq249PhysicalFineLatticeDisplacement xi
        (fun mu => target mu - source mu) := by
  funext mu
  simp only [cmp89Eq249PhysicalFineLatticeDisplacement]
  push_cast
  ring

/-- The directed synthesis has exponential decay in the integer fine-site
distance at the explicitly rescaled rate `rho * (L^j)^(-1)`.  The printed
`(L^j+1)^2` value scale remains inside the named amplitude bound. -/
theorem norm_cmp89Eq246DirectedNormalizedPhysicalFineKernel_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hstabilized : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpair : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (target source : Fin 4 → ℤ) :
    ‖cmp89Eq246DirectedNormalizedPhysicalFineKernel
        L j mass a rho target source‖ ≤
      Real.exp (-((rho * cmp89Eq249FineLatticeSpacing L j) *
        cmp89Eq251LatticeL1Length (fun mu => target mu - source mu))) *
        cmp89Eq246DirectedFullSolutionSumBound L j a rho := by
  let xi := cmp89Eq249FineLatticeSpacing L j
  have hxi : 0 ≤ xi := (cmp89Eq249FineLatticeSpacing_pos L j).le
  have hbound :=
    norm_cmp89Eq246DirectedNormalizedFullSolutionIntegral_le
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hradius hmass hstabilized hpair hamplitude
      (cmp89Eq249PhysicalFineLatticeDisplacement xi target)
      (cmp89Eq249PhysicalFineLatticeDisplacement xi source)
  dsimp only at hbound
  rw [cmp89Eq246PhysicalFineEndpointDifference_eq,
    cmp89Eq251DisplacementL1_physicalFineLatticeDisplacement hxi] at hbound
  simpa [cmp89Eq246DirectedNormalizedPhysicalFineKernel, xi, mul_assoc]
    using hbound

/-- The physical fine-site wrapper at zero contour radius is the existing
real-slice normalized fine-to-fine point-source Green synthesis.  This does
not identify either presentation with the generated finite periodic Green. -/
theorem cmp89Eq246DirectedNormalizedPhysicalFineKernel_zero_eq_realGreenSynthesis
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (target source : Fin 4 → ℤ) :
    cmp89Eq246DirectedNormalizedPhysicalFineKernel
        L j mass a 0 target source =
      cmp89Eq246NormalizedPhysicalFineToFineGreen
        L j mass a target source := by
  unfold cmp89Eq246DirectedNormalizedPhysicalFineKernel
  rw [cmp89Eq246DirectedNormalizedFullSolutionIntegral_zero_eq_realSlice]
  rfl

end

end YangMills.RG
