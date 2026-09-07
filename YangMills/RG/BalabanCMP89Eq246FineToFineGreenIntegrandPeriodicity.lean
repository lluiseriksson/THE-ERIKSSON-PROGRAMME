import YangMills.RG.BalabanCMP89Eq246FinePointSourceSolutionCycle

/-!
# Physical periodicity of the complete CMP89 (2.46) integrand

The full fine-to-fine point-source integrand is periodic in each physical
Brillouin coordinate.  The proof transports both the solved source fibre and
the inverse-transform target phase through the same centered-alias cycle,
then reindexes the complete finite sum.  It does not use the distinct
Eq. (2.48) averaged source.
-/

namespace YangMills.RG

noncomputable section

private theorem cmp89Eq246IntegrandCycleCount_pos
    (L j : ℕ) [NeZero L] : 0 < L ^ j :=
  pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j

/-- Periodicity of the complete physical fine-point-source integrand from
the two literal finite-system domain packages. -/
theorem cmp89Eq246PhysicalFineToFineGreenIntegrand_periodShift
    (L j : ℕ) [NeZero L] (mass a : ℝ) (nu : Fin 4)
    (z : Fin 4 → ℂ) (target source : Fin 4 → ℤ)
    (baseDomain : CMP89Eq246FullSolutionDomain 4 L j mass a z)
    (shiftedDomain : CMP89Eq246FullSolutionDomain 4 L j mass a
      (cmp89Eq248PhysicalCoordinatePeriodShift nu z)) :
    cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) target source =
      cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        z target source := by
  let cycle := cmp89Eq245CenteredAliasVectorCycle 4 (L ^ j)
    (cmp89Eq246IntegrandCycleCount_pos L j) nu
  let targetEndpoint := cmp89Eq249PhysicalFineLatticeDisplacement
    (((L ^ j : ℕ) : ℝ)⁻¹) target
  let sourceEndpoint := cmp89Eq249PhysicalFineLatticeDisplacement
    (((L ^ j : ℕ) : ℝ)⁻¹) source
  let term := fun w : Fin 4 → ℂ => fun m : CMP89Eq246AliasIndex 4 L j =>
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum w m.1) targetEndpoint) *
      cmp89Eq246StabilizedFinePointSourceSolution
        4 L j mass a w sourceEndpoint m
  rw [cmp89Eq246PhysicalFineToFineGreenIntegrand_eq,
    cmp89Eq246PhysicalFineToFineGreenIntegrand_eq,
    cmp89Eq246StabilizedFineToFineGreenIntegrand]
  change (∑ m, term (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m) =
    ∑ m, term z m
  calc
    (∑ m, term (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m) =
      ∑ m, term z (cycle m) := by
        apply Finset.sum_congr rfl
        intro m _
        unfold term
        rw [exp_I_cmp89Eq246TargetPhase_physicalShift_eq_cycle,
          cmp89Eq246StabilizedFinePointSourceSolution_physicalShift_eq_cycle
            4 L j mass a nu z source baseDomain shiftedDomain]
    _ = ∑ m, term z m := Equiv.sum_comp cycle (term z)

end

end YangMills.RG
