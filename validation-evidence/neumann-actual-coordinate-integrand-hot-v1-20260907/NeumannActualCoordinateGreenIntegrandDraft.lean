import NeumannActualCoordinateSolutionDraft
import NeumannCoordinateEndpointPhaseDraft

/-!
# PRE-VALIDATION: literal full point-source integrand reflection
Source present; .olean not materialized; result not compiler-verified.
R3 and the integer endpoint phases are consumed, not assumed as a Green law.
Both literal solver domains remain visible; integration is a separate gate.
-/

namespace YangMills.RG
noncomputable section

theorem neumannActualPointSource_coordinateTransport
    (d L j : ℕ) [NeZero L] (mu : Fin d) (z : Fin d → ℂ)
    (u : Fin d → ℤ) :
    neumannActualCoordinateSourceTransport d L j mu z
      (cmp89Eq246FinePointSourceAliasVector d L j z
        (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹) u)) =
    cmp89Eq246FinePointSourceAliasVector d L j
      (neumannMomentumCoordinateReflection d mu z)
      (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹)
        (neumannFineEndpointCoordinateReflection d (L ^ j) mu u)) := by
  funext k
  obtain ⟨m, rfl⟩ := (neumannPhysicalAliasCoordinateReflection d L j mu).surjective k
  simpa [neumannActualCoordinateSourceTransport,
    NeumannDiagonalTransportRepro.transport, cmp89Eq246FinePointSourceAliasVector,
    mul_comm] using (neumannAliasSourcePhase_coordinateReflection d L j mu z m u).symm

theorem neumannActualPointSolution_coordinateReflection
    (d L j : ℕ) [NeZero L] (mu : Fin d) (mass a : ℝ) (z : Fin d → ℂ)
    (u : Fin d → ℤ)
    (baseDomain : CMP89Eq246FullSolutionDomain d L j mass a z)
    (reflectedDomain : CMP89Eq246FullSolutionDomain d L j mass a
      (neumannMomentumCoordinateReflection d mu z))
    (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246StabilizedFinePointSourceSolution d L j mass a
      (neumannMomentumCoordinateReflection d mu z)
      (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹)
        (neumannFineEndpointCoordinateReflection d (L ^ j) mu u))
      (neumannPhysicalAliasCoordinateReflection d L j mu m) =
    neumannCoordinateHalfCellPhase d (L ^ j) mu
      (cmp89Eq248EntireAliasMomentum z m.1) *
    cmp89Eq246StabilizedFinePointSourceSolution d L j mass a z
      (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹) u) m := by
  have h := neumannActualCoordinateFullSolution_transport d L j mu mass a z
    (cmp89Eq246FinePointSourceAliasVector d L j z
      (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹) u))
    baseDomain reflectedDomain
  rw [neumannActualPointSource_coordinateTransport] at h
  have hm := congrFun h (neumannPhysicalAliasCoordinateReflection d L j mu m)
  simpa [neumannActualCoordinateSourceTransport,
    NeumannDiagonalTransportRepro.transport,
    cmp89Eq246StabilizedFinePointSourceSolution] using hm.symm

theorem neumannActualFineGreenIntegrand_coordinateReflection
    (d L j : ℕ) [NeZero L] (mu : Fin d) (mass a : ℝ) (z : Fin d → ℂ)
    (target source : Fin d → ℤ)
    (baseDomain : CMP89Eq246FullSolutionDomain d L j mass a z)
    (reflectedDomain : CMP89Eq246FullSolutionDomain d L j mass a
      (neumannMomentumCoordinateReflection d mu z)) :
    cmp89Eq246StabilizedFineToFineGreenIntegrand d L j mass a
      (neumannMomentumCoordinateReflection d mu z)
      (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹)
        (neumannFineEndpointCoordinateReflection d (L ^ j) mu target))
      (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹)
        (neumannFineEndpointCoordinateReflection d (L ^ j) mu source)) =
    cmp89Eq246StabilizedFineToFineGreenIntegrand d L j mass a z
      (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹) target)
      (cmp89Eq249PhysicalFineLatticeDisplacement (((L ^ j : ℕ) : ℝ)⁻¹) source) := by
  unfold cmp89Eq246StabilizedFineToFineGreenIntegrand
  rw [← Equiv.sum_comp (neumannPhysicalAliasCoordinateReflection d L j mu)]
  apply Finset.sum_congr rfl
  intro m _
  rw [neumannAliasTargetPhase_coordinateReflection,
    neumannActualPointSolution_coordinateReflection d L j mu mass a z source
      baseDomain reflectedDomain]
  have hD := neumannCoordinateHalfCellPhase_ne_zero d (L ^ j) mu
    (cmp89Eq248EntireAliasMomentum z m.1)
  field_simp [hD]

#print axioms neumannActualPointSource_coordinateTransport
#print axioms neumannActualPointSolution_coordinateReflection
#print axioms neumannActualFineGreenIntegrand_coordinateReflection

end
end YangMills.RG
