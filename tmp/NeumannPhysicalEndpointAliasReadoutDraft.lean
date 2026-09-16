import YangMills.RG.NeumannAliasPrecisionReadout

/-!
PRE-VALIDATION: source present, .olean not materialized; these new statements
are not compiler verified. Preserve the two actual fine endpoints until
AFTER the alias precision acts on its internally built solution. The alias
side L^j is not the ambient torus side. No physical inverse is asserted.
-/

namespace YangMills.RG
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

end
end YangMills.RG

#print axioms YangMills.RG.neumannPhysicalEndpoint_aliasPhase
#print axioms YangMills.RG.neumannPhysicalEndpoint_aliasPrecision_readout
