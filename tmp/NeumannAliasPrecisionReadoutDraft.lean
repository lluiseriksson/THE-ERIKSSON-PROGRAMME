import YangMills.RG.BalabanCMP89Eq246FullSolutionDomain

/-!
PRE-VALIDATION: source present; .olean not materialized and compiler result
not verified. Read out the literal precision acting on its internally built
fine point-source solution. The source and solution are not free families.
The two endpoint phases combine only AFTER applying the alias precision;
this does not identify the two-endpoint Green with a displacement kernel.
The finite physical operator/action dictionary and integral remain open.
-/

namespace YangMills.RG
noncomputable section

theorem neumannAliasPrecision_finePointSource_readout
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (targetEndpoint sourceEndpoint : Fin d → ℝ)
    (domain : CMP89Eq246FullSolutionDomain d L j mass a z) :
    (∑ m : CMP89Eq246AliasIndex d L j,
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint) *
      ((cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec
        (cmp89Eq246StabilizedFinePointSourceSolution
          d L j mass a z sourceEndpoint)) m) =
    ∑ m : CMP89Eq246AliasIndex d L j,
      Complex.exp (Complex.I *
        (cmp89Eq251EntirePhase (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint -
          cmp89Eq251EntirePhase (cmp89Eq248EntireAliasMomentum z m.1) sourceEndpoint)) := by
  rw [cmp89Eq246EntireAliasPrecisionMatrix_mulVec_finePointSourceSolution
    d L j mass a z sourceEndpoint domain.fine domain.stabilized domain.row]
  apply Finset.sum_congr rfl
  intro m _
  change Complex.exp _ * Complex.exp _ = Complex.exp _
  rw [← Complex.exp_add]
  congr 1
  ring

end
end YangMills.RG

#print axioms YangMills.RG.neumannAliasPrecision_finePointSource_readout
