import YangMills.RG.FinitePiLpOwnerWeightedSupKernelAlgebra

/-!
# PRE-VALIDATION: owner-kernel composition for localized supremum bounds

This source is present, its `.olean` has not yet been materialized, and its
result has not yet been verified by the Lean compiler.

A block-localized left factor and an explicit owner-fibre coefficient matrix
for a right factor compose once their literal owner convolution is bounded.
The theorem does not hide any physical radius, overlap, or cardinality input.
-/

namespace YangMills.RG

noncomputable section

/-- Draft C6c.4d7b.  A block-localized left factor and an explicit
owner-fibre coefficient matrix for the right factor give a block-localized
composition once their literal owner convolution is bounded pointwise.

This lemma does not manufacture a radius estimate or a cardinality bound;
those remain visible in the physical caller. -/
theorem finitePiLpTypedBlockLocalizedSupBound_comp_of_ownerKernel
    {ι κ ν β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ]
    [Fintype ν] [Nonempty ν]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (Left : FinitePiLpField κ g →L[ℝ] FinitePiLpField ν g)
    (Right : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (sourceOwner : ι → β) (middleOwner : κ → β) (targetOwner : ν → β)
    (dist : β → β → ℕ)
    (rightCoefficient : β → β → ℝ)
    {A B rate : ℝ}
    (hLeft : FinitePiLpTypedBlockLocalizedSupBound Left
      middleOwner targetOwner dist A rate)
    (hRight : FinitePiLpTypedOwnerSupKernelBound Right
      sourceOwner middleOwner rightCoefficient)
    (hB : 0 ≤ B)
    (hconvolution : ∀ targetBlock sourceBlock,
      finiteOwnerKernelConvolution
          (finiteOwnerExponentialCoefficient dist A rate)
          rightCoefficient targetBlock sourceBlock ≤
        B * Real.exp (-(rate * (dist targetBlock sourceBlock : ℝ)))) :
    FinitePiLpTypedBlockLocalizedSupBound (Left.comp Right)
      sourceOwner targetOwner dist B rate := by
  classical
  have hLeftKernel := finitePiLpTypedOwnerSupKernelBound_of_blockLocalized
    Left middleOwner targetOwner dist hLeft
  have hcomp := finitePiLpTypedOwnerSupKernelBound_comp hLeftKernel hRight
  refine ⟨hB, hLeft.2.1, ?_⟩
  intro sourceBlock f hf target
  have howner := hcomp.2 sourceBlock f hf (targetOwner target)
  have hpoint := norm_apply_le_finitePiLpSupNorm
    (finitePiLpOwnerPart targetOwner (targetOwner target)
      ((Left.comp Right) f)) target
  rw [finitePiLpOwnerPart_apply, if_pos rfl] at hpoint
  calc
    ‖(Left.comp Right) f target‖ ≤
        finitePiLpSupNorm
          (finitePiLpOwnerPart targetOwner (targetOwner target)
            ((Left.comp Right) f)) := hpoint
    _ ≤ finiteOwnerKernelConvolution
          (finiteOwnerExponentialCoefficient dist A rate)
          rightCoefficient (targetOwner target) sourceBlock *
        finitePiLpSupNorm f := howner
    _ ≤ (B * Real.exp (-(rate *
          (dist (targetOwner target) sourceBlock : ℝ)))) *
        finitePiLpSupNorm f :=
      mul_le_mul_of_nonneg_right
        (hconvolution (targetOwner target) sourceBlock)
        (finitePiLpSupNorm_nonneg f)

end

end YangMills.RG
