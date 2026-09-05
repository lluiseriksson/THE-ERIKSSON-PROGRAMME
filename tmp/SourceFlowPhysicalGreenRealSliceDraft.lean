import YangMills.RG.FinitePiLpRealSliceFibreTransport
import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalGreenIdentification

/-!
# PRE-VALIDATION: literal physical source-flow Green on the real slice

Source present; .olean not materialized; result not compiler-verified.
This draft is outside the promoted F5 cold checkpoint and outside the root.
It depends on the F5 generic real-slice module cold-verified in ledger1118.
This physical specialization itself is not yet compiler-verified.

The operator in every endpoint is the internally constructed source-flow
Green. The carrier map is the existing physical Step-7b site permutation.
Only coordinate evaluation and single-fibre norms are transported: no outer
norm isometry, regional inverse identification, derivative bound or B0 is
asserted. No freely supplied Green family or dictionary equality is assumed.
-/

namespace YangMills.RG

open YangMills
noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The literal ambient complex Green restricts to the literal real Green.
The ordinary-function/PiLp coordinate transport stays explicit. -/
theorem cmp99SourceFlowPhysicalAmbientGreen_ofReal_draft
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc)) :
    cmp99SourceSeparatedSourceFlowFlatAmbientGreenComplex
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha
        (finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal phi)) =
      finitePiLpComplexOuterEquiv
        (finitePiLpComplexOfReal
          (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
            (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha phi)) := by
  exact finitePiLpCanonicalComplexificationOuterCLM_ofReal
    (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha) phi

/-- Named evaluation law for the existing physical carrier permutation;
there is no assertion about an outer norm. -/
theorem cmp99SourceFlowPhysicalStep7bFieldEquiv_apply_site_draft
    (depth : ℕ)
    (f : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      SUNLieComplexCoord Nc)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth f
        (cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth x) =
      f x := by
  simp [cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv,
    ContinuousLinearEquiv.piCongrLeft,
    Homeomorph.piCongrLeft, Equiv.piCongrLeft]

/-- Conjugating the literal complex Green and transporting a real input
gives the transported output of the literal real Green. -/
theorem cmp99SourceFlowPhysicalStep7bGreen_ofReal_draft
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc)) :
    cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha
        (cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
          (finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal phi))) =
      cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
        (finitePiLpComplexOuterEquiv
          (finitePiLpComplexOfReal
            (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
              (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha phi))) := by
  let U := cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
  change U
    (cmp99SourceSeparatedSourceFlowFlatAmbientGreenComplex
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha
      (U.symm (U (finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal phi))))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply,
    cmp99SourceFlowPhysicalAmbientGreen_ofReal_draft]

/-- The physical Step-7b output at the transported site has exactly the
whole real Lie-fibre norm, with no Lie-dimension or volume factor. -/
theorem norm_cmp99SourceFlowPhysicalStep7bGreen_ofReal_apply_draft
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc))
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ‖cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha
        (cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
          (finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal phi)))
        (cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth x)‖ =
      ‖cmp99SourceSeparatedSourceFlowFlatAmbientGreen
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha phi x‖ := by
  rw [cmp99SourceFlowPhysicalStep7bGreen_ofReal_draft,
    cmp99SourceFlowPhysicalStep7bFieldEquiv_apply_site_draft]
  exact norm_finitePiLpComplexOfReal_apply
    (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha phi) x

#print axioms cmp99SourceFlowPhysicalAmbientGreen_ofReal_draft
#print axioms cmp99SourceFlowPhysicalStep7bFieldEquiv_apply_site_draft
#print axioms cmp99SourceFlowPhysicalStep7bGreen_ofReal_draft
#print axioms norm_cmp99SourceFlowPhysicalStep7bGreen_ofReal_apply_draft

end
end YangMills.RG
