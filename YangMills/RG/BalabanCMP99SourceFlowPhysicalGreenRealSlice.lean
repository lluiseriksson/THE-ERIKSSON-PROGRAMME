import YangMills.RG.FinitePiLpRealSliceFibreTransport
import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalGreenIdentification

/-!
# BalabanCMP99SourceFlowPhysicalGreenRealSlice

Cold-verified and .olean materialized at source b2d5df8ad on 2026-09-05.
Downloaded evidence independently verified; see ledger Addendum 1122.
This selective seal changes provenance comments only, not the mathematics.
Its draft was checked at 59f9f522f3f731ac8a6270ac5c3ae719b1b201f6; see ledger 1119.
Only the explicit public-name map and audit placement are changed.

Literal internally constructed source-flow Green, exact site evaluation and single-fibre real-slice norms. No outer-norm isometry, regional inverse or derivative estimate.
No window-15 attainment or terminal field is claimed; 20/41, TermSource=0.
-/

namespace YangMills.RG

open YangMills
noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The literal ambient complex Green restricts to the literal real Green.
The ordinary-function/PiLp coordinate transport stays explicit. -/
theorem cmp99SourceFlowPhysicalAmbientGreen_ofReal
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
theorem cmp99SourceFlowPhysicalStep7bFieldEquiv_apply_site
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
theorem cmp99SourceFlowPhysicalStep7bGreen_ofReal
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
    cmp99SourceFlowPhysicalAmbientGreen_ofReal]

/-- The physical Step-7b output at the transported site has exactly the
whole real Lie-fibre norm, with no Lie-dimension or volume factor. -/
theorem norm_cmp99SourceFlowPhysicalStep7bGreen_ofReal_apply
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
  rw [cmp99SourceFlowPhysicalStep7bGreen_ofReal,
    cmp99SourceFlowPhysicalStep7bFieldEquiv_apply_site]
  exact norm_finitePiLpComplexOfReal_apply
    (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha phi) x


end
end YangMills.RG
