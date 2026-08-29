import YangMills.RG.FinitePiLpTypedKernelDistanceRescaling
import YangMills.RG.BalabanCMP99SourceLocalizationOwnerDistanceBridge

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Exact fine-to-owner decay rescaling on the C6d source carrier

This specializes the algebraic distance-rescaling lemma to the literal C6d
source-separated carrier and the already sealed source-localization owner.
The boundary payment remains exactly `2 * (ell - 1)` and the output rate is
exactly `ell * rate`, where `ell = L^(depth+1)`.

The theorem still accepts an already proved kernel bound.  It does not choose
a Green, identify two inverses, construct any of the four CMP99 (3.42)
actions, prove uniform `B0`/`delta0`, attain window 15, move `20/41`, or
inhabit `TermSource`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc depth : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The literal fine-site decay on a C6d source region transports to the
source-localization owner metric with the exact block-boundary payment. -/
theorem cmp99Eq360C6dSourceSeparated_exponentialKernelBound_rescaleOwner
    (OmegaSource : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    {C : ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc)}
    {A rate : ℝ}
    (hC : FinitePiLpExponentialKernelBound C
      (fun target source : ActiveGaugeRegion.Site OmegaSource =>
        finBoxDist target.1 source.1) A rate) :
    let ell := L ^ (depth + 1)
    FinitePiLpExponentialKernelBound C
      (fun target source : ActiveGaugeRegion.Site OmegaSource =>
        finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth target.1)
          (cmp99Eq389SourceLocalizationOwner L K Q depth source.1))
      (A * Real.exp (rate * (2 * (ell - 1) : ℕ)))
      ((ell : ℝ) * rate) := by
  dsimp only
  apply finitePiLpTypedExponentialKernelBound_rescale_dist
      (ell := L ^ (depth + 1))
      (boundary := 2 * (L ^ (depth + 1) - 1))
  · exact pow_pos (NeZero.pos L) (depth + 1)
  · intro target source
    exact cmp99Eq389SourceLocalizationOwner_mul_dist_le_fineDist_add_boundary
      depth target.1 source.1
  · exact hC

end

end YangMills.RG
