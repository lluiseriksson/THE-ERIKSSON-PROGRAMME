/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq342RegionalGreenCertificate
import YangMills.RG.BalabanCMP99SourceGeneratedCountingMassVaryingOutput
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary

/-!
# PRE-VALIDATION: common Green metric for the generated mass fibre

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

The normalized third species of CMP99 (3.88)--(3.89) sums Green values which
vary over one terminal fibre of the literal generated `Q'` tower.  The Green
metric groups sites at the larger separated scale `K * L^r`.  This file proves
that equality of the finer `L^r` terminal owner implies equality of that
larger Green owner, with no exponential loss.

It also records the exact sum-level transport of varying coordinate probes
through an isometric kernel reindexing.  No Green estimate, cutoff difference,
mass coefficient, cell sum or contraction is introduced here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe u v u' v' w

/-- A varying-coordinate fixed-output norm sum is invariant under exact
isometric reindexing of both kernel legs. -/
theorem sum_norm_finitePiLpTypedKernelReindex_single_varying
    {ι : Type u} {κ : Type v} {ι' : Type u'} {κ' : Type v'} {g : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    [Fintype ι'] [DecidableEq ι'] [Fintype κ']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (sourceEquiv : ι ≃ ι') (targetEquiv : κ ≃ κ')
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (phi : ι' → g) (target : κ') :
    (∑ source : ι',
        ‖finitePiLpTypedKernelReindex sourceEquiv targetEquiv T
          (singleFinitePiLp source (phi source)) target‖) =
      ∑ source : ι,
        ‖T (singleFinitePiLp source (phi (sourceEquiv source)))
          (targetEquiv.symm target)‖ := by
  classical
  let sourceBack :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g
      sourceEquiv.symm).toContinuousLinearEquiv
  let targetMap :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g
      targetEquiv).toContinuousLinearEquiv
  calc
    (∑ source : ι',
        ‖finitePiLpTypedKernelReindex sourceEquiv targetEquiv T
          (singleFinitePiLp source (phi source)) target‖) =
      ∑ source : ι,
        ‖finitePiLpTypedKernelReindex sourceEquiv targetEquiv T
          (singleFinitePiLp (sourceEquiv source)
            (phi (sourceEquiv source))) target‖ := by
        exact (Equiv.sum_comp sourceEquiv fun source =>
          ‖finitePiLpTypedKernelReindex sourceEquiv targetEquiv T
            (singleFinitePiLp source (phi source)) target‖).symm
    _ = ∑ source : ι,
        ‖T (singleFinitePiLp source (phi (sourceEquiv source)))
          (targetEquiv.symm target)‖ := by
      apply Finset.sum_congr rfl
      intro source _hsource
      have hsingle : sourceBack
          (singleFinitePiLp (sourceEquiv source)
            (phi (sourceEquiv source))) =
          singleFinitePiLp source (phi (sourceEquiv source)) := by
        rw [singleFinitePiLp_eq_toLp_single,
          singleFinitePiLp_eq_toLp_single]
        simpa only [sourceBack, Equiv.symm_apply_apply] using
          (LinearIsometryEquiv.piLpCongrLeft_single
            (p := (2 : ENNReal)) (𝕜 := ℝ) sourceEquiv.symm
            (sourceEquiv source) (phi (sourceEquiv source)))
      change ‖targetMap
          (T (sourceBack (singleFinitePiLp (sourceEquiv source)
            (phi (sourceEquiv source))))) target‖ = _
      rw [hsingle]
      rfl

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq389GeneratedMassSeparatedBlockSide
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth) :=
  ⟨by
    unfold cmp99SourceSeparatedLargeBlockSide
    exact (Nat.mul_pos (NeZero.pos K)
      (pow_pos (NeZero.pos L) (depth + 1))).ne'⟩

/-- One generated `L^(depth+1)` terminal fibre lies inside one literal
`K * L^(depth+1)` Green block after the separated ambient reindexing. -/
theorem
    cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv_blockSite_eq_of_sameTerminalBlock
    (depth : ℕ)
    (source target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)))
    (hsame : (cmp99SourceIteratedLiftActiveRegionChain (M := L)
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      (depth + 1)).SameTerminalBlock source target) :
    blockSite (cmp99SourceSeparatedLargeBlockSide L K depth) (2 * Q)
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth source) =
      blockSite (cmp99SourceSeparatedLargeBlockSide L K depth) (2 * Q)
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth target) := by
  have howner :=
    (cmp99SourceIteratedLift_sameTerminalBlock_iff
      (M := L)
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      (depth + 1) source target).1 hsame
  let hsize :=
    cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier L K Q depth
  funext i
  apply Fin.ext
  change ((hsize ▸ source.1) i).val /
      (K * L ^ (depth + 1)) =
    ((hsize ▸ target.1) i).val /
      (K * L ^ (depth + 1))
  rw [finBox_cast_apply_val hsize source.1 i,
    finBox_cast_apply_val hsize target.1 i]
  have hi : (source.1 i).val / L ^ (depth + 1) =
      (target.1 i).val / L ^ (depth + 1) := by
    exact congrArg Fin.val (congrFun howner i)
  calc
    (source.1 i).val / (K * L ^ (depth + 1)) =
        (source.1 i).val / (L ^ (depth + 1) * K) := by
      simpa only [Nat.mul_comm]
    _ = ((source.1 i).val / L ^ (depth + 1)) / K := by
      rw [Nat.div_div_eq_div_mul]
    _ = ((target.1 i).val / L ^ (depth + 1)) / K := by rw [hi]
    _ = (target.1 i).val / (L ^ (depth + 1) * K) := by
      rw [Nat.div_div_eq_div_mul]
    _ = (target.1 i).val / (K * L ^ (depth + 1)) := by
      simpa only [Nat.mul_comm]

/-- The literal CMP99 (3.42) block metric is exactly constant in its output
coordinate across one generated terminal fibre. -/
theorem cmp99Eq342RescaledBlockDist_sourceSeparated_eq_of_sameTerminalBlock
    (depth : ℕ)
    (source target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)))
    (probe : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (hsame : (cmp99SourceIteratedLiftActiveRegionChain (M := L)
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      (depth + 1)).SameTerminalBlock source target) :
    cmp99Eq342RescaledBlockDist
        (cmp99SourceSeparatedLargeBlockSide L K depth) Q
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth source) probe =
      cmp99Eq342RescaledBlockDist
        (cmp99SourceSeparatedLargeBlockSide L K depth) Q
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth target) probe := by
  unfold cmp99Eq342RescaledBlockDist
  rw [cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv_blockSite_eq_of_sameTerminalBlock
    (L := L) (K := K) (Q := Q) depth source target hsame]

end

end YangMills.RG
