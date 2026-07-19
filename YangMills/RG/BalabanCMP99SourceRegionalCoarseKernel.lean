/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalCoarseCovarianceTransition

/-!
# Physical fine/coarse kernel geometry for one CMP99 averaging step

Coarse sites are represented by the canonical lower corner of their physical
`M`-block.  This puts fine-to-coarse, coarse-to-fine and coarse-to-coarse
kernels in the same ambient fine-site metric.  The literal average and its
source-weighted adjoint then have range one block, with bounds independent of
the ambient periodic volume.
-/

namespace YangMills.RG

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- Canonical fine representative of an active regional coarse site. -/
def cmp99OmegaCoarseRepresentative
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r))) :
    FinBox 4 (M * (2 * Q)) :=
  blockBasepoint M (2 * Q) y.1

/-- Fine-to-coarse distance measured at the canonical block corner. -/
def cmp99OmegaFineToCoarseDist
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (target : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r)))
    (source : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r)) : ℕ :=
  finBoxDist (cmp99OmegaCoarseRepresentative (M := M) Seq r target) source.1

/-- Coarse-to-fine distance measured at the same canonical corner. -/
def cmp99OmegaCoarseToFineDist
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (target : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r))
    (source : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r))) : ℕ :=
  finBoxDist target.1 (cmp99OmegaCoarseRepresentative (M := M) Seq r source)

/-- Literal one-step averaging has fine-to-coarse range at most `M`. -/
theorem cmp99OmegaSourcePhysicalOneStepQ_finiteRange_M
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc) :
    FinitePiLpTypedFiniteRange
      (cmp99OmegaSourcePhysicalOneStepQ Seq r rho U)
      (cmp99OmegaFineToCoarseDist (M := M) Seq r) M := by
  intro source target v hfar
  let Omega := cmp99OmegaActiveGaugeRegion (M := M) Seq r
  let transport := cmp99SourceWeightedPhysicalTransport rho U
  have howner : blockSite M (2 * Q) source.1 ≠ target.1 := by
    intro h
    have hsame : blockSite M (2 * Q)
        (cmp99OmegaCoarseRepresentative (M := M) Seq r target) =
        blockSite M (2 * Q) source.1 := by
      unfold cmp99OmegaCoarseRepresentative
      rw [blockSite_blockBasepoint, h]
    have hnear := finBoxDist_le_of_same_block
      (cmp99OmegaCoarseRepresentative (M := M) Seq r target) source.1 hsame
    unfold cmp99OmegaFineToCoarseDist at hfar
    omega
  rw [cmp99OmegaSourcePhysicalOneStepQ,
    cmp99SourceTransportedBlockAverageCLM,
    cmp99TransportedBlockAverageCLM_apply]
  apply smul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro x hx
  have hxne : cmp99ActiveFineSiteOfBlock Omega target x ≠ source := by
    intro heq
    apply howner
    have hxblock : blockSite M (2 * Q) x.1 = target.1 :=
      (mem_blockOf M (2 * Q) target.1 x.1).mp x.2
    rw [← hxblock]
    exact (congrArg (fun z => blockSite M (2 * Q) z.1) heq).symm
  rw [singleFinitePiLp_of_ne v hxne]
  exact map_zero _

/-- The source-weighted adjoint has coarse-to-fine range at most `M`. -/
theorem cmp99OmegaSourcePhysicalOneStepWeightedAdjoint_finiteRange_M
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    FinitePiLpTypedFiniteRange
      (cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing).weightedAdjoint
      (cmp99OmegaCoarseToFineDist (M := M) Seq r) M := by
  intro source target v hfar
  let Omega := cmp99OmegaActiveGaugeRegion (M := M) Seq r
  let hOmega : Omega.BlockSaturated :=
    cmp99OmegaActiveGaugeRegion_blockSaturated (M := M) Seq r
  let transport := cmp99SourceWeightedPhysicalTransport rho U
  have howner : blockSite M (2 * Q) target.1 ≠ source.1 := by
    intro h
    have hsame : blockSite M (2 * Q) target.1 =
        blockSite M (2 * Q)
          (cmp99OmegaCoarseRepresentative (M := M) Seq r source) := by
      unfold cmp99OmegaCoarseRepresentative
      rw [blockSite_blockBasepoint, h]
    have hnear := finBoxDist_le_of_same_block target.1
      (cmp99OmegaCoarseRepresentative (M := M) Seq r source) hsame
    unfold cmp99OmegaCoarseToFineDist at hfar
    omega
  change cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega transport
      (singleFinitePiLp source v) target = 0
  rw [cmp99SourceTransportedBlockWeightedAdjointCLM,
    cmp99TransportedBlockSynthesisCLM_apply]
  have hne :
      (⟨blockSite M (2 * Q) target.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff
          (M := M) (N' := 2 * Q) Omega
          (blockSite M (2 * Q) target.1)).2
            (hOmega target.1 target.2)⟩ :
          ActiveGaugeRegion.Site
            (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q) Omega)) ≠ source := by
    intro h
    exact howner (congrArg Subtype.val h)
  rw [singleFinitePiLp_of_ne v hne, map_zero, smul_zero]

/-- The literal one-step average is contractive in counting norm. -/
theorem norm_cmp99OmegaSourcePhysicalOneStepQ_le_one
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing : ℝ} (hspacing : 0 < spacing) :
    ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U‖ ≤ 1 := by
  rw [← cmp99OmegaSourcePhysicalOneStepTower_Qprime Seq r rho U spacing]
  exact CMP99SourceWeightedRegionalTower.norm_Qprime_le_one_unconditional
    (cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing)
    hspacing.le (by
      have hMpos : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
      dsimp
      positivity) (by
      have hM : (1 : ℝ) ≤ M := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
      dsimp
      nlinarith)

/-- Counting norm of the literal one-step source-weighted adjoint. -/
theorem norm_cmp99OmegaSourcePhysicalOneStepWeightedAdjoint_le
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    ‖(cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing).weightedAdjoint‖
      ≤ (M : ℝ) ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro eta
  change ‖cmp99SourceTransportedBlockWeightedAdjointCLM
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r)
      (cmp99OmegaActiveGaugeRegion_blockSaturated (M := M) Seq r)
      (cmp99SourceWeightedPhysicalTransport rho U) eta‖ ≤
    (M : ℝ) ^ 2 * ‖eta‖
  have hsq := norm_cmp99SourceTransportedBlockWeightedAdjointCLM_sq
    (cmp99OmegaActiveGaugeRegion (M := M) Seq r)
    (cmp99OmegaActiveGaugeRegion_blockSaturated (M := M) Seq r)
    (cmp99SourceWeightedPhysicalTransport rho U) eta
  have hright : 0 ≤ (M : ℝ) ^ 2 * ‖eta‖ := by positivity
  apply le_of_sq_le_sq _ hright
  rw [hsq]
  ring_nf
  exact le_rfl

/-- Uniform entry budget for the physical one-step average. -/
theorem cmp99OmegaSourcePhysicalOneStepQ_kernelBound_one
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing : ℝ} (hspacing : 0 < spacing) :
    FinitePiLpTypedKernelBound
      (cmp99OmegaSourcePhysicalOneStepQ Seq r rho U) (fun _ _ => 1) := by
  intro source target v
  calc
    ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U
        (singleFinitePiLp source v) target‖ ≤
      ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U‖ * ‖v‖ :=
        finitePiLpTypedKernelBound_const_opNorm
          (cmp99OmegaSourcePhysicalOneStepQ Seq r rho U) source target v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right
      (norm_cmp99OmegaSourcePhysicalOneStepQ_le_one
        Seq r rho U hspacing) (norm_nonneg v)

/-- Uniform entry budget for the source-weighted adjoint. -/
theorem cmp99OmegaSourcePhysicalOneStepWeightedAdjoint_kernelBound
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    FinitePiLpTypedKernelBound
      (cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing).weightedAdjoint
      (fun _ _ => (M : ℝ) ^ 2) := by
  intro source target v
  calc
    ‖(cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing).weightedAdjoint
        (singleFinitePiLp source v) target‖ ≤
      ‖(cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing).weightedAdjoint‖ *
        ‖v‖ := finitePiLpTypedKernelBound_const_opNorm
          ((cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing).weightedAdjoint)
          source target v
    _ ≤ (M : ℝ) ^ 2 * ‖v‖ := mul_le_mul_of_nonneg_right
      (norm_cmp99OmegaSourcePhysicalOneStepWeightedAdjoint_le
        Seq r rho U spacing) (norm_nonneg v)

end

end YangMills.RG
