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

/-- Coarse metric in physical fine-lattice units. -/
def cmp99OmegaCoarseDist
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (target source : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r))) : ℕ :=
  finBoxDist (cmp99OmegaCoarseRepresentative (M := M) Seq r target)
    (cmp99OmegaCoarseRepresentative (M := M) Seq r source)

/-- Cross-region coarse metric for a consecutive transition. -/
def cmp99OmegaCoarseTransitionDist
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (target : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r))))
    (source : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionIndex r)))) : ℕ :=
  finBoxDist
    (cmp99OmegaCoarseRepresentative (M := M) Seq
      (cmp99OmegaTransitionNextIndex r) target)
    (cmp99OmegaCoarseRepresentative (M := M) Seq
      (cmp99OmegaTransitionIndex r) source)

/-- Distance from a large-region fine source to a small-region coarse
target, used before the final weighted-adjoint composition. -/
def cmp99OmegaCoarseToTransitionFineDist
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (target : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r))))
    (source : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r))) : ℕ :=
  finBoxDist
    (cmp99OmegaCoarseRepresentative (M := M) Seq
      (cmp99OmegaTransitionNextIndex r) target) source.1

/-- The canonical representative belongs to its active fine region. -/
def cmp99OmegaCoarseRepresentativeSite
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r))) :
    ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r) :=
  ⟨cmp99OmegaCoarseRepresentative (M := M) Seq r y,
    (mem_cmp99ActiveCoarseRegion_sites_iff
      (M := M) (N' := 2 * Q)
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r) y.1).mp y.2
        ((mem_blockOf M (2 * Q) y.1
          (cmp99OmegaCoarseRepresentative (M := M) Seq r y)).mpr (by
            unfold cmp99OmegaCoarseRepresentative
            exact blockSite_blockBasepoint M (2 * Q) y.1))⟩

@[simp] theorem cmp99OmegaCoarseRepresentativeSite_val
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r))) :
    (cmp99OmegaCoarseRepresentativeSite (M := M) Seq r y).1 =
      cmp99OmegaCoarseRepresentative (M := M) Seq r y := rfl

/-- Distinct active coarse blocks have distinct canonical fine
representatives. -/
theorem cmp99OmegaCoarseRepresentativeSite_injective
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) :
    Function.Injective
      (cmp99OmegaCoarseRepresentativeSite (M := M) Seq r) := by
  intro y z h
  apply Subtype.ext
  have hval := congrArg (fun q => blockSite M (2 * Q) q.1) h
  simpa [cmp99OmegaCoarseRepresentativeSite,
    cmp99OmegaCoarseRepresentative] using hval

/-- A coarse exponential row sum injects into the corresponding fine-site
row sum.  Hence its constant is independent of the number of active coarse
blocks. -/
theorem cmp99OmegaCoarseDist_exp_sum_le
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (target : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r)))
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ∑ source : ActiveGaugeRegion.Site
        (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r)),
      Real.exp (-(sigma *
        (cmp99OmegaCoarseDist (M := M) Seq r target source : ℝ))) ≤
      cmp99OmegaSiteExpSumBound sigma := by
  classical
  let rep := cmp99OmegaCoarseRepresentativeSite (M := M) Seq r
  let f : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r) → ℝ := fun source =>
    Real.exp (-(sigma *
      (cmp99OmegaSiteDist Seq r (rep target) source : ℝ)))
  have hinj : Function.Injective rep :=
    cmp99OmegaCoarseRepresentativeSite_injective (M := M) Seq r
  calc
    ∑ source, Real.exp (-(sigma *
        (cmp99OmegaCoarseDist (M := M) Seq r target source : ℝ))) =
      ∑ source, f (rep source) := by
        apply Finset.sum_congr rfl
        intro source _
        rfl
    _ = ∑ source ∈ Finset.univ.image rep, f source := by
      rw [Finset.sum_image hinj.injOn]
    _ ≤ ∑ source, f source := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _)
        (fun _ _ _ => (Real.exp_pos _).le)
    _ ≤ cmp99OmegaSiteExpSumBound sigma :=
      cmp99OmegaSiteDist_exp_sum_le Seq r (rep target) hsigma

/-- Uniform exponential row sum centred at a coarse block representative. -/
theorem cmp99OmegaFineToCoarseDist_exp_sum_le
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (target : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r)))
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ∑ middle : ActiveGaugeRegion.Site
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r),
      Real.exp (-(sigma *
        (cmp99OmegaFineToCoarseDist (M := M) Seq r target middle : ℝ))) ≤
      cmp99OmegaSiteExpSumBound sigma := by
  simpa [cmp99OmegaFineToCoarseDist, cmp99OmegaSiteDist] using
    cmp99OmegaSiteDist_exp_sum_le Seq r
      (cmp99OmegaCoarseRepresentativeSite (M := M) Seq r target) hsigma

/-- The small-region representative, viewed in the consecutive large
region. -/
def cmp99OmegaCoarseTransitionRepresentativeLarge
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (target : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r)))) :
    ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)) :=
  let smallSite := cmp99OmegaCoarseRepresentativeSite (M := M) Seq
    (cmp99OmegaTransitionNextIndex r) target
  ⟨smallSite.1,
    (mem_cmp99OmegaActiveGaugeRegion_sites_iff
      (M := M) Seq (cmp99OmegaTransitionIndex r) smallSite.1).mpr
      (cmp99OmegaTransition_region_subset Seq r
        ((mem_cmp99OmegaActiveGaugeRegion_sites_iff
          (M := M) Seq (cmp99OmegaTransitionNextIndex r) smallSite.1).mp
            smallSite.2))⟩

/-- Uniform large-region row sum centred at a small coarse target. -/
theorem cmp99OmegaCoarseTransitionFine_exp_sum_le
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (target : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r))))
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ∑ middle : ActiveGaugeRegion.Site
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionIndex r)),
      Real.exp (-(sigma * (finBoxDist
        (cmp99OmegaCoarseRepresentative (M := M) Seq
          (cmp99OmegaTransitionNextIndex r) target) middle.1 : ℝ))) ≤
      cmp99OmegaSiteExpSumBound sigma := by
  simpa [cmp99OmegaSiteDist,
    cmp99OmegaCoarseTransitionRepresentativeLarge,
    cmp99OmegaCoarseRepresentativeSite] using
      cmp99OmegaSiteDist_exp_sum_le Seq (cmp99OmegaTransitionIndex r)
        (cmp99OmegaCoarseTransitionRepresentativeLarge
          (M := M) Seq r target) hsigma

/-- A cross-region coarse row sum injects into the corresponding large-region
fine-site row sum. -/
theorem cmp99OmegaCoarseTransitionDist_exp_sum_le
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (target : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r))))
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ∑ source : ActiveGaugeRegion.Site
        (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionIndex r))),
      Real.exp (-(sigma *
        (cmp99OmegaCoarseTransitionDist (M := M) Seq r target source : ℝ))) ≤
      cmp99OmegaSiteExpSumBound sigma := by
  classical
  let largeIndex := cmp99OmegaTransitionIndex r
  let rep := cmp99OmegaCoarseRepresentativeSite (M := M) Seq largeIndex
  let center := cmp99OmegaCoarseTransitionRepresentativeLarge (M := M) Seq r target
  let f : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq largeIndex) → ℝ := fun source =>
    Real.exp (-(sigma *
      (cmp99OmegaSiteDist Seq largeIndex center source : ℝ)))
  have hinj : Function.Injective rep :=
    cmp99OmegaCoarseRepresentativeSite_injective (M := M) Seq largeIndex
  calc
    ∑ source, Real.exp (-(sigma *
        (cmp99OmegaCoarseTransitionDist (M := M) Seq r target source : ℝ))) =
      ∑ source, f (rep source) := by
        apply Finset.sum_congr rfl
        intro source _
        rfl
    _ = ∑ source ∈ Finset.univ.image rep, f source := by
      rw [Finset.sum_image hinj.injOn]
    _ ≤ ∑ source, f source := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _)
        (fun _ _ _ => (Real.exp_pos _).le)
    _ ≤ cmp99OmegaSiteExpSumBound sigma := by
      exact cmp99OmegaSiteDist_exp_sum_le Seq largeIndex center hsigma

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
