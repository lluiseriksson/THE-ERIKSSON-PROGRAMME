/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedKernel
import YangMills.RG.BalabanCMP99SourceLaplacianTransitionSupport
import YangMills.RG.BalabanCMP99SourcePi4Collar
import YangMills.RG.PhysicalShellLocalityQ

/-!
# Source-regional Combes--Thomas geometry for CMP99

The index metric is the literal periodic Chebyshev distance of the underlying
fine sites.  Restricting it to an active Dirichlet subtype preserves symmetry,
the triangle inequality, and the uniform ambient ball count.  Consequently
the Schur cardinality in the regional Combes--Thomas estimate is independent
of both the active region and the periodic volume.
-/

namespace YangMills.RG

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- Literal site metric on one active CMP99 Dirichlet region. -/
def cmp99OmegaSiteDist
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (x y : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r)) : ℕ :=
  finBoxDist x.1 y.1

theorem cmp99OmegaSiteDist_comm
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (x y : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r)) :
    cmp99OmegaSiteDist Seq r x y = cmp99OmegaSiteDist Seq r y x :=
  finBoxDist_comm x.1 y.1

@[simp] theorem cmp99OmegaSiteDist_self
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (x : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r)) :
    cmp99OmegaSiteDist Seq r x x = 0 :=
  finBoxDist_self x.1

theorem cmp99OmegaSiteDist_triangle
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (x y z : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r)) :
    cmp99OmegaSiteDist Seq r x z ≤
      cmp99OmegaSiteDist Seq r x y + cmp99OmegaSiteDist Seq r y z :=
  finBoxDist_triangle x.1 y.1 z.1

/-- Regional balls inject into the ambient site ball, so the source-region
cardinality never enters the Schur budget. -/
theorem cmp99OmegaSiteDist_ball_card_le
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (x : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r)) (R : ℕ) :
    (Finset.univ.filter (fun y => cmp99OmegaSiteDist Seq r x y ≤ R)).card ≤
      (2 * R + 1) ^ 4 := by
  classical
  let regional := Finset.univ.filter
    (fun y : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r) =>
        cmp99OmegaSiteDist Seq r x y ≤ R)
  let ambient := Finset.univ.filter
    (fun y : FinBox 4 (M * (2 * Q)) => finBoxDist x.1 y ≤ R)
  have hmaps : ∀ y ∈ regional, y.1 ∈ ambient := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hy.2⟩
  have hinj : Set.InjOn
      (fun y : ActiveGaugeRegion.Site
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r) => y.1)
      (regional : Set _) := by
    intro y _ z _ h
    exact Subtype.ext h
  calc
    (Finset.univ.filter (fun y =>
        cmp99OmegaSiteDist Seq r x y ≤ R)).card = regional.card := rfl
    _ ≤ ambient.card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ (2 * R + 1) ^ 4 :=
      finBoxDist_ball_card_le_two_mul_add_one_pow x.1 R

/-- Literal cross-region distance from a large-region source to a
small-region target. -/
def cmp99OmegaTransitionSiteDist
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (target : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionNextIndex r)))
    (source : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r))) : ℕ :=
  finBoxDist target.1 source.1

/-- Restricting a large-region coordinate probe whose site survives gives
the corresponding small-region coordinate probe exactly. -/
theorem cmp99OmegaTransitionRestriction_single_of_mem
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (source : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)))
    (hsource : source.1 ∈
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionNextIndex r)).sites)
    (v : SUNLieCoord Nc) :
    cmp99OmegaTransitionRestriction (M := M) Seq r
        (singleFinitePiLp source v) =
      singleFinitePiLp
        (⟨source.1, hsource⟩ : ActiveGaugeRegion.Site
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionNextIndex r))) v := by
  apply PiLp.ext
  intro target
  have hsourceLargeBlock : blockSite M (2 * Q) source.1 ∈
      Seq.regions (cmp99OmegaTransitionIndex r) :=
    (mem_cmp99OmegaActiveGaugeRegion_sites_iff
      (M := M) Seq (cmp99OmegaTransitionIndex r) source.1).mp source.2
  by_cases hval : target.1 = source.1
  · have htarget : target = ⟨source.1, hsource⟩ := Subtype.ext hval
    subst target
    simp [cmp99OmegaTransitionRestriction, restrictZeroCLM,
      extendZeroZeroCLM, hsourceLargeBlock, singleFinitePiLp]
  · have hne : target ≠
        (⟨source.1, hsource⟩ : ActiveGaugeRegion.Site
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionNextIndex r))) := by
      intro h
      exact hval (congrArg Subtype.val h)
    have htargetSmallBlock : blockSite M (2 * Q) target.1 ∈
        Seq.regions (cmp99OmegaTransitionNextIndex r) :=
      (mem_cmp99OmegaActiveGaugeRegion_sites_iff
        (M := M) Seq (cmp99OmegaTransitionNextIndex r) target.1).mp target.2
    have htargetLargeBlock : blockSite M (2 * Q) target.1 ∈
        Seq.regions (cmp99OmegaTransitionIndex r) :=
      cmp99OmegaTransition_region_subset Seq r htargetSmallBlock
    have hlargeNe :
        (⟨target.1,
          (mem_cmp99OmegaActiveGaugeRegion_sites_iff
            (M := M) Seq (cmp99OmegaTransitionIndex r) target.1).mpr
              htargetLargeBlock⟩ : ActiveGaugeRegion.Site
                (cmp99OmegaActiveGaugeRegion (M := M) Seq
                  (cmp99OmegaTransitionIndex r))) ≠ source := by
      intro h
      exact hval (congrArg Subtype.val h)
    simp [cmp99OmegaTransitionRestriction, restrictZeroCLM,
      extendZeroZeroCLM, htargetLargeBlock, singleFinitePiLp,
      hlargeNe, hne]

/-- A large-region coordinate probe outside the smaller region restricts to
zero. -/
theorem cmp99OmegaTransitionRestriction_single_of_not_mem
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (source : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)))
    (hsource : source.1 ∉
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionNextIndex r)).sites)
    (v : SUNLieCoord Nc) :
    cmp99OmegaTransitionRestriction (M := M) Seq r
        (singleFinitePiLp source v) = 0 := by
  apply PiLp.ext
  intro target
  have hval : target.1 ≠ source.1 := by
    intro h
    exact hsource (h ▸ target.2)
  have htargetSmallBlock : blockSite M (2 * Q) target.1 ∈
      Seq.regions (cmp99OmegaTransitionNextIndex r) :=
    (mem_cmp99OmegaActiveGaugeRegion_sites_iff
      (M := M) Seq (cmp99OmegaTransitionNextIndex r) target.1).mp target.2
  have htargetLargeBlock : blockSite M (2 * Q) target.1 ∈
      Seq.regions (cmp99OmegaTransitionIndex r) :=
    cmp99OmegaTransition_region_subset Seq r htargetSmallBlock
  have hlargeNe :
      (⟨target.1,
        (mem_cmp99OmegaActiveGaugeRegion_sites_iff
          (M := M) Seq (cmp99OmegaTransitionIndex r) target.1).mpr
            htargetLargeBlock⟩ : ActiveGaugeRegion.Site
              (cmp99OmegaActiveGaugeRegion (M := M) Seq
                (cmp99OmegaTransitionIndex r))) ≠ source := by
    intro h
    exact hval (congrArg Subtype.val h)
  simp [cmp99OmegaTransitionRestriction, restrictZeroCLM,
    extendZeroZeroCLM, htargetLargeBlock, singleFinitePiLp, hlargeNe]

/-- The literal regional covariant Laplacian has nearest-neighbour range in
the source site metric. -/
theorem cmp99OmegaSourceCovariantLaplacian_finiteRange_one
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) : ∀
      (source target : ActiveGaugeRegion.Site
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r))
      (v : SUNLieCoord Nc),
      1 < cmp99OmegaSiteDist Seq r target source →
      cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing
        (singleFinitePiLp source v) target = 0 := by
  intro source target v hfar
  let Omega := cmp99OmegaActiveGaugeRegion (M := M) Seq r
  let phi : CMP99OmegaDirichletZeroField (M := M) Seq r (SUNLieCoord Nc) :=
    singleFinitePiLp source v
  let ext : PhysicalGaugeZeroCochain 4 (M * (2 * Q)) Nc :=
    extendZeroZeroCLM Omega phi
  have hext_zero (y : FinBox 4 (M * (2 * Q))) (hy : y ≠ source.1) :
      ext y = 0 := by
    by_cases hyOmega : y ∈ Omega.sites
    · rw [show ext y = phi ⟨y, hyOmega⟩ by
          exact extendZeroZeroCLM_apply_of_mem Omega phi y hyOmega]
      apply singleFinitePiLp_of_ne
      intro hsub
      exact hy (congrArg Subtype.val hsub)
    · exact extendZeroZeroCLM_apply_of_not_mem Omega phi y hyOmega
  have htarget : target.1 ≠ source.1 := by
    intro h
    have hzero : cmp99OmegaSiteDist Seq r target source = 0 := by
      unfold cmp99OmegaSiteDist
      rw [h, finBoxDist_self]
    omega
  have hforward : ∀ i : Fin 4, target.1.shift i ≠ source.1 := by
    intro i h
    have hnear : cmp99OmegaSiteDist Seq r target source ≤ 1 := by
      unfold cmp99OmegaSiteDist
      rw [← h]
      exact finBoxDist_shift_le target.1 i
    omega
  have hback : ∀ i : Fin 4, target.1.shiftBack i ≠ source.1 := by
    intro i h
    have hnear : cmp99OmegaSiteDist Seq r target source ≤ 1 := by
      unfold cmp99OmegaSiteDist
      rw [← h]
      exact finBoxDist_shiftBack_le target.1 i
    omega
  have hambient :
      cmp99AmbientScaledCovariantLaplacian rho U spacing ext target.1 = 0 :=
    cmp99AmbientScaledCovariantLaplacian_apply_eq_zero rho U spacing ext target.1
      (hext_zero target.1 htarget)
      (fun i => hext_zero _ (hforward i))
      (fun i => hext_zero _ (hback i))
  rw [cmp99OmegaSourceCovariantLaplacian_apply_eq_dirichletCompression]
  exact hambient

/-- The physical averaging mass couples only fine sites owned by the same
`M`-block, hence has range at most `M` in the fine-site metric. -/
theorem cmp99OmegaSourcePhysicalOneStepQ_adjoint_comp_finiteRange_M
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc) : ∀
      (source target : ActiveGaugeRegion.Site
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r))
      (v : SUNLieCoord Nc),
      M < cmp99OmegaSiteDist Seq r target source →
      ((cmp99OmegaSourcePhysicalOneStepQ Seq r rho U).adjoint.comp
        (cmp99OmegaSourcePhysicalOneStepQ Seq r rho U))
          (singleFinitePiLp source v) target = 0 := by
  intro source target v hfar
  let Omega := cmp99OmegaActiveGaugeRegion (M := M) Seq r
  let hOmega : Omega.BlockSaturated :=
    cmp99OmegaActiveGaugeRegion_blockSaturated (M := M) Seq r
  let transport := cmp99SourceWeightedPhysicalTransport rho U
  let weight := cmp99SourceBlockAverageWeight M 4
  let Qop := cmp99TransportedBlockAverageCLM Omega weight transport
  have howner : blockSite M (2 * Q) target.1 ≠
      blockSite M (2 * Q) source.1 := by
    intro heq
    have hnear : cmp99OmegaSiteDist Seq r target source ≤ M - 1 := by
      unfold cmp99OmegaSiteDist
      exact finBoxDist_le_of_same_block target.1 source.1 heq
    omega
  have haverage : Qop (singleFinitePiLp source v)
      ⟨blockSite M (2 * Q) target.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff
          (M := M) (N' := 2 * Q) Omega
          (blockSite M (2 * Q) target.1)).2
            (hOmega target.1 target.2)⟩ = 0 := by
    rw [cmp99TransportedBlockAverageCLM_apply]
    simp only [smul_eq_zero]
    right
    apply Finset.sum_eq_zero
    intro x _hx
    have hxne : cmp99ActiveFineSiteOfBlock Omega
        ⟨blockSite M (2 * Q) target.1,
          (mem_cmp99ActiveCoarseRegion_sites_iff
            (M := M) (N' := 2 * Q) Omega
            (blockSite M (2 * Q) target.1)).2
              (hOmega target.1 target.2)⟩ x ≠ source := by
      intro heq
      apply howner
      have hxblock : blockSite M (2 * Q) x.1 =
          blockSite M (2 * Q) target.1 :=
        (mem_blockOf M (2 * Q) (blockSite M (2 * Q) target.1) x.1).mp x.2
      rw [← hxblock]
      exact congrArg (fun z => blockSite M (2 * Q) z.1) heq
    rw [singleFinitePiLp_of_ne v hxne]
    exact map_zero _
  change Qop.adjoint (Qop (singleFinitePiLp source v)) target = 0
  rw [← cmp99TransportedBlockSynthesisCLM_eq_adjoint
    Omega hOmega weight transport]
  rw [cmp99TransportedBlockSynthesisCLM_apply]
  change weight • (transport (blockSite M (2 * Q) target.1) target.1).symm
      (Qop (singleFinitePiLp source v)
        ⟨blockSite M (2 * Q) target.1,
          (mem_cmp99ActiveCoarseRegion_sites_iff
            (M := M) (N' := 2 * Q) Omega
            (blockSite M (2 * Q) target.1)).2
              (hOmega target.1 target.2)⟩) = 0
  rw [haverage, map_zero, smul_zero]

/-- The full literal source precision has range at most one physical
`M`-block: the Laplacian part has range one and the averaging mass has range
`M`. -/
theorem cmp99OmegaSourcePhysicalOneStepGaugePrecision_finiteRange_M
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing a : ℝ) : ∀
      (source target : ActiveGaugeRegion.Site
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r))
      (v : SUNLieCoord Nc),
      M < cmp99OmegaSiteDist Seq r target source →
      cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq r rho U spacing a
        (singleFinitePiLp source v) target = 0 := by
  intro source target v hfar
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hlap := cmp99OmegaSourceCovariantLaplacian_finiteRange_one
    Seq r rho U spacing source target v (lt_of_le_of_lt hM hfar)
  have hmass :=
    cmp99OmegaSourcePhysicalOneStepQ_adjoint_comp_finiteRange_M
      Seq r rho U source target v hfar
  rw [cmp99OmegaSourcePhysicalOneStepGaugePrecision,
    cmp99SourceGaugePrecision, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  change cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing
        (singleFinitePiLp source v) target +
      a • (((cmp99OmegaSourcePhysicalOneStepQ Seq r rho U).adjoint.comp
        (cmp99OmegaSourcePhysicalOneStepQ Seq r rho U))
          (singleFinitePiLp source v)) target = 0
  rw [hlap, hmass, smul_zero, add_zero]

/-- The genuinely rectangular consecutive precision defect has physical
range `M`; no equality transport between the two regional carrier types is
used. -/
theorem cmp99OmegaSourcePhysicalOneStepPrecisionDefect_finiteRange_M
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing a : ℝ) :
    FinitePiLpTypedFiniteRange
      (cmp99TypedPrecisionDefect
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionIndex r) rho U spacing a)
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionNextIndex r) rho U spacing a)
        (cmp99OmegaTransitionRestriction (M := M) Seq r))
      (cmp99OmegaTransitionSiteDist Seq r) M := by
  intro source target v hfar
  let largeIndex := cmp99OmegaTransitionIndex r
  let smallIndex := cmp99OmegaTransitionNextIndex r
  let OmegaLarge := cmp99OmegaActiveGaugeRegion (M := M) Seq largeIndex
  let OmegaSmall := cmp99OmegaActiveGaugeRegion (M := M) Seq smallIndex
  let Klarge := cmp99OmegaSourcePhysicalOneStepGaugePrecision
    Seq largeIndex rho U spacing a
  let Ksmall := cmp99OmegaSourcePhysicalOneStepGaugePrecision
    Seq smallIndex rho U spacing a
  let R := cmp99OmegaTransitionRestriction (M := M) Seq r (g := SUNLieCoord Nc)
  have htargetSmallBlock : blockSite M (2 * Q) target.1 ∈
      Seq.regions smallIndex :=
    (mem_cmp99OmegaActiveGaugeRegion_sites_iff
      (M := M) Seq smallIndex target.1).mp target.2
  have htargetLargeBlock : blockSite M (2 * Q) target.1 ∈
      Seq.regions largeIndex :=
    cmp99OmegaTransition_region_subset Seq r htargetSmallBlock
  let targetLarge : ActiveGaugeRegion.Site OmegaLarge :=
    ⟨target.1, (mem_cmp99OmegaActiveGaugeRegion_sites_iff
      (M := M) Seq largeIndex target.1).mpr htargetLargeBlock⟩
  have hlarge : Klarge (singleFinitePiLp source v) targetLarge = 0 := by
    exact cmp99OmegaSourcePhysicalOneStepGaugePrecision_finiteRange_M
      Seq largeIndex rho U spacing a source targetLarge v hfar
  have hfirst : R (Klarge (singleFinitePiLp source v)) target = 0 := by
    simp [R, cmp99OmegaTransitionRestriction, restrictZeroCLM,
      extendZeroZeroCLM, htargetLargeBlock, targetLarge, hlarge]
  have hsecond : Ksmall (R (singleFinitePiLp source v)) target = 0 := by
    by_cases hsource : source.1 ∈ OmegaSmall.sites
    · let sourceSmall : ActiveGaugeRegion.Site OmegaSmall := ⟨source.1, hsource⟩
      have hrestrict := cmp99OmegaTransitionRestriction_single_of_mem
        Seq r source hsource v
      have hsmall : Ksmall (singleFinitePiLp sourceSmall v) target = 0 := by
        exact cmp99OmegaSourcePhysicalOneStepGaugePrecision_finiteRange_M
          Seq smallIndex rho U spacing a sourceSmall target v hfar
      rw [hrestrict]
      exact hsmall
    · rw [cmp99OmegaTransitionRestriction_single_of_not_mem
        Seq r source hsource v, map_zero]
      rfl
  change R (Klarge (singleFinitePiLp source v)) target -
      Ksmall (R (singleFinitePiLp source v)) target = 0
  rw [hfirst, hsecond, sub_zero]

/-- Uniform entrywise bound for the rectangular consecutive precision
defect, derived from its source-generated volume-independent operator norm. -/
theorem cmp99OmegaSourcePhysicalOneStepPrecisionDefect_kernelBound
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing : ℝ} (hspacing : 0 < spacing) (a : ℝ) :
    FinitePiLpTypedKernelBound
      (cmp99TypedPrecisionDefect
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionIndex r) rho U spacing a)
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionNextIndex r) rho U spacing a)
        (cmp99OmegaTransitionRestriction (M := M) Seq r))
      (fun _ _ => 32 / spacing ^ 2) := by
  intro source target v
  have hbase := finitePiLpTypedKernelBound_const_opNorm
    (cmp99TypedPrecisionDefect
      (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
        (cmp99OmegaTransitionIndex r) rho U spacing a)
      (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
        (cmp99OmegaTransitionNextIndex r) rho U spacing a)
      (cmp99OmegaTransitionRestriction (M := M) Seq r)) source target v
  have hnorm := norm_cmp99OmegaSourcePhysicalOneStepPrecisionDefect_le
    Seq r rho U hspacing a
  calc
    _ ≤ ‖cmp99TypedPrecisionDefect
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionIndex r) rho U spacing a)
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionNextIndex r) rho U spacing a)
        (cmp99OmegaTransitionRestriction (M := M) Seq r)‖ * ‖v‖ := hbase
    _ ≤ (32 / spacing ^ 2) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)

/-- Uniform entrywise budget for the literal regional precision, obtained
from its already source-generated operator-norm bound. -/
theorem cmp99OmegaSourcePhysicalOneStepGaugePrecision_kernelBound
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing : ℝ} (hspacing : 0 < spacing) (a : ℝ) :
    FinitePiLpKernelBound
      (cmp99OmegaSourcePhysicalOneStepGaugePrecision
        Seq r rho U spacing a)
      (fun _ _ => cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound
        spacing a) := by
  intro source target v
  have hbase := finitePiLpKernelBound_const_opNorm
    (cmp99OmegaSourcePhysicalOneStepGaugePrecision
      Seq r rho U spacing a) source target v
  have hnorm := norm_cmp99OmegaSourcePhysicalOneStepGaugePrecision_le
    Seq r rho U (a := a) hspacing
  calc
    ‖cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq r rho U spacing a
        (singleFinitePiLp source v) target‖ ≤
      ‖cmp99OmegaSourcePhysicalOneStepGaugePrecision
        Seq r rho U spacing a‖ * ‖v‖ := hbase
    _ ≤ cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a * ‖v‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)

/-- Source-specific Combes--Thomas estimate for the exact regional one-step
Green operator.  Every constant is physical and uniform in the ambient
periodic volume; the only scalar premise is the displayed tilt budget. -/
theorem cmp99OmegaSourcePhysicalOneStepGreen_exponentialKernelBound
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a rate : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (hrate : 0 < rate)
    (hbudget :
      cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a *
          (Real.exp (rate * (M : ℝ)) - 1) *
          (((2 * M + 1) ^ 4 : ℕ) : ℝ) ≤
        cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a / 2) :
    FinitePiLpExponentialKernelBound
      (cmp99OmegaSourcePhysicalOneStepGreen Seq r rho U hspacing ha)
      (cmp99OmegaSiteDist Seq r)
      (2 / cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a)
      rate := by
  apply finitePiLpExponentialKernelBound_of_coercive
    (cmp99OmegaSiteDist Seq r)
    (cmp99OmegaSiteDist_comm Seq r)
    (cmp99OmegaSiteDist_triangle Seq r)
    (cmp99OmegaSiteDist_self Seq r)
    hrate
    (cmp99OmegaSourcePhysicalOneStepCoercivityConstant_pos ha)
    (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound_pos hspacing).le
    (R := M) (NR := (2 * M + 1) ^ 4)
    (fun x => cmp99OmegaSiteDist_ball_card_le Seq r x M)
    (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq r rho U spacing a)
    (cmp99OmegaSourcePhysicalOneStepGreen Seq r rho U hspacing ha)
  · intro source target v hfar
    exact cmp99OmegaSourcePhysicalOneStepGaugePrecision_finiteRange_M
      Seq r rho U spacing a source target v hfar
  · exact cmp99OmegaSourcePhysicalOneStepGaugePrecision_kernelBound
      Seq r rho U hspacing a
  · exact coercive_cmp99OmegaSourcePhysicalOneStepGaugePrecision
      Seq r rho U hspacing ha.le
  · exact cmp99OmegaSourcePhysicalOneStepPrecision_comp_green
      Seq r rho U hspacing ha
  · exact hbudget

/-- Canonical positive Combes--Thomas rate obtained by spending exactly the
available half-coercivity budget. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepCombesThomasRate
    (M : ℕ) (spacing a : ℝ) : ℝ :=
  Real.log
      (1 + cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a /
        (2 * cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a *
          (((2 * M + 1) ^ 4 : ℕ) : ℝ))) /
    (M : ℝ)

theorem cmp99OmegaSourcePhysicalOneStepCombesThomasRate_pos
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    0 < cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hB : 0 < cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a :=
    cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound_pos hspacing
  have hN : (0 : ℝ) < (((2 * M + 1) ^ 4 : ℕ) : ℝ) := by positivity
  have hc : 0 < cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a :=
    cmp99OmegaSourcePhysicalOneStepCoercivityConstant_pos ha
  unfold cmp99OmegaSourcePhysicalOneStepCombesThomasRate
  apply div_pos
  · apply Real.log_pos
    have : 0 <
        cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a /
          (2 * cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a *
            (((2 * M + 1) ^ 4 : ℕ) : ℝ)) := by positivity
    linarith
  · exact hM

theorem cmp99OmegaSourcePhysicalOneStepCombesThomasRate_budget
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a *
        (Real.exp
            (cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a *
              (M : ℝ)) - 1) *
        (((2 * M + 1) ^ 4 : ℕ) : ℝ) ≤
      cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a / 2 := by
  let B := cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a
  let c := cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a
  let N : ℝ := (((2 * M + 1) ^ 4 : ℕ) : ℝ)
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hB : 0 < B := cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound_pos hspacing
  have hN : 0 < N := by dsimp [N]; positivity
  have hc : 0 < c := cmp99OmegaSourcePhysicalOneStepCoercivityConstant_pos ha
  have harg : 0 < 1 + c / (2 * B * N) := by positivity
  have hrateMul :
      cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a * (M : ℝ) =
        Real.log (1 + c / (2 * B * N)) := by
    unfold cmp99OmegaSourcePhysicalOneStepCombesThomasRate
    dsimp [B, c, N]
    field_simp
  have hexp :
      Real.exp
          (cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a *
            (M : ℝ)) =
        1 + c / (2 * B * N) := by
    rw [hrateMul, Real.exp_log harg]
  change B *
      (Real.exp
          (cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a *
            (M : ℝ)) - 1) * N ≤ c / 2
  rw [hexp]
  have hBN : 2 * B * N ≠ 0 := by positivity
  field_simp
  linarith

/-- Unconditional physical regional Green decay at the canonical positive
rate; no caller-supplied tilt budget remains. -/
theorem cmp99OmegaSourcePhysicalOneStepGreen_canonicalExponentialKernelBound
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    FinitePiLpExponentialKernelBound
      (cmp99OmegaSourcePhysicalOneStepGreen Seq r rho U hspacing ha)
      (cmp99OmegaSiteDist Seq r)
      (2 / cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a)
      (cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a) :=
  cmp99OmegaSourcePhysicalOneStepGreen_exponentialKernelBound
    Seq r rho U hspacing ha
    (cmp99OmegaSourcePhysicalOneStepCombesThomasRate_pos hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepCombesThomasRate_budget hspacing ha)

end

end YangMills.RG
