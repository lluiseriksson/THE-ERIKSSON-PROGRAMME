/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq342SourceLocalizedGreenCertificate
import YangMills.RG.BalabanCMP99Eq389GeneratedMassPhysicalBound
import YangMills.RG.FinitePiLpBlockLocalizedSupAlgebra

/-!
# PRE-VALIDATION: source-localized generated-mass species of CMP99 (3.89)

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

This module applies the literal generated counting mass to an arbitrary field
supported in one source-localization block.  The generated terminal-fibre
relation is proved to preserve the exact source owner, so the normalized
counting-mass estimate consumes the source-facing Green value bound without a
probe expansion or an ambient cardinality loss.

The result is one physical third-species cell before the overlap-16 sum.  It
does not prove the complete CMP99 (3.89) estimate or the defect contraction.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq389GeneratedMassSourceAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

private instance instNeZeroEq389GeneratedMassSourceOwnerSide
    (K Q : ℕ) [NeZero K] [NeZero Q] :
    NeZero (2 * (K * Q)) :=
  ⟨(Nat.mul_pos (by omega)
    (Nat.mul_pos (NeZero.pos K) (NeZero.pos Q))).ne'⟩

/-- Kernel expansion of a scalar commutator after an arbitrary input field.
This is the field-valued analogue of the already sealed probe expansion, and
uses only linearity. -/
theorem finitePiLpScalarCommutator_smul_comp_apply_eq_sum
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ) (mass : ℝ)
    (T G : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (f : FinitePiLpField ι g) (target : ι) :
    ((finitePiLpScalarCommutator h (mass • T)).comp G) f target =
      ∑ source, (-mass) • T (singleFinitePiLp source
        ((h source - h target) • G f source)) target := by
  rw [ContinuousLinearMap.comp_apply,
    finitePiLpScalarCommutator_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro source _hsource
  have hsingle :
      singleFinitePiLp source ((h source - h target) • G f source) =
        (h source - h target) • singleFinitePiLp source (G f source) := by
    apply PiLp.ext
    intro x
    by_cases hx : x = source
    · subst x
      simp
    · rw [singleFinitePiLp_of_ne _ hx, PiLp.smul_apply,
        singleFinitePiLp_of_ne _ hx, smul_zero]
  rw [hsingle, map_smul]
  simp only [ContinuousLinearMap.smul_apply, PiLp.smul_apply]
  module

/-- One generated terminal fibre has one exact source-localization owner.
This is the source-scale counterpart of the coarser common-metric bridge. -/
theorem
    cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv_sourceLocalizationOwner_eq_of_sameTerminalBlock
    (depth : ℕ)
    (source target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)))
    (hsame : (cmp99SourceIteratedLiftActiveRegionChain (M := L)
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      (depth + 1)).SameTerminalBlock source target) :
    cmp99Eq389SourceLocalizationOwner L K Q depth
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth source) =
      cmp99Eq389SourceLocalizationOwner L K Q depth
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth target) := by
  have howner :=
    (cmp99SourceIteratedLift_sameTerminalBlock_iff
      (M := L)
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      (depth + 1) source target).1 hsame
  let hsize :=
    cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier L K Q depth
  have castFinVal {n m : ℕ} (h : n = m) (x : Fin n) :
      (cast (congrArg (fun k => Fin k) h) x).val = x.val := by
    subst h
    rfl
  funext i
  apply Fin.ext
  simp only [cmp99Eq389SourceLocalizationOwner,
    cmp99Eq389SourceLocalizationSiteEquiv, Equiv.cast_apply, blockSite_val,
    castFinVal]
  change ((hsize ▸ source.1) i).val / L ^ (depth + 1) =
    ((hsize ▸ target.1) i).val / L ^ (depth + 1)
  rw [finBox_cast_apply_val hsize source.1 i,
    finBox_cast_apply_val hsize target.1 i]
  exact congrArg Fin.val (congrFun howner i)

/-- Reindexed generated counting mass with arbitrary varying source values.
Only values on the actual terminal fibre are charged, and the exact one
surviving normalized block weight remains visible. -/
theorem cmp99SourceSeparatedGeneratedCountingMass_varying_le
    (hL : 2 ≤ L) (depth : ℕ) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (target : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc))
    (C : ℝ) (hC : 0 ≤ C)
    (hphi : ∀ source,
      (cmp99SourceIteratedLiftActiveRegionChain (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)).SameTerminalBlock source
          ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
            L K Q depth).symm target) →
      ‖phi (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
        L K Q depth source)‖ ≤ C) :
    (∑ source, ‖cmp99SourceSeparatedGeneratedCountingMass
        (L := L) (K := K) (Q := Q) hL depth rho spacing epsilon
        background chain fineSmall
        (singleFinitePiLp source (phi source)) target‖) ≤
      (cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) * C := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := L)
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  let T : ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)) (SUNLieCoord Nc) →L[ℝ]
    ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)) (SUNLieCoord Nc) :=
    regions.generatedCountingMass (by norm_num) hL rho spacing epsilon
      background chain fineSmall
  let phiActive : ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)) (SUNLieCoord Nc) :=
    WithLp.toLp 2 fun source => phi (e source)
  calc
    (∑ source, ‖cmp99SourceSeparatedGeneratedCountingMass
        (L := L) (K := K) (Q := Q) hL depth rho spacing epsilon
        background chain fineSmall
        (singleFinitePiLp source (phi source)) target‖) =
      ∑ source, ‖T
        (singleFinitePiLp source (phiActive source)) (e.symm target)‖ := by
        simpa only [cmp99SourceSeparatedGeneratedCountingMass, regions, T,
          phiActive, e, Equiv.apply_symm_apply] using
          (sum_norm_finitePiLpTypedKernelReindex_single_varying
            e e T phi target)
    _ ≤ (cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) * C := by
      apply cmp99SourceIteratedLift_sum_norm_generatedCountingMass_varying_le
        (Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth := depth + 1) (by norm_num) hL rho spacing epsilon background
        chain fineSmall (e.symm target) phiActive C hC
      intro source hsame
      simpa only [phiActive, e] using hphi source hsame

/-- The complete literal generated-mass cell obeys the source-localized
supremum estimate with its physical mass and normalized counting weight
visible in the amplitude. -/
theorem cmp99Eq389GeneratedMassRegionalCorrection_blockLocalizedSupBound
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 : ℝ)
    (C : CMP99Eq342SourceLocalizedGreenCertificate
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      depth Omega (matrixSUNAdjointModel Nc) U spacing A c hc hAcoer
      B0 delta0) :
    FinitePiLpTypedBlockLocalizedSupBound
      (ι := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (κ := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (β := FinBox 4 (2 * (K * Q)))
      (g := SUNLieCoord Nc)
      (cmp99Eq389GeneratedMassRegionalCorrection
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P hL depth spacing epsilon background chain fineSmall cell Omega
        A c hc hAcoer)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      finBoxDist
      (cmp99Eq389GeneratedMassSourceBudget
        (L := L) (K := K) P depth spacing epsilon B0
          (L ^ (depth + 1) : ℝ))
      delta0 := by
  let hcutoff : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℝ :=
    cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
  let G := cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer
  let T := cmp99SourceSeparatedGeneratedCountingMass
    (L := L) (K := K) (Q := Q) hL depth (matrixSUNAdjointModel Nc)
    spacing epsilon background chain fineSmall
  let mass := cmp99SourceGeneratedPhysicalMass
    4 L (depth + 1) spacing epsilon
  let slope : ℝ := (8 * P.derivBound) / (K : ℝ)
  let ell : ℝ := (L ^ (depth + 1) : ℝ)
  have hslope : 0 ≤ slope := by
    dsimp [slope]
    exact div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
      (Nat.cast_nonneg _)
  have hcutoff_le : ∀ source, ‖hcutoff source‖ ≤ 1 := by
    intro source
    exact
      (cmp99SourceSeparatedSignedLargeBlockSquarePartition
        (L := L) (K := K) (Q := Q) (depth := depth) P).norm_value_le_one
          cell source
  have hgreen : FinitePiLpTypedBlockLocalizedSupBound
      (G.comp (finitePiLpScalarMultiplier (g := SUNLieCoord Nc) hcutoff))
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      finBoxDist (B0 * ell ^ 2) delta0 := by
    have hbase : FinitePiLpTypedBlockLocalizedSupBound
        G
        (cmp99Eq389SourceLocalizationOwner L K Q depth)
        (cmp99Eq389SourceLocalizationOwner L K Q depth)
        finBoxDist (B0 * ell ^ 2) delta0 := by
      unfold G cmp99RegionalExtendedDirichletGreen
      apply finitePiLpTypedBlockLocalizedSupBound_extend_comp_restrictZeroCLM
      simpa [cmp99Eq342SourceLocalizedActiveOwner, ell] using C.value_bound
    exact finitePiLpTypedBlockLocalizedSupBound_comp_scalarMultiplier_right
      hcutoff G hcutoff_le hbase
  refine ⟨?_, C.delta0_pos, ?_⟩
  · unfold cmp99Eq389GeneratedMassSourceBudget
    exact mul_nonneg (abs_nonneg _)
      (mul_nonneg (pow_nonneg (cmp99SourceBlockAverageWeight_nonneg L 4) _)
        (mul_nonneg hslope
          (mul_nonneg C.B0_nonneg (sq_nonneg ell))))
  · intro owner f hf target
    let cutGreen : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
      G (finitePiLpScalarMultiplier (g := SUNLieCoord Nc) hcutoff f)
    let phi : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
      WithLp.toLp 2 fun source =>
        (hcutoff source - hcutoff target) • cutGreen source
    let decay := Real.exp (-(delta0 *
      (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth target)
        owner : ℝ)))
    let sourceValue := slope * ((B0 * ell ^ 2) * decay * finitePiLpSupNorm f)
    have hsourceValue : 0 ≤ sourceValue := by
      exact mul_nonneg hslope
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg C.B0_nonneg (sq_nonneg ell))
            (Real.exp_pos _).le)
          (finitePiLpSupNorm_nonneg f))
    have hphi : ∀ source,
        (cmp99SourceIteratedLiftActiveRegionChain (M := L)
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
          (depth + 1)).SameTerminalBlock source
            ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
              L K Q depth).symm target) →
        ‖phi (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth source)‖ ≤ sourceValue := by
      intro source hsame
      let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
      have hownerEq :
          cmp99Eq389SourceLocalizationOwner L K Q depth (e source) =
            cmp99Eq389SourceLocalizationOwner L K Q depth target := by
        have :=
          cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv_sourceLocalizationOwner_eq_of_sameTerminalBlock
            (L := L) (K := K) (Q := Q) depth source (e.symm target) hsame
        simpa only [e, Equiv.apply_symm_apply] using this
      have hG := hgreen.2.2 owner f hf (e source)
      rw [hownerEq] at hG
      have hdiff :=
        norm_cmp99SourceSeparatedSignedLargeBlockCutoff_sub_le_of_sameTerminalBlock
          (L := L) (K := K) (Q := Q) P depth cell source (e.symm target)
          hsame
      change ‖(hcutoff (e source) - hcutoff target) • cutGreen (e source)‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs]
      have hdiff' : |hcutoff (e source) - hcutoff target| ≤ slope := by
        simpa only [hcutoff, slope, e, Equiv.apply_symm_apply,
          Real.norm_eq_abs] using hdiff
      exact mul_le_mul hdiff' hG (norm_nonneg _) hslope
    have hmass := cmp99SourceSeparatedGeneratedCountingMass_varying_le
      (L := L) (K := K) (Q := Q) hL depth (matrixSUNAdjointModel Nc)
      spacing epsilon background chain fineSmall target phi sourceValue
      hsourceValue hphi
    have hexpand := finitePiLpScalarCommutator_smul_comp_apply_eq_sum
      hcutoff mass T G
      (finitePiLpScalarMultiplier (g := SUNLieCoord Nc) hcutoff f) target
    change ‖cmp99Eq389GeneratedMassRegionalCorrection
        (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
        chain fineSmall cell Omega A c hc hAcoer f target‖ ≤ _
    rw [cmp99Eq389GeneratedMassRegionalCorrection,
      ContinuousLinearMap.comp_apply,
      cmp99Eq389GeneratedMassAmbientCorrection]
    change ‖((finitePiLpScalarCommutator hcutoff (mass • T)).comp G)
      (finitePiLpScalarMultiplier (g := SUNLieCoord Nc) hcutoff f) target‖ ≤ _
    rw [hexpand]
    calc
      ‖∑ source, (-mass) • T (singleFinitePiLp source
          ((hcutoff source - hcutoff target) • cutGreen source)) target‖ ≤
          ∑ source, ‖(-mass) • T (singleFinitePiLp source
            ((hcutoff source - hcutoff target) • cutGreen source)) target‖ :=
        norm_sum_le _ _
      _ = |mass| * ∑ source, ‖T
          (singleFinitePiLp source (phi source)) target‖ := by
        simp only [phi, norm_smul, Real.norm_eq_abs, abs_neg,
          Finset.mul_sum]
      _ ≤ |mass| *
          ((cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) * sourceValue) :=
        mul_le_mul_of_nonneg_left hmass (abs_nonneg _)
      _ = cmp99Eq389GeneratedMassSourceBudget
            (L := L) (K := K) P depth spacing epsilon B0 ell *
          decay * finitePiLpSupNorm f := by
        unfold cmp99Eq389GeneratedMassSourceBudget sourceValue slope mass
        ring

end

end YangMills.RG
