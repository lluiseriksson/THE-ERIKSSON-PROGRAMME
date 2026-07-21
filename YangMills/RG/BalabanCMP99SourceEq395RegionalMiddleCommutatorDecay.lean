/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395MiddleGapPhysicalAdjoint

/-!
# Fixed-rate decay of the regional commutator in CMP99 (3.95)

This module treats the second term in the source-faithful splitting of the
grouped left defect.  It first identifies the regional middle with the
generated source operator sandwiched between physical restriction and zero
extension.  Its source decay then transfers to the ambient block field and
survives multiplication by the smooth cutoff on either side.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
/-- The generated regional middle in the ambient field is exactly the
source-reindexed generated middle sandwiched between physical restriction and
zero extension. -/
theorem generatedPhysicalCoarseCovarianceMiddleAmbient_eq_extend_onSource
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let Omega := D.operatorCoarseRegion hpi5 s
    D.generatedPhysicalCoarseCovarianceMiddleAmbient hpi5 s hM depth
        hspacing background budget fineSmall hsmall =
      (extendZeroZeroCLM Omega).comp
        ((cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
          background budget fineSmall hsmall).comp (restrictZeroCLM Omega)) := by
  dsimp only
  unfold generatedPhysicalCoarseCovarianceMiddleAmbient
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  let hT := regions.weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let hCoord := regions.terminalHilbertSpace_eq_coordinate (Nc := Nc)
  let hPhys := cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
    (Nc := Nc) (M := M) Omega (depth + 1)
  have hgenerated :=
    cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_transport_eq
      Omega hM depth hspacing background budget fineSmall hsmall
  have hsource := cmp99Eq395GeneratedPhysicalMiddleOnSource_eq_transport
    Omega hM depth hspacing background budget fineSmall hsmall
  have htrans := cmp99SourceTerminalCLMTransport_trans
    (hT.trans hCoord) (hT.trans hCoord)
    (hCoord.symm.trans hPhys) (hCoord.symm.trans hPhys) Middle
  rw [hgenerated] at htrans
  rw [hsource, htrans]
  congr

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
/-- The literal regional middle, extended to the ambient field, has the same
fixed-rate source decay.  Coordinates outside the physical region vanish
exactly on restriction or extension. -/
theorem generatedPhysicalCoarseCovarianceMiddleAmbient_exponentialKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let AD : CMP99Eq395AmbientOperator Q Nc :=
      D.generatedPhysicalCoarseCovarianceMiddleAmbient hpi5 s hM depth
        hspacing background budget fineSmall hsmall
    FinitePiLpTypedExponentialKernelBound AD
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4) := by
  dsimp only
  let Omega := D.operatorCoarseRegion hpi5 s
  let A := cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
    background budget fineSmall hsmall
  have hA := cmp99Eq395GeneratedPhysicalMiddleOnSource_exponentialKernelBound
    Omega hM depth hspacing background budget fineSmall hsmall
  rw [D.generatedPhysicalCoarseCovarianceMiddleAmbient_eq_extend_onSource]
  refine ⟨hA.1, hA.2.1, ?_⟩
  intro source target v
  by_cases hsource : source ∈ Omega.sites
  · by_cases htarget : target ∈ Omega.sites
    · let sourceOmega : ActiveGaugeRegion.Site Omega := ⟨source, hsource⟩
      let targetOmega : ActiveGaugeRegion.Site Omega := ⟨target, htarget⟩
      have hrestrict :
          restrictZeroCLM Omega (singleFinitePiLp source v) =
            singleFinitePiLp sourceOmega v := by
        apply PiLp.ext
        intro x
        by_cases hx : x.1 = source
        · have heq : x = sourceOmega := Subtype.ext hx
          subst x
          simp [restrictZeroCLM, sourceOmega]
        · have hne : x ≠ sourceOmega := by
            intro heq
            exact hx (congrArg Subtype.val heq)
          simp [restrictZeroCLM, singleFinitePiLp, hx, hne]
      change ‖extendZeroZeroCLM Omega
          (A (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
      rw [extendZeroZeroCLM_apply_of_mem Omega _ target htarget, hrestrict]
      change ‖A (singleFinitePiLp sourceOmega v) targetOmega‖ ≤ _
      exact hA.2.2 sourceOmega targetOmega v
    · change ‖extendZeroZeroCLM Omega
          (A (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
      simp [extendZeroZeroCLM, htarget]
      exact mul_nonneg
        (mul_nonneg hA.1 (Real.exp_pos _).le) (norm_nonneg v)
  · have hrestrict : restrictZeroCLM Omega
        (singleFinitePiLp source v) = 0 := by
      apply PiLp.ext
      intro x
      have hne : x.1 ≠ source := by
        intro heq
        apply hsource
        simpa [heq] using x.2
      simp [restrictZeroCLM, singleFinitePiLp, hne]
    change ‖extendZeroZeroCLM Omega
        (A (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
    rw [hrestrict]
    simp only [map_zero, PiLp.zero_apply, norm_zero]
    exact mul_nonneg
      (mul_nonneg hA.1 (Real.exp_pos _).le) (norm_nonneg v)

/-- The literal regional commutator with the physical smooth cutoff has
fixed-rate decay and costs exactly twice the regional-middle amplitude. -/
theorem cmp99Eq395PhysicalMiddle_smoothCommutator_exponentialKernelBound
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall cell
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
    FinitePiLpTypedExponentialKernelBound (AD.comp h - h.comp AD)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (2 * cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4) := by
  dsimp only
  let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  let f := fun block : FinBox 4 (2 * Q) =>
    (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block
  have hf : ∀ block, ‖f block‖ ≤ 1 := fun block =>
    (cmp95SourcePeriodicCoarseSquarePartition P Q).norm_value_le_one cell block
  have hAD : FinitePiLpTypedExponentialKernelBound AD
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4) := by
    simpa [AD, cmp99Eq395PhysicalMiddle] using
      ((D cell).generatedPhysicalCoarseCovarianceMiddleAmbient_exponentialKernelBound
        (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background budget
        fineSmall hsmall)
  have hright := finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_right
    f AD hf hAD
  have hleft := finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_left
    f AD hf hAD
  have hsum := finitePiLpTypedExponentialKernelBound_add hright
    (finitePiLpTypedExponentialKernelBound_neg hleft)
  simpa [AD, f, cmp99Eq395PhysicalSmoothMultiplier, sub_eq_add_neg,
    two_mul] using hsum

set_option maxHeartbeats 1000000 in
/-- The complete grouped left defect in the physical cell identity has a
single fixed-rate, volume-independent exponential bound.  Its two amplitudes
are the rectangular gluing defect and the regional commutator respectively.
-/
theorem cmp99Eq395PhysicalGroupedLeftDefect_exponentialKernelBound
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    let L : CMP99Eq395AmbientOperator Q Nc :=
      cmp99Eq395PhysicalGroupedLeftDefect D hpi5 P hM depth hspacing
        background budget fineSmall hsmall cell
    FinitePiLpTypedExponentialKernelBound
      L
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude
          M depth spacing epsilon +
        2 * cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 12) := by
  dsimp only
  let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
    budget fineSmall hsmall
  let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  have hgap := cmp99Eq395PhysicalMiddleGap_comp_smoothMultiplier_exponentialKernelBound
    D hpi5 P hM depth hspacing background budget fineSmall hsmall cell
  have hpow : 1 ≤ M ^ (depth + 1) := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (NeZero.ne M))
  have hgapWeak := finitePiLpTypedExponentialKernelBound_mono_dist
    (dist' := (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ))
    (fun target source => by
      rw [finBoxDist_comm]
      simpa using Nat.mul_le_mul_right (finBoxDist source target) hpow)
    hgap
  have hcomm := cmp99Eq395PhysicalMiddle_smoothCommutator_exponentialKernelBound
    D hpi5 P hM depth hspacing background budget fineSmall hsmall cell
  have hcommWeak := finitePiLpTypedExponentialKernelBound_mono_rate
    hgap.2.1 (by nlinarith [hcomm.2.1]) hcomm
  rw [cmp99Eq395PhysicalGroupedLeftDefect_eq_middleGap_add_commutator]
  exact finitePiLpTypedExponentialKernelBound_add hgapWeak hcommWeak

end CMP99SourceDependentOmegaGeometry

end
