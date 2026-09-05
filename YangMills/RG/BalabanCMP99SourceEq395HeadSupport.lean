/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395HeadDictionary
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCHeadSupportWeightedRow

/-!
# Ambient support of the CMP99 equation (3.95) head

The exact dictionary identifies each ambient head with a zero-extended local
head.  Here we record its bilateral CMP95 source support directly on the
ambient coarse torus and derive a fixed-rate weighted row using only the
literal sixteen-block source cell.  No ambient-volume cardinality occurs.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/-- Support-sharp ambient weighted-row amplitude for one literal head. -/
noncomputable def cmp99Eq395PhysicalHeadWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
      M depth spacing epsilon * Real.exp rate * 16

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

/-- Generic finite-support weighted-row estimate used below.  Separating the
finite sum from the dependent CMP99 data keeps the physical specialization
small and transparent. -/
theorem finitePiLpTypedWeightedRowKernelBound_of_bilateral_finset_support
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (F : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (sourceDist : ι → ι → ℕ) (supported : Finset ι)
    (A rate : ℝ) (R K : ℕ)
    (hA : 0 ≤ A) (hrate : 0 < rate) (hnorm : ‖F‖ ≤ A)
    (hcard : supported.card ≤ K)
    (hdiam : ∀ target ∈ supported, ∀ source ∈ supported,
      sourceDist target source ≤ R)
    (htarget : ∀ source target v, target ∉ supported →
      F (singleFinitePiLp source v) target = 0)
    (hsource : ∀ source target v, source ∉ supported →
      F (singleFinitePiLp source v) target = 0) :
    FinitePiLpTypedWeightedRowKernelBound F sourceDist
      (A * Real.exp (rate * (R : ℝ)) * K) rate := by
  classical
  have hentry := finitePiLpTypedKernelBound_const_opNorm F
  refine ⟨mul_nonneg (mul_nonneg hA (Real.exp_pos _).le)
      (Nat.cast_nonneg K), hrate.le, ?_⟩
  intro source v
  by_cases hs : source ∈ supported
  · let f := fun target : ι =>
      Real.exp (rate * (sourceDist target source : ℝ)) *
        ‖F (singleFinitePiLp source v) target‖
    have hsumSupport : (∑ target, f target) =
        ∑ target ∈ supported, f target := by
      refine (Finset.sum_subset (Finset.subset_univ supported) ?_).symm
      intro target _ ht
      simp [f, htarget source target v ht]
    change (∑ target, f target) ≤ _
    rw [hsumSupport]
    calc
      ∑ target ∈ supported, f target ≤
          ∑ _target ∈ supported,
            (A * Real.exp (rate * (R : ℝ))) * ‖v‖ := by
        apply Finset.sum_le_sum
        intro target ht
        have hdist : (sourceDist target source : ℝ) ≤ (R : ℝ) := by
          exact_mod_cast hdiam target ht source hs
        have hexp : Real.exp (rate * (sourceDist target source : ℝ)) ≤
            Real.exp (rate * (R : ℝ)) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left hdist hrate.le
        calc
          f target ≤ Real.exp (rate * (sourceDist target source : ℝ)) *
              (A * ‖v‖) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            exact (hentry source target v).trans
              (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
          _ ≤ Real.exp (rate * (R : ℝ)) * (A * ‖v‖) :=
            mul_le_mul_of_nonneg_right hexp
              (mul_nonneg hA (norm_nonneg v))
          _ = (A * Real.exp (rate * (R : ℝ))) * ‖v‖ := by ring
      _ = (supported.card : ℝ) *
          ((A * Real.exp (rate * (R : ℝ))) * ‖v‖) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (K : ℝ) * ((A * Real.exp (rate * (R : ℝ))) * ‖v‖) := by
        gcongr
      _ = (A * Real.exp (rate * (R : ℝ)) * K) * ‖v‖ := by ring
  · have hzero : ∀ target, F (singleFinitePiLp source v) target = 0 :=
      fun target => hsource source target v hs
    simp only [hzero, norm_zero, mul_zero, Finset.sum_const_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (Nat.cast_nonneg K))
      (norm_nonneg v)

/-- The ambient head vanishes at every target outside its literal CMP95
source cell. -/
theorem cmp99Eq395PhysicalHead_apply_single_eq_zero_of_target
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
    (cell : FinBox 4 Q) (source target : FinBox 4 (2 * Q))
    (v : SUNLieCoord Nc)
    (houtside : ¬ cmp95SourcePeriodicCoarseCellSupport Q cell target) :
    cmp99Eq395PhysicalHead D hpi5 P hM depth hspacing background budget
      fineSmall hsmall cell (singleFinitePiLp source v) target = 0 := by
  have hzero :
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell target = 0 :=
    cmp95SourcePeriodicCoarseSquarePartition_value_eq_zero_of_not_support
      P Q cell target houtside
  simp [cmp99Eq395PhysicalHead, cmp99Eq395PhysicalSmoothMultiplier,
    finitePiLpScalarMultiplier_apply, hzero]

/-- The ambient head also vanishes when its one-site source lies outside the
literal CMP95 source cell. -/
theorem cmp99Eq395PhysicalHead_apply_single_eq_zero_of_source
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
    (cell : FinBox 4 Q) (source target : FinBox 4 (2 * Q))
    (v : SUNLieCoord Nc)
    (houtside : ¬ cmp95SourcePeriodicCoarseCellSupport Q cell source) :
    cmp99Eq395PhysicalHead D hpi5 P hM depth hspacing background budget
      fineSmall hsmall cell (singleFinitePiLp source v) target = 0 := by
  have hzero :
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell source = 0 :=
    cmp95SourcePeriodicCoarseSquarePartition_value_eq_zero_of_not_support
      P Q cell source houtside
  have hsingle : singleFinitePiLp source (0 : SUNLieCoord Nc) = 0 := by
    apply PiLp.ext
    intro x
    by_cases hx : x = source
    · subst x
      simp
    · rw [singleFinitePiLp_of_ne (0 : SUNLieCoord Nc) hx]
      rfl
  simp [cmp99Eq395PhysicalHead, cmp99Eq395PhysicalSmoothMultiplier,
    finitePiLpScalarMultiplier_single, hzero, hsingle]

/-- Bilateral exact support of the literal ambient head. -/
theorem cmp99Eq395PhysicalHead_apply_single_eq_zero_of_endpoint
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
    (cell : FinBox 4 Q) (source target : FinBox 4 (2 * Q))
    (v : SUNLieCoord Nc)
    (houtside :
      ¬ cmp95SourcePeriodicCoarseCellSupport Q cell source ∨
      ¬ cmp95SourcePeriodicCoarseCellSupport Q cell target) :
    cmp99Eq395PhysicalHead D hpi5 P hM depth hspacing background budget
      fineSmall hsmall cell (singleFinitePiLp source v) target = 0 := by
  rcases houtside with hsource | htarget
  · exact cmp99Eq395PhysicalHead_apply_single_eq_zero_of_source D hpi5 P hM
      depth hspacing background budget fineSmall hsmall cell source target v
        hsource
  · exact cmp99Eq395PhysicalHead_apply_single_eq_zero_of_target D hpi5 P hM
      depth hspacing background budget fineSmall hsmall cell source target v
        htarget

/-- Fixed-rate weighted-row bound for the literal ambient head.  Its row
count is the physical `2^4 = 16` source cell, not the ambient torus. -/
theorem cmp99Eq395PhysicalHead_weightedRow
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon rate : ℝ}
    (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    FinitePiLpTypedWeightedRowKernelBound
      (cmp99Eq395PhysicalHead D hpi5 P hM depth hspacing background budget
        fineSmall hsmall cell : CMP99Eq395AmbientOperator Q Nc)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395PhysicalHeadWeightedRowAmplitude
        M depth spacing epsilon rate) rate := by
  classical
  let F := cmp99Eq395PhysicalHead D hpi5 P hM depth hspacing background
    budget fineSmall hsmall cell
  let A := cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
    M depth spacing epsilon
  let supported := cmp95SourcePeriodicCoarseCellSupportFinset cell
  have hnorm : ‖F‖ ≤ A :=
    norm_cmp99Eq395PhysicalHead_le D hpi5 P hM depth hspacing background
      budget fineSmall hsmall cell
  have hA : 0 ≤ A := (norm_nonneg F).trans hnorm
  have hcard : supported.card ≤ 16 := by
    exact card_cmp95SourcePeriodicCoarseCellSupportFinset_le_sixteen cell
  have hdiam : ∀ target ∈ supported, ∀ source ∈ supported,
      finBoxDist target source ≤ 1 := by
    intro target htarget source hsource
    have htargetSupport :
        cmp95SourcePeriodicCoarseCellSupport Q cell target :=
      (mem_cmp95SourcePeriodicCoarseCellSupportFinset_iff cell target).mp
        (by simpa [supported] using htarget)
    have hsourceSupport :
        cmp95SourcePeriodicCoarseCellSupport Q cell source :=
      (mem_cmp95SourcePeriodicCoarseCellSupportFinset_iff cell source).mp
        (by simpa [supported] using hsource)
    have htargetCell :=
      cmp95SourcePeriodicCoarseCellSupport_mem_sourceBaseCell cell target
        htargetSupport
    have hsourceCell :=
      cmp95SourcePeriodicCoarseCellSupport_mem_sourceBaseCell cell source
        hsourceSupport
    have htargetZero :
        target ∈ cmp99SourceTildePiLargeBlocks cell 0 := by
      rw [cmp99SourceTildePiLargeBlocks_zero]
      exact htargetCell
    have hsourceZero :
        source ∈ cmp99SourceTildePiLargeBlocks cell 0 := by
      rw [cmp99SourceTildePiLargeBlocks_zero]
      exact hsourceCell
    simpa using
      (finBoxDist_le_of_mem_cmp99SourceTildePiLargeBlocks cell 0
        htargetZero hsourceZero)
  have htarget : ∀ source target v, target ∉ supported →
      F (singleFinitePiLp source v) target = 0 := by
    intro source target v houtside
    have hnot : ¬ cmp95SourcePeriodicCoarseCellSupport Q cell target := by
      simpa [supported,
        mem_cmp95SourcePeriodicCoarseCellSupportFinset_iff] using houtside
    simpa [F] using
      cmp99Eq395PhysicalHead_apply_single_eq_zero_of_target D hpi5 P hM
        depth hspacing background budget fineSmall hsmall cell source target v
          hnot
  have hsource : ∀ source target v, source ∉ supported →
      F (singleFinitePiLp source v) target = 0 := by
    intro source target v houtside
    have hnot : ¬ cmp95SourcePeriodicCoarseCellSupport Q cell source := by
      simpa [supported,
        mem_cmp95SourcePeriodicCoarseCellSupportFinset_iff] using houtside
    simpa [F] using
      cmp99Eq395PhysicalHead_apply_single_eq_zero_of_source D hpi5 P hM
        depth hspacing background budget fineSmall hsmall cell source target v
          hnot
  simpa [cmp99Eq395PhysicalHeadWeightedRowAmplitude, F, A] using
    (finitePiLpTypedWeightedRowKernelBound_of_bilateral_finset_support F
      finBoxDist supported A rate
      1 16 hA hrate hnorm hcard hdiam htarget hsource)

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
