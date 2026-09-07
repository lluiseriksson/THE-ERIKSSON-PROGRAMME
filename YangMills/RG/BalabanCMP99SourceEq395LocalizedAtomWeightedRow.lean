/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395LocalizedAtomNorm
import YangMills.RG.BalabanCMP99SourceEq395HeadSupport

/-!
# Fixed-rate weighted rows of the localized CMP99 equation (3.95) atoms

Exact bilateral support in the sixteen-block source cell converts the uniform
operator norms of the second and third physical atoms into a fixed-rate
weighted-row estimate.  The amplitude is independent of the ambient torus:
only the literal cardinality `16` and diameter `1` occur.
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

/-- Support-sharp weighted-row amplitude for either localized atom. -/
noncomputable def cmp99Eq395LocalizedAtomWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99Eq395LocalizedAtomNormBound M depth spacing epsilon *
    Real.exp rate * 16

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

/-- Every non-first physical atom has a volume-independent fixed-rate
weighted row on its exact source cell. -/
theorem cmp99Eq395PhysicalRAtom_weightedRow_of_ne_first
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
    (cell : FinBox 4 Q) (species : CMP99Eq395CorrectionSpecies)
    (hspecies : species ≠ .first) :
    FinitePiLpTypedWeightedRowKernelBound
      (cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
        fineSmall hsmall (cell, species) : CMP99Eq395AmbientOperator Q Nc)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395LocalizedAtomWeightedRowAmplitude
        M depth spacing epsilon rate) rate := by
  classical
  let F := cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background
    budget fineSmall hsmall (cell, species)
  let A := cmp99Eq395LocalizedAtomNormBound M depth spacing epsilon
  let supported := cmp99SourceBaseCell cell
  have hnorm : ‖F‖ ≤ A := by
    cases species with
    | first => exact (hspecies rfl).elim
    | second =>
        simpa [F, A] using norm_cmp99Eq395PhysicalRAtom_second_le D hpi5 P
          hM depth hspacing background budget fineSmall hsmall cell
    | third =>
        simpa [F, A] using norm_cmp99Eq395PhysicalRAtom_third_le D hpi5 P
          hM depth hspacing background budget fineSmall hsmall cell
  have hA : 0 ≤ A := (norm_nonneg F).trans hnorm
  have hcard : supported.card ≤ 16 := by
    simpa [supported] using (le_of_eq (card_cmp99SourceBaseCell cell))
  have hdiam : ∀ target ∈ supported, ∀ source ∈ supported,
      finBoxDist target source ≤ 1 := by
    intro target htarget source hsource
    have htargetZero : target ∈ cmp99SourceTildePiLargeBlocks cell 0 := by
      rw [cmp99SourceTildePiLargeBlocks_zero]
      simpa [supported] using htarget
    have hsourceZero : source ∈ cmp99SourceTildePiLargeBlocks cell 0 := by
      rw [cmp99SourceTildePiLargeBlocks_zero]
      simpa [supported] using hsource
    simpa using
      (finBoxDist_le_of_mem_cmp99SourceTildePiLargeBlocks cell 0
        htargetZero hsourceZero)
  have htarget : ∀ source target v, target ∉ supported →
      F (singleFinitePiLp source v) target = 0 := by
    intro source target v houtside
    simpa [F, supported] using
      cmp99Eq395PhysicalRAtom_apply_single_eq_zero_of_target_of_ne_first
        D hpi5 P hM depth hspacing background budget fineSmall hsmall cell
          species source target v hspecies houtside
  have hsource : ∀ source target v, source ∉ supported →
      F (singleFinitePiLp source v) target = 0 := by
    intro source target v houtside
    simpa [F, supported] using
      cmp99Eq395PhysicalRAtom_apply_single_eq_zero_of_endpoint_of_ne_first
        D hpi5 P hM depth hspacing background budget fineSmall hsmall cell
          species source target v hspecies (Or.inl houtside)
  simpa [cmp99Eq395LocalizedAtomWeightedRowAmplitude, F, A] using
    (finitePiLpTypedWeightedRowKernelBound_of_bilateral_finset_support F
      finBoxDist supported A rate 1 16 hA hrate hnorm hcard hdiam htarget
        hsource)

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG
