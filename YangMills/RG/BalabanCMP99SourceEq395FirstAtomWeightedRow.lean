/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395FirstLeftWeightedRow
import YangMills.RG.BalabanCMP99SourceEq395LocalizedAtomWeightedRow

/-!
# Fixed-rate weighted row of the first CMP99 equation (3.95) atom

The first atom is the only species not confined bilaterally to one source
cell.  Its left factor is the global generated middle multiplied on the
target side by the literal exterior characteristic.  The characteristic is
contractive, so the ambient exponential estimate survives unchanged.  A
uniform four-dimensional shell sum converts it to a weighted row, which is
then composed with the already localized physical head.
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

/-- Weighted-row amplitude of the complete first atom. -/
noncomputable def cmp99Eq395PhysicalFirstAtomWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99Eq395PhysicalFirstLeftWeightedRowAmplitude M depth spacing epsilon *
    cmp99Eq395PhysicalHeadWeightedRowAmplitude M depth spacing epsilon
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon)

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- The first physical atom of (3.95) has a volume-independent fixed-rate
weighted row. -/
theorem cmp99Eq395PhysicalRAtom_first_weightedRow
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
    FinitePiLpTypedWeightedRowKernelBound
      (cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
        fineSmall hsmall (cell, .first) : CMP99Eq395AmbientOperator Q Nc)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395PhysicalFirstAtomWeightedRowAmplitude
        M depth spacing epsilon)
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon) := by
  let rate := cmp99Eq395FirstAtomDecayRate M depth spacing epsilon
  have hrate : 0 < rate := by
    dsimp [rate, cmp99Eq395FirstAtomDecayRate]
    have := cmp99SourceGeneratedCombesThomasRate_pos
      4 M depth hspacing hsmall
    positivity
  have hleft := cmp99Eq395PhysicalFirstLeft_weightedRow
    hM depth hspacing background budget fineSmall hsmall cell
  have hhead := cmp99Eq395PhysicalHead_weightedRow D hpi5 P hM depth
    hspacing hrate background budget fineSmall hsmall cell
  have hcomp := finitePiLpTypedWeightedRowKernelBound_comp
    (fun target middle : FinBox 4 (2 * Q) => finBoxDist target middle)
    (fun middle source : FinBox 4 (2 * Q) => finBoxDist middle source)
    (fun target source : FinBox 4 (2 * Q) => finBoxDist target source)
    (fun target middle source => finBoxDist_triangle target middle source)
    hleft hhead
  rw [cmp99Eq395PhysicalRAtom_first_eq]
  refine ⟨hcomp.1, hcomp.2.1, ?_⟩
  intro source v
  simpa only [ContinuousLinearMap.neg_apply, PiLp.neg_apply, norm_neg] using
    hcomp.2.2 source v

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG
