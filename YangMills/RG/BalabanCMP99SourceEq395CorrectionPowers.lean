/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395CorrectionSharpWeightedRow
import YangMills.RG.DependentFinitePiLpWeightedRowWalk

/-!
# Fixed-rate bounds for every Neumann layer of CMP99 equation (3.95)

The complete physical correction already has a volume-independent weighted
row.  Submultiplicativity at the same spatial rate now gives the exact
geometric amplitude for every noncommutative power occurring in the Neumann
series.
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

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- Every homogeneous Neumann layer preserves the fixed rate of the physical
correction and has the literal geometric amplitude `A ^ n`. -/
theorem cmp99Eq395PhysicalCorrection_pow_weightedRow
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
      spacing epsilon < 1) (n : ℕ) :
    FinitePiLpTypedWeightedRowKernelBound
      ((cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
        budget fineSmall hsmall : CMP99Eq395AmbientOperator Q Nc) ^ n)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      ((cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
        M depth spacing epsilon) ^ n)
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon) := by
  let R := cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
    budget fineSmall hsmall
  let A := cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
    M depth spacing epsilon
  let rate := cmp99Eq395FirstAtomDecayRate M depth spacing epsilon
  have hR : FinitePiLpTypedWeightedRowKernelBound
      (R : CMP99Eq395AmbientOperator Q Nc)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ) A rate := by
    exact cmp99Eq395PhysicalCorrection_sharp_weightedRow D hpi5 P hM depth hspacing
      background budget fineSmall hsmall
  induction n with
  | zero =>
      simpa [R, A, rate] using
        (finitePiLpTypedWeightedRowKernelBound_id
          (g := SUNLieCoord Nc)
          (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
          hR.2.1 (fun x => finBoxDist_self x))
  | succ n ih =>
      simpa [R, A, rate, pow_succ] using
        (finitePiLpTypedWeightedRowKernelBound_comp
          (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
          finBoxDist finBoxDist
          (fun target middle source => finBoxDist_triangle target middle source)
          ih hR)

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG
