/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389CovariantLinkCommonMetric

/-!
# PRE-VALIDATION: physical first-species bound in CMP99 (3.89)

The source is present, but its `.olean` has not yet been materialized and its
declarations have not yet been verified by the Lean compiler.

This module specializes the sealed common-metric link estimate to the literal
source-separated square partition.  The exact pre-sum `Klarge⁻¹` gain is
retained and the four directions are evaluated explicitly.  `Klarge` is the
source's independent large-block parameter; `A` is the regional precision.
They are deliberately not given the same Lean name.

No cell, overlap, layer, Schur, Poincare, or operator-norm sum occurs here.
This is only the first of the three displayed species in CMP99 (3.89).
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {L Klarge Q Nc : ℕ}
variable [NeZero L] [NeZero Klarge] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq389SeparatedBlockSide
    (L Klarge depth : ℕ) [NeZero L] [NeZero Klarge] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L Klarge depth) :=
  ⟨by
    unfold cmp99SourceSeparatedLargeBlockSide
    exact (Nat.mul_pos (NeZero.pos Klarge)
      (pow_pos (NeZero.pos L) (depth + 1))).ne'⟩

private instance instNeZeroEq389SeparatedAmbientSide
    (L Klarge Q depth : ℕ) [NeZero L] [NeZero Klarge] [NeZero Q] :
    NeZero
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos Klarge)
      (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- Explicit scalar multiplying the central source-decay factor for the first
covariant-link species.  The first `4` counts directions; the second is the
sealed slope-times-derivative-scale constant. -/
noncomputable def cmp99Eq389CovariantLinkSourceBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (B0 delta0 : ℝ) (Klarge : ℕ) : ℝ :=
  4 * ((4 * B0 * P.derivBound) / (Klarge : ℝ)) *
    (1 + Real.exp delta0)

/-- The literal source-separated cutoff and the literal regional Green obey
the complete pointwise bound for the first displayed species of CMP99 (3.89).

The inverse-`Klarge` gain is present before any cell or layer sum. -/
theorem norm_cmp99CovariantCutoffLinkDerivative_regionalGreen_sourceSeparated_le
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U 1 A c hc hAcoer
      B0 delta0 (L ^ (depth + 1) : ℝ))
    (source : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))) :
    ‖cmp99CovariantCutoffLinkDerivative rho U 1
        (fun y => (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := Klarge) (Q := Q) (depth := depth) P).value cell y)
        (extendZeroZeroCLM Omega
          (cmp99RegionalDirichletGreen Omega A hc hAcoer
            (singleFinitePiLp source v))) x‖ ≤
      cmp99Eq389CovariantLinkSourceBudget P B0 delta0 Klarge *
        Real.exp (-(delta0 *
          (cmp99Eq342RescaledBlockDist
            (cmp99SourceSeparatedLargeBlockSide L Klarge depth) Q
            x source.1 : ℝ))) * ‖v‖ := by
  let slope := cmp96SourceSeparatedCutoffDifferenceBudget P L Klarge depth
  have hslope : 0 ≤ slope :=
    cmp96SourceSeparatedCutoffDifferenceBudget_nonneg P L Klarge depth
  have hforward (i : Fin 4) :
      ‖(cmp99SourceSeparatedLargeBlockSquarePartition
            (L := L) (K := Klarge) (Q := Q) (depth := depth) P).value cell x -
          (cmp99SourceSeparatedLargeBlockSquarePartition
            (L := L) (K := Klarge) (Q := Q) (depth := depth) P).value cell
              (x.shift i)‖ ≤ slope :=
    norm_cmp96SourceSeparatedCutoff_sub_shift_le
      (L := L) (K := Klarge) P depth cell x i
  have hback (i : Fin 4) :
      ‖(cmp99SourceSeparatedLargeBlockSquarePartition
            (L := L) (K := Klarge) (Q := Q) (depth := depth) P).value cell x -
          (cmp99SourceSeparatedLargeBlockSquarePartition
            (L := L) (K := Klarge) (Q := Q) (depth := depth) P).value cell
              (x.shiftBack i)‖ ≤ slope :=
    norm_cmp96SourceSeparatedCutoff_sub_shiftBack_le
      (L := L) (K := Klarge) P depth cell x i
  have hmain :=
    norm_cmp99CovariantCutoffLinkDerivative_regionalGreen_commonMetric
      Omega rho U A c hc hAcoer B0 delta0 (L ^ (depth + 1) : ℝ) C
      (fun y => (cmp99SourceSeparatedLargeBlockSquarePartition
        (L := L) (K := Klarge) (Q := Q) (depth := depth) P).value cell y)
      source v x slope hslope hforward hback
  calc
    ‖cmp99CovariantCutoffLinkDerivative rho U 1
        (fun y => (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := Klarge) (Q := Q) (depth := depth) P).value cell y)
        (extendZeroZeroCLM Omega
          (cmp99RegionalDirichletGreen Omega A hc hAcoer
            (singleFinitePiLp source v))) x‖ ≤
        slope * ∑ _i : Fin 4,
          ((B0 * (L ^ (depth + 1) : ℝ)) *
                Real.exp (-(delta0 *
                  (cmp99Eq342RescaledBlockDist
                    (cmp99SourceSeparatedLargeBlockSide L Klarge depth) Q
                    x source.1 : ℝ))) * ‖v‖ +
            (B0 * (L ^ (depth + 1) : ℝ)) *
                (Real.exp delta0 * Real.exp (-(delta0 *
                  (cmp99Eq342RescaledBlockDist
                    (cmp99SourceSeparatedLargeBlockSide L Klarge depth) Q
                    x source.1 : ℝ)))) * ‖v‖) := hmain
    _ = cmp99Eq389CovariantLinkSourceBudget P B0 delta0 Klarge *
        Real.exp (-(delta0 *
          (cmp99Eq342RescaledBlockDist
            (cmp99SourceSeparatedLargeBlockSide L Klarge depth) Q
            x source.1 : ℝ))) * ‖v‖ := by
      rw [Fin.sum_univ_four]
      unfold cmp99Eq389CovariantLinkSourceBudget slope
      calc
        _ = 4 *
            (cmp96SourceSeparatedCutoffDifferenceBudget P L Klarge depth *
              (B0 * (L ^ (depth + 1) : ℝ))) *
            (1 + Real.exp delta0) *
            Real.exp (-(delta0 *
              (cmp99Eq342RescaledBlockDist
                (cmp99SourceSeparatedLargeBlockSide L Klarge depth) Q
                x source.1 : ℝ))) * ‖v‖ := by ring
        _ = 4 * ((4 * B0 * P.derivBound) / (Klarge : ℝ)) *
            (1 + Real.exp delta0) *
            Real.exp (-(delta0 *
              (cmp99Eq342RescaledBlockDist
                (cmp99SourceSeparatedLargeBlockSide L Klarge depth) Q
                x source.1 : ℝ))) * ‖v‖ := by
          rw [cmp99Eq389SourceSeparatedSlope_mul_leftDerivativeScale
            P B0 L Klarge depth]

end

end YangMills.RG
