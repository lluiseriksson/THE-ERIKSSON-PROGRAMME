/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96Eq240SourceSeparatedCutoffLaplacian
import YangMills.RG.BalabanCMP99Eq342RegionalGreenCertificate

/-!
# PRE-VALIDATION: the covariant-link species in CMP99 (3.89)

The source of this module is present, but its `.olean` has not yet been
materialized and its declarations have not yet been verified by the Lean
compiler.

CMP99 (3.88)--(3.89), printed p. 409, estimates the link-derivative species
directly from the `D G'` component of (3.42).  At rescaled unit spacing the
two oriented bonds incident to a site are exactly entries of the same
covariant derivative.  The reverse entry is transported by the literal
adjoint isometry; no abstract row/column symmetry is used.

The source-separated cutoff slope is multiplied by the `(B0 * ell)` scale
of `D G'` before any cell or layer sum.  The resulting scalar product is
definitionally `4 * B0 * derivBound / K`, so the inverse-large-block gain is
visible at the first analytic species rather than recovered after a Schur
majorant.  This is one component of (3.89), not yet the complete defect
bound or the contraction `norm R' < 1`.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {L K Q N Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero N] [NeZero Nc]

/-- The reverse oriented difference at `x` has exactly the norm of the
positive covariant derivative based at `x.shiftBack i`.  The equality is
physical: it uses the adjoint action of the actual background link. -/
theorem norm_covariant_reverse_difference_eq
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground 4 N Nc)
    (phi : PhysicalGaugeZeroCochain 4 N Nc)
    (x : FinBox 4 N) (i : Fin 4) :
    ‖phi x -
        rho.adCLM
          (U (positiveEdgeOfPhysicalBond
            ((FinBox.shiftBack x i, i) : PhysicalBond 4 N)))⁻¹
          (phi (x.shiftBack i))‖ =
      ‖covariantD0CLM rho U phi
        ((FinBox.shiftBack x i, i) : PhysicalBond 4 N)‖ := by
  let u := U (positiveEdgeOfPhysicalBond
    ((FinBox.shiftBack x i, i) : PhysicalBond 4 N))
  calc
    ‖phi x - rho.adCLM u⁻¹ (phi (x.shiftBack i))‖ =
        ‖rho.adCLM u⁻¹
          (rho.adCLM u (phi x) - phi (x.shiftBack i))‖ := by
      congr 1
      rw [map_sub, rho.ad_inv_apply_ad]
    _ = ‖rho.adCLM u (phi x) - phi (x.shiftBack i)‖ := rho.norm_ad _ _
    _ = ‖phi (x.shiftBack i) - rho.adCLM u (phi x)‖ := norm_sub_rev _ _
    _ = ‖covariantD0CLM rho U phi
        ((FinBox.shiftBack x i, i) : PhysicalBond 4 N)‖ := by
      simp only [covariantD0CLM_apply]
      rw [FinBox.shift_shiftBack]
      rfl

/-- Direct pointwise estimate for the first species of CMP99 (3.88).

At unit lattice spacing it pays one cutoff difference and one entry of the
literal covariant derivative for each of the eight oriented bonds incident
to `x`.  No operator norm, Combes--Thomas estimate, Schur sum, carrier
cardinality or Poincare constant occurs. -/
theorem norm_cmp99CovariantCutoffLinkDerivative_one_le
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground 4 N Nc)
    (h : FinBox 4 N → ℝ) (phi : PhysicalGaugeZeroCochain 4 N Nc)
    (x : FinBox 4 N) (slope : ℝ)
    (hforward : ∀ i : Fin 4, ‖h x - h (x.shift i)‖ ≤ slope)
    (hback : ∀ i : Fin 4, ‖h x - h (x.shiftBack i)‖ ≤ slope) :
    ‖cmp99CovariantCutoffLinkDerivative rho U 1 h phi x‖ ≤
      slope * ∑ i : Fin 4,
        (‖covariantD0CLM rho U phi ((x, i) : PhysicalBond 4 N)‖ +
          ‖covariantD0CLM rho U phi
            ((FinBox.shiftBack x i, i) : PhysicalBond 4 N)‖) := by
  simp only [cmp99CovariantCutoffLinkDerivative, inv_one, one_smul]
  calc
    ‖∑ i : Fin 4,
        ((h x - h (x.shift i)) •
            (phi x - rho.adCLM (U (ConcreteEdge.mk x i true))
              (phi (x.shift i))) +
          (h x - h (x.shiftBack i)) •
            (phi x -
              rho.adCLM
                (U (positiveEdgeOfPhysicalBond
                  ((FinBox.shiftBack x i, i) : PhysicalBond 4 N)))⁻¹
                (phi (x.shiftBack i))))‖ ≤
        ∑ i : Fin 4,
          ‖(h x - h (x.shift i)) •
              (phi x - rho.adCLM (U (ConcreteEdge.mk x i true))
                (phi (x.shift i))) +
            (h x - h (x.shiftBack i)) •
              (phi x -
                rho.adCLM
                  (U (positiveEdgeOfPhysicalBond
                    ((FinBox.shiftBack x i, i) : PhysicalBond 4 N)))⁻¹
                  (phi (x.shiftBack i)))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 4,
        (slope *
            ‖covariantD0CLM rho U phi ((x, i) : PhysicalBond 4 N)‖ +
          slope *
            ‖covariantD0CLM rho U phi
              ((FinBox.shiftBack x i, i) : PhysicalBond 4 N)‖) := by
      gcongr with i
      calc
        ‖(h x - h (x.shift i)) •
              (phi x - rho.adCLM (U (ConcreteEdge.mk x i true))
                (phi (x.shift i))) +
            (h x - h (x.shiftBack i)) •
              (phi x -
                rho.adCLM
                  (U (positiveEdgeOfPhysicalBond
                    ((FinBox.shiftBack x i, i) : PhysicalBond 4 N)))⁻¹
                  (phi (x.shiftBack i)))‖ ≤
            ‖(h x - h (x.shift i)) •
              (phi x - rho.adCLM (U (ConcreteEdge.mk x i true))
                (phi (x.shift i)))‖ +
            ‖(h x - h (x.shiftBack i)) •
              (phi x -
                rho.adCLM
                  (U (positiveEdgeOfPhysicalBond
                    ((FinBox.shiftBack x i, i) : PhysicalBond 4 N)))⁻¹
                  (phi (x.shiftBack i)))‖ := norm_add_le _ _
        _ = ‖h x - h (x.shift i)‖ *
              ‖covariantD0CLM rho U phi ((x, i) : PhysicalBond 4 N)‖ +
            ‖h x - h (x.shiftBack i)‖ *
              ‖covariantD0CLM rho U phi
                ((FinBox.shiftBack x i, i) : PhysicalBond 4 N)‖ := by
          rw [norm_smul, norm_smul,
            norm_covariant_reverse_difference_eq rho U phi x i]
          simp only [Real.norm_eq_abs, covariantD0CLM_apply]
        _ ≤ slope *
              ‖covariantD0CLM rho U phi ((x, i) : PhysicalBond 4 N)‖ +
            slope *
              ‖covariantD0CLM rho U phi
                ((FinBox.shiftBack x i, i) : PhysicalBond 4 N)‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right (hforward i) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (hback i) (norm_nonneg _))
    _ = slope * ∑ i : Fin 4,
        (‖covariantD0CLM rho U phi ((x, i) : PhysicalBond 4 N)‖ +
          ‖covariantD0CLM rho U phi
            ((FinBox.shiftBack x i, i) : PhysicalBond 4 N)‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/-- The source slope times the derivative scale from CMP99 (3.42) has the
literal inverse-`K` gain before any cell or layer sum. -/
theorem cmp99Eq389SourceSeparatedSlope_mul_leftDerivativeScale
    (P : CMP95SourceSmoothPartitionProfile)
    (B0 : ℝ) (L K depth : ℕ) [NeZero L] [NeZero K] :
    cmp96SourceSeparatedCutoffDifferenceBudget P L K depth *
        (B0 * (L ^ (depth + 1) : ℝ)) =
      (4 * B0 * P.derivBound) / (K : ℝ) := by
  unfold cmp96SourceSeparatedCutoffDifferenceBudget
  rw [show
      ((8 * P.derivBound) /
          (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ)) *
          (B0 * (L ^ (depth + 1) : ℝ)) =
        B0 * (((8 * P.derivBound) /
          (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ)) *
            (L ^ (depth + 1) : ℝ)) by ring]
  rw [cmp99SourceSeparatedLargeBlockSlope_mul_precisionRange P L K depth]
  ring

end

end YangMills.RG
