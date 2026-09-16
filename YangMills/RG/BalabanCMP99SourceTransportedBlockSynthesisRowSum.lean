/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceActiveFineBlockEquiv
import YangMills.RG.BalabanCMP99SourceWeightedRegionalAdjoint

/-!
# Exact row sum of one transported source synthesis

The counting-space adjoint of one source average spreads a coarse value over
one complete block.  Reindexing the saturated fine region by active blocks
shows that its `l1` row cost is exactly `|w| M^d`.  At the printed source
weight `w = M^{-d}` this is one, so no range-ball cardinality survives.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

variable {d M N' : ℕ} [NeZero M] [NeZero N']
variable {g : Type*}
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]

/-- Exact `l1` target sum of a transported block synthesis on a saturated
fine region. -/
theorem sum_norm_cmp99TransportedBlockSynthesisCLM
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (w : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g) :
    (∑ x : ActiveGaugeRegion.Site Omega,
        ‖cmp99TransportedBlockSynthesisCLM
          Omega hOmega w transport eta x‖) =
      |w| * (M : ℝ) ^ d * ∑ y, ‖eta y‖ := by
  rw [sum_activeGaugeRegion_eq_sum_activeBlocks Omega hOmega]
  simp_rw [cmp99TransportedBlockSynthesisCLM_apply_block, norm_smul,
    LinearIsometryEquiv.norm_map]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    blockOf_card, nsmul_eq_mul, Nat.cast_pow, Real.norm_eq_abs]
  change (∑ x ∈ Finset.univ,
      (M : ℝ) ^ d * (|w| * ‖eta.ofLp x‖)) =
    |w| * (M : ℝ) ^ d * ∑ x ∈ Finset.univ, ‖eta.ofLp x‖
  calc
    _ = (M : ℝ) ^ d *
        (∑ x ∈ Finset.univ, |w| * ‖eta.ofLp x‖) :=
      (Finset.mul_sum Finset.univ
        (fun x => |w| * ‖eta.ofLp x‖) ((M : ℝ) ^ d)).symm
    _ = (M : ℝ) ^ d *
        (|w| * ∑ x ∈ Finset.univ, ‖eta.ofLp x‖) := by
      exact congrArg (fun z : ℝ => (M : ℝ) ^ d * z)
        (Finset.mul_sum Finset.univ (fun x => ‖eta.ofLp x‖) |w|).symm
    _ = _ := by ring

/-- At the literal CMP99 coefficient `M^{-d}`, the counting adjoint has
exactly unit `l1` row cost. -/
theorem sum_norm_cmp99SourceTransportedBlockAverage_adjoint
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g) :
    (∑ x : ActiveGaugeRegion.Site Omega,
        ‖(cmp99SourceTransportedBlockAverageCLM Omega transport).adjoint
          eta x‖) =
      ∑ y, ‖eta y‖ := by
  rw [cmp99SourceTransportedBlockAverageCLM,
    ← cmp99TransportedBlockSynthesisCLM_eq_adjoint Omega hOmega
      (cmp99SourceBlockAverageWeight M d) transport,
    sum_norm_cmp99TransportedBlockSynthesisCLM]
  have hw : 0 ≤ cmp99SourceBlockAverageWeight M d := by
    unfold cmp99SourceBlockAverageWeight
    positivity
  rw [abs_of_nonneg hw, cmp99SourceBlockAverageWeight_mul_card, one_mul]

end

end YangMills.RG
