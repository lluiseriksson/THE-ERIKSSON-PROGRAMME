/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpOwnerWeightedSupKernelNeumann

/-!
# PRE-VALIDATION: owner-weighted Neumann inverse identities

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

The previously sealed owner-sup contraction makes the literal power series
summable in the endomorphism ring.  The standard telescoping identities for a
summable geometric series therefore identify its `tsum` as both a left and a
right inverse of `1 - T`.

This is ring-level closure of the Neumann object.  It does not specialize the
physical CMP99 amplitude, produce uniform `B0` or `delta0`, or attain window
15.
-/

namespace YangMills.RG

noncomputable section

/-- The owner-weighted Neumann `tsum` is a right inverse of `1 - T`. -/
theorem finitePiLp_ownerWeighted_neumann_mul_one_sub
    {ι β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : β → β → ℕ)
    (hdiag : ∀ owner, dist owner owner = 0)
    (htri : ∀ targetBlock middleBlock sourceBlock,
      dist targetBlock sourceBlock ≤
        dist targetBlock middleBlock + dist middleBlock sourceBlock)
    {T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    {ownerMap : ι → β} {coefficient : β → β → ℝ}
    {A rate : ℝ}
    (hT : FinitePiLpTypedOwnerWeightedSupKernelBound
      T ownerMap ownerMap coefficient dist A rate)
    (hsmall : A < 1) :
    (∑' n : ℕ, T ^ n) * (1 - T) = 1 := by
  exact (summable_finitePiLp_ownerWeighted_pow
    dist hdiag htri hT hsmall).tsum_pow_mul_one_sub

/-- The owner-weighted Neumann `tsum` is a left inverse of `1 - T`. -/
theorem finitePiLp_one_sub_mul_ownerWeighted_neumann
    {ι β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : β → β → ℕ)
    (hdiag : ∀ owner, dist owner owner = 0)
    (htri : ∀ targetBlock middleBlock sourceBlock,
      dist targetBlock sourceBlock ≤
        dist targetBlock middleBlock + dist middleBlock sourceBlock)
    {T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    {ownerMap : ι → β} {coefficient : β → β → ℝ}
    {A rate : ℝ}
    (hT : FinitePiLpTypedOwnerWeightedSupKernelBound
      T ownerMap ownerMap coefficient dist A rate)
    (hsmall : A < 1) :
    (1 - T) * (∑' n : ℕ, T ^ n) = 1 := by
  exact (summable_finitePiLp_ownerWeighted_pow
    dist hdiag htri hT hsmall).one_sub_mul_tsum_pow

end

end YangMills.RG
