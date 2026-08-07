/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpOwnerWeightedSupKernelPowers

/-!
# PRE-VALIDATION: summability of fixed-rate owner-kernel powers

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

An output-fixed weighted owner row controls the global finite supremum norm
without paying either the number of owners or the size of an owner fibre.
For convergence only, the finite ambient `L2` norm is compared with that
supremum norm by the explicit factor `sqrt(card ι)`.  This prefactor does not
alter the geometric ratio `A`, so `A < 1` makes the operator powers summable
in the existing complete continuous-linear-map space.

This module proves convergence of the homogeneous powers.  It does not yet
form their `tsum`, prove the inverse identities, specialize the physical
CMP99 amplitude, or attain window 15.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- The explicit finite supremum norm is bounded by the ambient counting-L2
norm. -/
theorem finitePiLpSupNorm_le_norm
    {ι g : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup g]
    (f : FinitePiLpField ι g) :
    finitePiLpSupNorm f ≤ ‖f‖ := by
  unfold finitePiLpSupNorm
  apply Finset.max'_le
  intro value hvalue
  rcases Finset.mem_image.mp hvalue with ⟨i, _hi, rfl⟩
  exact PiLp.norm_apply_le f i

/-- The ambient counting-L2 norm is bounded by the finite supremum norm with
the one explicit finite-dimensional comparison factor. -/
theorem norm_finitePiLp_le_sqrt_card_mul_supNorm
    {ι g : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup g]
    (f : FinitePiLpField ι g) :
    ‖f‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * finitePiLpSupNorm f := by
  rw [PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (finitePiLpSupNorm_nonneg f), ?_⟩
  calc
    (∑ i : ι, ‖f i‖ ^ 2) ≤
        ∑ _i : ι, finitePiLpSupNorm f ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact pow_le_pow_left₀ (norm_nonneg (f i))
        (norm_apply_le_finitePiLpSupNorm f i) 2
    _ = (Fintype.card ι : ℝ) * finitePiLpSupNorm f ^ 2 := by
      simp
    _ = (Real.sqrt (Fintype.card ι : ℝ) * finitePiLpSupNorm f) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Forgetting the nonnegative exponential weights gives the unweighted
output row with the same amplitude. -/
theorem finiteOwnerRowSum_le_of_weighted
    {β : Type*} [Fintype β]
    (dist : β → β → ℕ)
    {coefficient : β → β → ℝ} {A rate : ℝ}
    (hcoefficient : ∀ targetBlock sourceBlock,
      0 ≤ coefficient targetBlock sourceBlock)
    (hrow : FiniteOwnerWeightedRowBound coefficient dist A rate)
    (targetBlock : β) :
    ∑ sourceBlock : β, coefficient targetBlock sourceBlock ≤ A := by
  calc
    ∑ sourceBlock : β, coefficient targetBlock sourceBlock ≤
        ∑ sourceBlock : β,
          Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            coefficient targetBlock sourceBlock := by
      apply Finset.sum_le_sum
      intro sourceBlock _hsource
      calc
        coefficient targetBlock sourceBlock =
            1 * coefficient targetBlock sourceBlock := by ring
        _ ≤ Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
              coefficient targetBlock sourceBlock :=
          mul_le_mul_of_nonneg_right
            (Real.one_le_exp
              (mul_nonneg hrow.2.1 (Nat.cast_nonneg _)))
            (hcoefficient targetBlock sourceBlock)
    _ ≤ A := hrow.2.2 targetBlock

/-- A complete output-fixed owner row controls one application in the global
finite supremum norm without a carrier-cardinality factor. -/
theorem finitePiLpSupNorm_map_le_of_ownerWeighted
    {ι β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    {T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    {ownerMap : ι → β} {coefficient : β → β → ℝ}
    (dist : β → β → ℕ) {A rate : ℝ}
    (hT : FinitePiLpTypedOwnerWeightedSupKernelBound
      T ownerMap ownerMap coefficient dist A rate)
    (f : FinitePiLpField ι g) :
    finitePiLpSupNorm (T f) ≤ A * finitePiLpSupNorm f := by
  apply finitePiLpSupNorm_le_of_norm_apply_le
  intro target
  have hdecomp : f = ∑ sourceBlock,
      finitePiLpOwnerPart ownerMap sourceBlock f :=
    (sum_finitePiLpOwnerPart_eq ownerMap f).symm
  conv_lhs => rw [hdecomp]
  rw [map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  calc
    ‖∑ sourceBlock : β,
          T (finitePiLpOwnerPart ownerMap sourceBlock f) target‖ ≤
        ∑ sourceBlock : β,
          ‖T (finitePiLpOwnerPart ownerMap sourceBlock f) target‖ :=
      norm_sum_le _ _
    _ ≤ ∑ sourceBlock : β,
          coefficient (ownerMap target) sourceBlock *
            finitePiLpSupNorm
              (finitePiLpOwnerPart ownerMap sourceBlock f) := by
      apply Finset.sum_le_sum
      intro sourceBlock _hsource
      calc
        ‖T (finitePiLpOwnerPart ownerMap sourceBlock f) target‖ =
            ‖finitePiLpOwnerPart ownerMap (ownerMap target)
              (T (finitePiLpOwnerPart ownerMap sourceBlock f)) target‖ := by
          rw [finitePiLpOwnerPart_apply, if_pos rfl]
        _ ≤ finitePiLpSupNorm
              (finitePiLpOwnerPart ownerMap (ownerMap target)
                (T (finitePiLpOwnerPart ownerMap sourceBlock f))) :=
          norm_apply_le_finitePiLpSupNorm _ target
        _ ≤ coefficient (ownerMap target) sourceBlock *
              finitePiLpSupNorm
                (finitePiLpOwnerPart ownerMap sourceBlock f) :=
          hT.1.2 sourceBlock
            (finitePiLpOwnerPart ownerMap sourceBlock f)
            (finitePiLpOwnerPart_supported ownerMap sourceBlock f)
            (ownerMap target)
    _ ≤ ∑ sourceBlock : β,
          coefficient (ownerMap target) sourceBlock *
            finitePiLpSupNorm f := by
      apply Finset.sum_le_sum
      intro sourceBlock _hsource
      exact mul_le_mul_of_nonneg_left
        (finitePiLpSupNorm_ownerPart_le ownerMap sourceBlock f)
        (hT.1.1 (ownerMap target) sourceBlock)
    _ = (∑ sourceBlock : β,
          coefficient (ownerMap target) sourceBlock) *
            finitePiLpSupNorm f := by
      rw [Finset.sum_mul]
    _ ≤ A * finitePiLpSupNorm f :=
      mul_le_mul_of_nonneg_right
        (finiteOwnerRowSum_le_of_weighted dist hT.1.1 hT.2
          (ownerMap target))
        (finitePiLpSupNorm_nonneg f)

/-- Every homogeneous power has an ambient operator-norm majorant with the
same geometric ratio.  The finite-cardinality factor is only a convergence
prefactor. -/
theorem norm_finitePiLp_ownerWeighted_pow_le
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
    (n : ℕ) :
    ‖T ^ n‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * A ^ n := by
  have hpow := finitePiLpTypedOwnerWeightedSupKernelBound_pow
    dist hdiag htri hT n
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hT.2.1 n))
  intro f
  calc
    ‖(T ^ n) f‖ ≤ Real.sqrt (Fintype.card ι : ℝ) *
        finitePiLpSupNorm ((T ^ n) f) :=
      norm_finitePiLp_le_sqrt_card_mul_supNorm _
    _ ≤ Real.sqrt (Fintype.card ι : ℝ) *
          ((A ^ n) * finitePiLpSupNorm f) :=
      mul_le_mul_of_nonneg_left
        (finitePiLpSupNorm_map_le_of_ownerWeighted dist hpow f)
        (Real.sqrt_nonneg _)
    _ = (Real.sqrt (Fintype.card ι : ℝ) * A ^ n) *
          finitePiLpSupNorm f := by ring
    _ ≤ (Real.sqrt (Fintype.card ι : ℝ) * A ^ n) * ‖f‖ :=
      mul_le_mul_of_nonneg_left (finitePiLpSupNorm_le_norm f)
        (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hT.2.1 n))

/-- A strict owner-sup contraction makes the homogeneous continuous-linear
operator powers summable in the existing ambient topology. -/
theorem summable_finitePiLp_ownerWeighted_pow
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
    Summable fun n : ℕ => T ^ n := by
  have hmajor : Summable fun n : ℕ =>
      Real.sqrt (Fintype.card ι : ℝ) * A ^ n :=
    (summable_geometric_of_lt_one hT.2.1 hsmall).mul_left
      (Real.sqrt (Fintype.card ι : ℝ))
  apply Summable.of_norm_bounded hmajor
  intro n
  exact norm_finitePiLp_ownerWeighted_pow_le
    dist hdiag htri hT n

end

end YangMills.RG
