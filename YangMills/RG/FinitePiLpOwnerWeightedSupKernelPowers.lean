/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpOwnerWeightedSupKernelAlgebra

/-!
# PRE-VALIDATION: fixed-rate powers of owner-weighted supremum kernels

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

The identity coefficient is the literal diagonal matrix on owner fibres.
Starting from it, coefficient powers are defined by the already sealed
convolution, in the same order as powers of continuous linear endomorphisms.
Every power retains the original spatial rate and has geometric amplitude
`A ^ n`.

This module proves homogeneous power bounds only.  It does not sum the
Neumann series, assert `A < 1`, specialize a physical CMP99 budget, or attain
window 15.
-/

namespace YangMills.RG

noncomputable section

/-- Literal identity matrix on the finite owner type. -/
noncomputable def finiteOwnerIdentityCoefficient
    {β : Type*} [DecidableEq β] (targetBlock sourceBlock : β) : ℝ :=
  if targetBlock = sourceBlock then 1 else 0

/-- A field supported in one owner fibre has zero projection to every
different owner fibre. -/
theorem finitePiLpOwnerPart_eq_zero_of_supported_of_ne
    {ι β g : Type*} [Fintype ι] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (ownerMap : ι → β) {sourceBlock targetBlock : β}
    (f : FinitePiLpField ι g)
    (hf : FinitePiLpSupportedInOwner ownerMap sourceBlock f)
    (hne : targetBlock ≠ sourceBlock) :
    finitePiLpOwnerPart ownerMap targetBlock f = 0 := by
  apply PiLp.ext
  intro source
  rw [finitePiLpOwnerPart_apply]
  by_cases hsource : ownerMap source = targetBlock
  · have hsourceNe : ownerMap source ≠ sourceBlock := by
      intro howner
      exact hne (hsource.symm.trans howner)
    rw [if_pos hsource, hf source hsourceNe]
    simp
  · rw [if_neg hsource]
    simp

/-- The identity endomorphism has the literal diagonal owner-block
coefficient matrix. -/
theorem finitePiLpTypedOwnerSupKernelBound_id
    {ι β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (ownerMap : ι → β) :
    FinitePiLpTypedOwnerSupKernelBound
      (ContinuousLinearMap.id ℝ (FinitePiLpField ι g))
      ownerMap ownerMap finiteOwnerIdentityCoefficient := by
  refine ⟨?_, ?_⟩
  · intro targetBlock sourceBlock
    by_cases h : targetBlock = sourceBlock <;>
      simp [finiteOwnerIdentityCoefficient, h]
  · intro sourceBlock f hf targetBlock
    by_cases hblocks : targetBlock = sourceBlock
    · subst targetBlock
      simpa [finiteOwnerIdentityCoefficient] using
        (finitePiLpSupNorm_ownerPart_le ownerMap sourceBlock f)
    · rw [ContinuousLinearMap.id_apply,
        finitePiLpOwnerPart_eq_zero_of_supported_of_ne
          ownerMap f hf hblocks]
      rw [finiteOwnerIdentityCoefficient, if_neg hblocks, zero_mul]
      apply finitePiLpSupNorm_le_of_norm_apply_le
      intro source
      simp

/-- The output-fixed weighted row of the identity coefficient has amplitude
one whenever owner distance vanishes on the diagonal. -/
theorem finiteOwnerWeightedRowBound_id
    {β : Type*} [Fintype β] [DecidableEq β]
    (dist : β → β → ℕ) {rate : ℝ}
    (hrate : 0 ≤ rate) (hdiag : ∀ owner, dist owner owner = 0) :
    FiniteOwnerWeightedRowBound
      finiteOwnerIdentityCoefficient dist 1 rate := by
  refine ⟨zero_le_one, hrate, ?_⟩
  intro targetBlock
  classical
  calc
    ∑ sourceBlock : β,
          Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            finiteOwnerIdentityCoefficient targetBlock sourceBlock =
        Real.exp (rate * (dist targetBlock targetBlock : ℝ)) *
          finiteOwnerIdentityCoefficient targetBlock targetBlock := by
      apply Fintype.sum_eq_single targetBlock
      intro sourceBlock hsource
      simp [finiteOwnerIdentityCoefficient, Ne.symm hsource]
    _ = 1 := by simp [finiteOwnerIdentityCoefficient, hdiag]
    _ ≤ 1 := le_rfl

/-- Complete identity certificate for the owner-weighted supremum kernel
interface. -/
theorem finitePiLpTypedOwnerWeightedSupKernelBound_id
    {ι β g : Type*}
    [Fintype ι] [Nonempty ι]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (ownerMap : ι → β) (dist : β → β → ℕ) {rate : ℝ}
    (hrate : 0 ≤ rate) (hdiag : ∀ owner, dist owner owner = 0) :
    FinitePiLpTypedOwnerWeightedSupKernelBound
      (ContinuousLinearMap.id ℝ (FinitePiLpField ι g))
      ownerMap ownerMap finiteOwnerIdentityCoefficient dist 1 rate := by
  exact ⟨finitePiLpTypedOwnerSupKernelBound_id ownerMap,
    finiteOwnerWeightedRowBound_id dist hrate hdiag⟩

/-- Literal power of an owner-block coefficient matrix, with the identity
coefficient at layer zero and sealed convolution at every successor. -/
noncomputable def finiteOwnerKernelPower
    {β : Type*} [Fintype β] [DecidableEq β]
    (coefficient : β → β → ℝ) : ℕ → β → β → ℝ
  | 0 => finiteOwnerIdentityCoefficient
  | n + 1 => finiteOwnerKernelConvolution
      (finiteOwnerKernelPower coefficient n) coefficient

/-- Every homogeneous operator power retains the same output-fixed weighted
owner rate and has the literal geometric amplitude `A ^ n`. -/
theorem finitePiLpTypedOwnerWeightedSupKernelBound_pow
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
      T ownerMap ownerMap coefficient dist A rate) :
    ∀ n,
      FinitePiLpTypedOwnerWeightedSupKernelBound
        (T ^ n) ownerMap ownerMap
        (finiteOwnerKernelPower coefficient n) dist (A ^ n) rate := by
  intro n
  induction n with
  | zero =>
      have hpow :
          T ^ 0 = ContinuousLinearMap.id ℝ (FinitePiLpField ι g) := by
        ext f
        rfl
      rw [hpow]
      simpa only [finiteOwnerKernelPower, pow_zero] using
        (finitePiLpTypedOwnerWeightedSupKernelBound_id
          (ι := ι) (β := β) (g := g)
          ownerMap dist hT.2.2.1 hdiag)
  | succ n ih =>
      simpa [finiteOwnerKernelPower, pow_succ] using
        (finitePiLpTypedOwnerWeightedSupKernelBound_comp
          dist htri ih hT)

end

end YangMills.RG
