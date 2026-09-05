/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpBlockLocalizedSupGlobal

/-!
# Cold-sealed output-fixed weighted owner rows in finite supremum norm

Compiler-verified at exact source checkpoint
`596802620b489c55a9a34c0e445323c1f426a125` by cold GitHub Actions run
`31195176692`.  The focal and audit exited zero, and all seven audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

A source-localized CMP99 estimate controls the action from one complete owner
fibre to one output owner fibre.  Iteration in the global supremum norm needs
the output-fixed row of those block-operator coefficients, not a source-fixed
sum over outputs and not an expansion into fine coordinate probes.

This module keeps the nonnegative coefficient matrix explicit.  Pointwise
decay at rate `decay` yields a weighted owner row at every strictly smaller
rate `rate`, paying exactly one shell sum at the reserved gap
`decay - rate`.  Composition and Neumann powers remain downstream.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- A nonnegative scalar matrix bounds the supremum action between complete
source and target owner fibres.  The scalar coefficient is explicit data,
not a hidden supremum over fields. -/
def FinitePiLpTypedOwnerSupKernelBound
    {ι κ β g : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (sourceOwner : ι → β) (targetOwner : κ → β)
    (coefficient : β → β → ℝ) : Prop :=
  (∀ targetBlock sourceBlock, 0 ≤ coefficient targetBlock sourceBlock) ∧
    ∀ sourceBlock f,
      FinitePiLpSupportedInOwner sourceOwner sourceBlock f →
      ∀ targetBlock,
        finitePiLpSupNorm
            (finitePiLpOwnerPart targetOwner targetBlock (T f)) ≤
          coefficient targetBlock sourceBlock * finitePiLpSupNorm f

/-- Output-fixed weighted row of a nonnegative owner-block coefficient
matrix.  This is the orientation that acts on the global supremum norm. -/
def FiniteOwnerWeightedRowBound
    {β : Type*} [Fintype β]
    (coefficient : β → β → ℝ) (dist : β → β → ℕ)
    (A rate : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ rate ∧
    ∀ targetBlock,
      ∑ sourceBlock : β,
          Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            coefficient targetBlock sourceBlock ≤ A

/-- Bundled owner-fibre kernel action and its output-fixed weighted row. -/
def FinitePiLpTypedOwnerWeightedSupKernelBound
    {ι κ β g : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (sourceOwner : ι → β) (targetOwner : κ → β)
    (coefficient : β → β → ℝ) (dist : β → β → ℕ)
    (A rate : ℝ) : Prop :=
  FinitePiLpTypedOwnerSupKernelBound T sourceOwner targetOwner coefficient ∧
    FiniteOwnerWeightedRowBound coefficient dist A rate

/-- Literal coefficient matrix supplied by a block-localized exponential
estimate. -/
noncomputable def finiteOwnerExponentialCoefficient
    {β : Type*} (dist : β → β → ℕ) (A decay : ℝ)
    (targetBlock sourceBlock : β) : ℝ :=
  A * Real.exp (-(decay * (dist targetBlock sourceBlock : ℝ)))

/-- A block-localized estimate supplies the literal nonnegative coefficient
matrix between complete owner fibres. -/
theorem finitePiLpTypedOwnerSupKernelBound_of_blockLocalized
    {ι κ β g : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (sourceOwner : ι → β) (targetOwner : κ → β)
    (dist : β → β → ℕ) {A decay : ℝ}
    (hT : FinitePiLpTypedBlockLocalizedSupBound T sourceOwner targetOwner
      dist A decay) :
    FinitePiLpTypedOwnerSupKernelBound T sourceOwner targetOwner
      (finiteOwnerExponentialCoefficient dist A decay) := by
  classical
  refine ⟨?_, ?_⟩
  · intro targetBlock sourceBlock
    exact mul_nonneg hT.1 (Real.exp_pos _).le
  · intro sourceBlock f hf targetBlock
    apply finitePiLpSupNorm_le_of_norm_apply_le
    intro target
    rw [finitePiLpOwnerPart_apply]
    by_cases htarget : targetOwner target = targetBlock
    · rw [if_pos htarget]
      simpa [finiteOwnerExponentialCoefficient, htarget] using
        hT.2.2 sourceBlock f hf target
    · rw [if_neg htarget, norm_zero]
      exact mul_nonneg
        (mul_nonneg hT.1 (Real.exp_pos _).le)
        (finitePiLpSupNorm_nonneg f)

/-- Reserving a strict rate gap converts a pointwise exponential coefficient
matrix into an output-fixed weighted row.  The only price is the supplied
volume-uniform shell sum at `decay - rate`. -/
theorem finiteOwnerWeightedRowBound_exponential_of_shell
    {β : Type*} [Fintype β]
    (dist : β → β → ℕ) {A decay rate S : ℝ}
    (hA : 0 ≤ A) (hrate : 0 ≤ rate) (hgap : rate < decay)
    (hS : 0 ≤ S)
    (hshell : ∀ targetBlock,
      ∑ sourceBlock : β,
        Real.exp (-((decay - rate) *
          (dist targetBlock sourceBlock : ℝ))) ≤ S) :
    FiniteOwnerWeightedRowBound
      (finiteOwnerExponentialCoefficient dist A decay)
      dist (A * S) rate := by
  refine ⟨mul_nonneg hA hS, hrate, ?_⟩
  intro targetBlock
  calc
    ∑ sourceBlock : β,
          Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            finiteOwnerExponentialCoefficient dist A decay
              targetBlock sourceBlock =
        A * ∑ sourceBlock : β,
          Real.exp (-((decay - rate) *
            (dist targetBlock sourceBlock : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sourceBlock _hsource
      unfold finiteOwnerExponentialCoefficient
      calc
        Real.exp (rate * (dist targetBlock sourceBlock : ℝ)) *
            (A * Real.exp (-(decay *
              (dist targetBlock sourceBlock : ℝ)))) =
          A * (Real.exp (rate *
              (dist targetBlock sourceBlock : ℝ)) *
            Real.exp (-(decay *
              (dist targetBlock sourceBlock : ℝ)))) := by ring
        _ = A * Real.exp
            (rate * (dist targetBlock sourceBlock : ℝ) +
              -(decay * (dist targetBlock sourceBlock : ℝ))) := by
          rw [Real.exp_add]
        _ = A * Real.exp (-((decay - rate) *
              (dist targetBlock sourceBlock : ℝ))) := by
          congr 2
          ring
    _ ≤ A * S := mul_le_mul_of_nonneg_left (hshell targetBlock) hA

/-- One block-localized exponential estimate therefore gives the complete
owner-fibre weighted-sup certificate at every strictly smaller rate. -/
theorem finitePiLpTypedOwnerWeightedSupKernelBound_of_blockLocalized
    {ι κ β g : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (sourceOwner : ι → β) (targetOwner : κ → β)
    (dist : β → β → ℕ) {A decay rate S : ℝ}
    (hT : FinitePiLpTypedBlockLocalizedSupBound T sourceOwner targetOwner
      dist A decay)
    (hrate : 0 ≤ rate) (hgap : rate < decay) (hS : 0 ≤ S)
    (hshell : ∀ targetBlock,
      ∑ sourceBlock : β,
        Real.exp (-((decay - rate) *
          (dist targetBlock sourceBlock : ℝ))) ≤ S) :
    FinitePiLpTypedOwnerWeightedSupKernelBound T sourceOwner targetOwner
      (finiteOwnerExponentialCoefficient dist A decay)
      dist (A * S) rate := by
  exact ⟨finitePiLpTypedOwnerSupKernelBound_of_blockLocalized
      T sourceOwner targetOwner dist hT,
    finiteOwnerWeightedRowBound_exponential_of_shell
      dist hT.1 hrate hgap hS hshell⟩

end

end YangMills.RG
