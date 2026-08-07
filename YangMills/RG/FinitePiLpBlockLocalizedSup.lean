/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedKernel

/-!
# PRE-VALIDATION: block-localized sup-norm action on finite PiLp fields

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

CMP99 (3.42) and (3.89) quantify an arbitrary field supported in one
localization block and measure that field in the finite supremum norm.  The
existing `FinitePiLpTypedExponentialKernelBound` instead tests only one
coordinate probe.  This module records the stronger quantifier literally.

The owner maps and their distance remain explicit so the source localization
scale cannot be confused with a coarser regional-cell scale.  This is only a
generic contract and its elementary algebra.  It does not prove that a
physical Green, defect, or three-species operator satisfies the contract.
-/

namespace YangMills.RG

noncomputable section

/-- Finite supremum norm of a counting-Hilbert field.  The ambient Hilbert
norm of `FinitePiLpField` remains unchanged; this is the separate norm used
by the source-localized CMP99 estimates. -/
noncomputable def finitePiLpSupNorm
    {ι g : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup g]
    (f : FinitePiLpField ι g) : ℝ :=
  (Finset.univ.image fun i : ι => ‖f i‖).max' (by simp)

/-- Every coordinate is bounded by the finite field supremum norm. -/
theorem norm_apply_le_finitePiLpSupNorm
    {ι g : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup g]
    (f : FinitePiLpField ι g) (i : ι) :
    ‖f i‖ ≤ finitePiLpSupNorm f := by
  unfold finitePiLpSupNorm
  exact Finset.le_max' _ _ (by simp)

/-- The finite field supremum norm is nonnegative. -/
theorem finitePiLpSupNorm_nonneg
    {ι g : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup g]
    (f : FinitePiLpField ι g) :
    0 ≤ finitePiLpSupNorm f := by
  let i : ι := Classical.choice inferInstance
  exact (norm_nonneg (f i)).trans (norm_apply_le_finitePiLpSupNorm f i)

/-- A field is supported in one owner fibre when it vanishes at every index
whose owner differs from the selected source block. -/
def FinitePiLpSupportedInOwner
    {ι β g : Type*} [Zero g]
    (sourceOwner : ι → β) (owner : β)
    (f : FinitePiLpField ι g) : Prop :=
  ∀ source, sourceOwner source ≠ owner → f source = 0

/-- Source-facing localized action estimate.

Unlike an entrywise kernel bound, this predicate quantifies one arbitrary
field supported in a complete source-owner fibre.  Its right-hand side uses
the finite supremum norm and the distance between the output owner and that
one selected source owner. -/
def FinitePiLpTypedBlockLocalizedSupBound
    {ι κ β g : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (sourceOwner : ι → β) (targetOwner : κ → β)
    (dist : β → β → ℕ) (A rate : ℝ) : Prop :=
  0 ≤ A ∧ 0 < rate ∧
    ∀ owner f, FinitePiLpSupportedInOwner sourceOwner owner f →
      ∀ target,
        ‖C f target‖ ≤
          A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
            finitePiLpSupNorm f

/-- Two localized-action bounds at one owner metric and rate add without a
cardinality factor. -/
theorem finitePiLpTypedBlockLocalizedSupBound_add
    {ι κ β g : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {C D : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {sourceOwner : ι → β} {targetOwner : κ → β}
    {dist : β → β → ℕ} {A B rate : ℝ}
    (hC : FinitePiLpTypedBlockLocalizedSupBound C sourceOwner targetOwner
      dist A rate)
    (hD : FinitePiLpTypedBlockLocalizedSupBound D sourceOwner targetOwner
      dist B rate) :
    FinitePiLpTypedBlockLocalizedSupBound (C + D) sourceOwner targetOwner
      dist (A + B) rate := by
  refine ⟨add_nonneg hC.1 hD.1, hC.2.1, ?_⟩
  intro owner f hf target
  have hCf := hC.2.2 owner f hf target
  have hDf := hD.2.2 owner f hf target
  change ‖C f target + D f target‖ ≤ _
  calc
    ‖C f target + D f target‖ ≤ ‖C f target‖ + ‖D f target‖ :=
      norm_add_le _ _
    _ ≤ A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f +
        B * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f := add_le_add hCf hDf
    _ = (A + B) *
        Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f := by ring

end

end YangMills.RG
