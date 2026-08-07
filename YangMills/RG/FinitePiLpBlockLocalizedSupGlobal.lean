/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpBlockLocalizedSupAlgebra

/-!
# PRE-VALIDATION: global supremum action from owner-localized decay

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

A block-localized estimate controls an arbitrary field supported in one
complete owner fibre.  This module decomposes an arbitrary field into those
owner fibres and sums the resulting exponential decay by a supplied
volume-uniform owner-shell bound.

No coordinate-probe expansion or cardinality of a fine fibre enters.  This
is norm algebra only: it does not prove that a physical defect has small
amplitude, construct a Neumann inverse, or identify the finite supremum norm
with the ambient Hilbert norm.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- The part of a finite field supported on one exact owner fibre. -/
noncomputable def finitePiLpOwnerPart
    {ι β g : Type*} [Fintype ι] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (sourceOwner : ι → β) (owner : β) (f : FinitePiLpField ι g) :
    FinitePiLpField ι g :=
  finitePiLpScalarMultiplier (g := g)
    (fun source => if sourceOwner source = owner then 1 else 0) f

/-- The owner part is the original value on its fibre and zero elsewhere. -/
theorem finitePiLpOwnerPart_apply
    {ι β g : Type*} [Fintype ι] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (sourceOwner : ι → β) (owner : β) (f : FinitePiLpField ι g)
    (source : ι) :
    finitePiLpOwnerPart sourceOwner owner f source =
      if sourceOwner source = owner then f source else 0 := by
  rw [finitePiLpOwnerPart, finitePiLpScalarMultiplier_apply]
  by_cases hsource : sourceOwner source = owner
  · simp [hsource]
  · simp [hsource]

/-- Each owner part is supported in the selected fibre. -/
theorem finitePiLpOwnerPart_supported
    {ι β g : Type*} [Fintype ι] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (sourceOwner : ι → β) (owner : β) (f : FinitePiLpField ι g) :
    FinitePiLpSupportedInOwner sourceOwner owner
      (finitePiLpOwnerPart sourceOwner owner f) := by
  intro source hsource
  rw [finitePiLpOwnerPart_apply, if_neg hsource]

/-- Owner projection cannot increase the finite supremum norm. -/
theorem finitePiLpSupNorm_ownerPart_le
    {ι β g : Type*} [Fintype ι] [Nonempty ι] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (sourceOwner : ι → β) (owner : β) (f : FinitePiLpField ι g) :
    finitePiLpSupNorm (finitePiLpOwnerPart sourceOwner owner f) ≤
      finitePiLpSupNorm f := by
  apply finitePiLpSupNorm_scalarMultiplier_le
  intro source
  by_cases hsource : sourceOwner source = owner
  · simp [hsource]
  · simp [hsource]

/-- Summing all exact owner parts reconstructs the original field. -/
theorem sum_finitePiLpOwnerPart_eq
    {ι β g : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (sourceOwner : ι → β) (f : FinitePiLpField ι g) :
    ∑ owner, finitePiLpOwnerPart sourceOwner owner f = f := by
  apply PiLp.ext
  intro source
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp [finitePiLpOwnerPart_apply]

/-- A volume-uniform exponential owner-shell sum converts a block-localized
action estimate into a global finite-supremum action bound.  The factor is
`A * S`; neither the number of owners nor the size of an owner fibre appears.
-/
theorem finitePiLpSupNorm_map_le_of_blockLocalized
    {ι κ β g : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    [Fintype β] [DecidableEq β]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (sourceOwner : ι → β) (targetOwner : κ → β)
    (dist : β → β → ℕ) {A rate S : ℝ}
    (hC : FinitePiLpTypedBlockLocalizedSupBound C sourceOwner targetOwner
      dist A rate)
    (hS : 0 ≤ S)
    (hshell : ∀ target,
      ∑ owner : β,
        Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) ≤ S)
    (f : FinitePiLpField ι g) :
    finitePiLpSupNorm (C f) ≤ (A * S) * finitePiLpSupNorm f := by
  apply finitePiLpSupNorm_le_of_norm_apply_le
  intro target
  have hdecomp : f = ∑ owner, finitePiLpOwnerPart sourceOwner owner f :=
    (sum_finitePiLpOwnerPart_eq sourceOwner f).symm
  rw [hdecomp, map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  calc
    ‖∑ owner, C (finitePiLpOwnerPart sourceOwner owner f) target‖ ≤
        ∑ owner, ‖C (finitePiLpOwnerPart sourceOwner owner f) target‖ :=
      norm_sum_le _ _
    _ ≤ ∑ owner,
        A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f := by
      apply Finset.sum_le_sum
      intro owner _howner
      have hbound := hC.2.2 owner
        (finitePiLpOwnerPart sourceOwner owner f)
        (finitePiLpOwnerPart_supported sourceOwner owner f) target
      calc
        ‖C (finitePiLpOwnerPart sourceOwner owner f) target‖ ≤
            A * Real.exp (-(rate *
              (dist (targetOwner target) owner : ℝ))) *
              finitePiLpSupNorm
                (finitePiLpOwnerPart sourceOwner owner f) := hbound
        _ ≤ A * Real.exp (-(rate *
              (dist (targetOwner target) owner : ℝ))) *
              finitePiLpSupNorm f := by
          apply mul_le_mul_of_nonneg_left
          · exact finitePiLpSupNorm_ownerPart_le sourceOwner owner f
          · exact mul_nonneg hC.1 (Real.exp_pos _).le
    _ = (A * finitePiLpSupNorm f) *
        ∑ owner : β,
          Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro owner _howner
      ring
    _ ≤ (A * finitePiLpSupNorm f) * S := by
      apply mul_le_mul_of_nonneg_left (hshell target)
      exact mul_nonneg hC.1 (finitePiLpSupNorm_nonneg f)
    _ = (A * S) * finitePiLpSupNorm f := by ring

end

end YangMills.RG
