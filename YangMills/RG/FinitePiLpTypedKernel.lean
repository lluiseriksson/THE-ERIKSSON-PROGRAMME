/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpCombesThomas

/-!
# Rectangular kernel predicates on finite dependent-index fields

Consecutive CMP99 regions have different site subtypes.  These predicates
record entry bounds, finite range and exponential decay without transporting
either operator through an equality of carriers.
-/

namespace YangMills.RG

noncomputable section

/-- Entrywise bound for a rectangular finite `PiLp` operator. -/
def FinitePiLpTypedKernelBound
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (weight : κ → ι → ℝ) : Prop :=
  ∀ source target (v : g),
    ‖C (singleFinitePiLp source v) target‖ ≤
      weight target source * ‖v‖

/-- Exact finite range for a rectangular finite `PiLp` operator. -/
def FinitePiLpTypedFiniteRange
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) (R : ℕ) : Prop :=
  ∀ source target (v : g), R < dist target source →
    C (singleFinitePiLp source v) target = 0

/-- Fixed-rate exponential bound for a rectangular finite `PiLp` operator. -/
def FinitePiLpTypedExponentialKernelBound
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) (A rate : ℝ) : Prop :=
  0 ≤ A ∧ 0 < rate ∧
    ∀ source target (v : g),
      ‖C (singleFinitePiLp source v) target‖ ≤
        A * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖

/-- The operator norm supplies a rectangular entry budget. -/
theorem finitePiLpTypedKernelBound_const_opNorm
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g) :
    FinitePiLpTypedKernelBound C (fun _ _ => ‖C‖) := by
  intro source target v
  calc
    ‖C (singleFinitePiLp source v) target‖ ≤
        ‖C (singleFinitePiLp source v)‖ := PiLp.norm_apply_le _ target
    _ ≤ ‖C‖ * ‖singleFinitePiLp source v‖ :=
      ContinuousLinearMap.le_opNorm C _
    _ = ‖C‖ * ‖v‖ := by rw [norm_singleFinitePiLp]

/-- A square exponential bound is a rectangular bound with identical index
types. -/
theorem finitePiLpTypedExponentialKernelBound_of_square
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {C : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    {dist : ι → ι → ℕ} {A rate : ℝ}
    (hC : FinitePiLpExponentialKernelBound C dist A rate) :
    FinitePiLpTypedExponentialKernelBound C dist A rate := hC

end

end YangMills.RG
