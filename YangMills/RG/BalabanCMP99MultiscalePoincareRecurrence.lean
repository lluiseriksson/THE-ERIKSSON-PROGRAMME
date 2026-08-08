/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib

/-!
# Backward recurrence for the CMP99 multiscale Poincare estimate

The one-scale physical estimate controls the field on `Omega_r` by its
derivative, its mass on `Lambda_r`, and the corresponding field on
`Omega_(r+1)`.  This file performs only the finite backward iteration.  It
keeps the derivative cost and the shell cost as explicit sequences, so no
analytic input can be hidden in a single unnamed constant.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Backward cost obtained by iterating a one-step estimate through `n + 1`
physical strata. -/
def cmp99MultiscalePoincareBackwardBound :
    ℕ → ℝ → (ℕ → ℝ) → (ℕ → ℝ) → ℝ
  | 0, _coupling, derivativeCost, shellCost =>
      derivativeCost 0 + shellCost 0
  | n + 1, coupling, derivativeCost, shellCost =>
      derivativeCost 0 + shellCost 0 +
        coupling * cmp99MultiscalePoincareBackwardBound n coupling
          (fun r => derivativeCost (r + 1))
          (fun r => shellCost (r + 1))

/-- Exact finite backward induction.  The hypotheses are precisely the
terminal estimate and the `n` physical transition estimates. -/
theorem cmp99MultiscalePoincareBackwardBound_controls
    (n : ℕ) (coupling : ℝ) (A derivativeCost shellCost : ℕ → ℝ)
    (hcoupling : 0 ≤ coupling)
    (hstep : ∀ r < n,
      A r ≤ derivativeCost r + shellCost r + coupling * A (r + 1))
    (hterminal : A n ≤ derivativeCost n + shellCost n) :
    A 0 ≤ cmp99MultiscalePoincareBackwardBound n coupling
      derivativeCost shellCost := by
  induction n generalizing A derivativeCost shellCost with
  | zero =>
      simpa [cmp99MultiscalePoincareBackwardBound] using hterminal
  | succ n ih =>
      have hhead := hstep 0 (Nat.zero_lt_succ n)
      have htailStep : ∀ r < n,
          A (r + 1) ≤ derivativeCost (r + 1) + shellCost (r + 1) +
            coupling * A ((r + 1) + 1) := by
        intro r hr
        exact hstep (r + 1) (by omega)
      have htailTerminal :
          A (n + 1) ≤ derivativeCost (n + 1) + shellCost (n + 1) := by
        simpa using hterminal
      have htail := ih
        (fun r => A (r + 1))
        (fun r => derivativeCost (r + 1))
        (fun r => shellCost (r + 1))
        htailStep htailTerminal
      calc
        A 0 ≤ derivativeCost 0 + shellCost 0 + coupling * A (0 + 1) := hhead
        _ ≤ derivativeCost 0 + shellCost 0 + coupling *
            cmp99MultiscalePoincareBackwardBound n coupling
              (fun r => derivativeCost (r + 1))
              (fun r => shellCost (r + 1)) := by
          gcongr
        _ = cmp99MultiscalePoincareBackwardBound (n + 1) coupling
            derivativeCost shellCost := rfl

/-- Closed form of the backward cost.  This exposes every scale coefficient:
the cost at level `r` is multiplied by `coupling ^ r`. -/
theorem cmp99MultiscalePoincareBackwardBound_eq_sum
    (n : ℕ) (coupling : ℝ) (derivativeCost shellCost : ℕ → ℝ) :
    cmp99MultiscalePoincareBackwardBound n coupling derivativeCost shellCost =
      ∑ r ∈ Finset.range (n + 1),
        coupling ^ r * (derivativeCost r + shellCost r) := by
  induction n generalizing derivativeCost shellCost with
  | zero =>
      simp [cmp99MultiscalePoincareBackwardBound]
  | succ n ih =>
      rw [cmp99MultiscalePoincareBackwardBound, ih]
      rw [Finset.sum_range_succ' _ (n + 1)]
      have hsum : coupling *
          (∑ r ∈ Finset.range (n + 1),
            coupling ^ r *
              (derivativeCost (r + 1) + shellCost (r + 1))) =
          ∑ r ∈ Finset.range (n + 1),
            coupling ^ (r + 1) *
              (derivativeCost (r + 1) + shellCost (r + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _hr
        ring
      rw [hsum]
      ring

end

end YangMills.RG
