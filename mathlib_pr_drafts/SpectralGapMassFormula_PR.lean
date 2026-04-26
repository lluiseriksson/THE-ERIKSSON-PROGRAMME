/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Spectral-gap mass formula: `0 < log(opNorm / λ)` when `0 < λ < opNorm`

This module proves the elementary but useful spectral-gap → mass-gap
lemma

  `mass_gap_pos_of_lambda_lt_opNorm`:
  if `0 < λ < opNorm`, then `0 < Real.log (opNorm / λ)`.

This is the standard formula relating a transfer-matrix spectral gap
(`opNorm - λ > 0`) to a mass gap (`m = log(opNorm/λ) > 0`) in lattice
gauge theory. While the constituents (`Real.log_pos`, `lt_div_iff`)
are all in Mathlib, the packaged lemma in this exact form is missing
and would be useful in numerical analysis, lattice physics, and any
application of Perron-Frobenius / transfer-matrix theory.

## Strategy

The proof is one line: from `0 < λ < opNorm`, dividing both sides by
`λ` gives `1 < opNorm/λ`, and `Real.log_pos` then yields
`0 < log(opNorm/λ)`.

## PR submission notes

This file uses only `Mathlib.Analysis.SpecialFunctions.Log.Basic`. It
is a small, self-contained one-theorem contribution suitable for direct
addition to Mathlib's `Real.log` library.

The theorem name `mass_gap_pos_of_lambda_lt_opNorm` reflects the
physics interpretation, but the lemma itself is purely about real
logarithms and would equally fit in a numerical-analysis namespace.

**Status (2026-04-25)**: produced in the workspace but not yet
verified with `lake build` (workspace lacks `lake`). The proof is
elementary (one application of `Real.log_pos` after `lt_div_iff`).
-/

namespace Real

/-! ## §1. The main lemma -/

/-- **Spectral-gap mass formula**: if `0 < λ < opNorm`, then
    `Real.log (opNorm / λ) > 0`.

    This packages the standard transfer-matrix spectral-gap to
    mass-gap conversion: in lattice gauge theory, when the second
    eigenvalue `λ` of a transfer matrix is strictly less than the
    operator norm `opNorm`, the mass gap

      `m := log(opNorm / λ)`

    is strictly positive. -/
theorem mass_gap_pos_of_lambda_lt_opNorm
    (opNorm lam : ℝ) (h_lam_pos : 0 < lam) (h_strict : lam < opNorm) :
    0 < Real.log (opNorm / lam) := by
  -- Step 1: from lam < opNorm and lam > 0, conclude 1 < opNorm/lam.
  have h_one_lt : 1 < opNorm / lam := by
    rw [lt_div_iff₀ h_lam_pos]
    linarith
  -- Step 2: apply Real.log_pos.
  exact Real.log_pos h_one_lt

#print axioms mass_gap_pos_of_lambda_lt_opNorm

/-! ## §2. Strict-inequality variant -/

/-- **Strict variant**: under the same hypotheses, the mass gap is
    bounded below by `log(opNorm) - log(lam)`. -/
theorem mass_gap_eq_log_diff
    (opNorm lam : ℝ) (h_lam_pos : 0 < lam) (h_op_pos : 0 < opNorm) :
    Real.log (opNorm / lam) = Real.log opNorm - Real.log lam := by
  exact Real.log_div (ne_of_gt h_op_pos) (ne_of_gt h_lam_pos)

#print axioms mass_gap_eq_log_diff

/-! ## §3. Numerical instance: `opNorm = 1, lam = 1/2` -/

/-- **Numerical instance**: at `opNorm = 1, lam = 1/2`, the mass gap
    is `log 2 > 0` (a standard reference case in lattice physics). -/
theorem mass_gap_at_one_half : 0 < Real.log (1 / (1/2 : ℝ)) := by
  apply mass_gap_pos_of_lambda_lt_opNorm
  · norm_num
  · norm_num

/-- **Equivalent reformulation**: `log(1/(1/2)) = log 2 > 0`. -/
theorem log_one_div_half_eq_log_two :
    Real.log (1 / (1/2 : ℝ)) = Real.log 2 := by
  norm_num

#print axioms mass_gap_at_one_half

/-! ## §4. Monotonicity: smaller `lam` gives larger mass gap -/

/-- **Monotonicity in `lam`**: shrinking `lam` (while keeping it
    positive) increases the mass gap. -/
theorem mass_gap_antitone_in_lam
    (opNorm lam1 lam2 : ℝ)
    (h_lam1_pos : 0 < lam1) (h_lam2_pos : 0 < lam2)
    (h_op_pos : 0 < opNorm)
    (h_lam_lt : lam1 < lam2) :
    Real.log (opNorm / lam2) < Real.log (opNorm / lam1) := by
  apply Real.log_lt_log
  · exact div_pos h_op_pos h_lam2_pos
  · exact (div_lt_div_iff_of_pos_left h_op_pos h_lam2_pos h_lam1_pos).mpr h_lam_lt

#print axioms mass_gap_antitone_in_lam

end Real
