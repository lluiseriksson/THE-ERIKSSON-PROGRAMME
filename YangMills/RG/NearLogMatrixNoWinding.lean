/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLogUnitaryCFC
import YangMills.RG.BalabanCMP116MatrixTraceL2OpNorm

/-!
# The explicit no-winding frontier for matrix Mercator logarithms

For a special unitary matrix, determinant one quantizes the trace of a
principal logarithm in `2π i ℤ`; it does not by itself force that integer to
vanish in arbitrary dimension.  This file formalizes the second, genuinely
elementary half of the argument:

* the complex trace costs at most the matrix dimension in L2 operator norm;
* a `2π i ℤ`-quantized trace of norm strictly below `2π` is zero;
* hence the CMP99 Mercator logarithm is traceless once quantization and the
  explicit no-winding norm budget are supplied.

The producer of trace quantization from `det D = 1` remains visible.  Mathlib
currently records `det (NormedSpace.exp X) = exp (trace X)` as a TODO, so this
file does not hide that gap behind a postulate or a renamed hypothesis.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator ContinuousFunctionalCalculus

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

/-- The full complex trace costs at most the matrix dimension in L2 operator
norm. -/
theorem norm_matrix_trace_le_card_mul_l2_opNorm
    (X : Matrix (Fin Nc) (Fin Nc) ℂ) :
    ‖X.trace‖ ≤ (Nc : ℝ) * ‖X‖ := by
  unfold Matrix.trace
  calc
    ‖∑ i : Fin Nc, X i i‖ ≤ ∑ i : Fin Nc, ‖X i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin Nc, ‖X‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_matrix_entry_le_l2_opNorm X i i
    _ = (Nc : ℝ) * ‖X‖ := by simp

/-- The trace is quantized in integral multiples of `2π i`.  This is the
precise output that the future determinant/exponential bridge must produce
from special-unitary data. -/
def MatrixTraceQuantized (X : Matrix (Fin Nc) (Fin Nc) ℂ) : Prop :=
  ∃ k : ℤ, X.trace = ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I

/-- A quantized trace strictly inside the first nonzero winding radius has
zero winding. -/
theorem trace_eq_zero_of_quantized_of_norm_lt_two_pi
    (X : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hquant : MatrixTraceQuantized X)
    (hsmall : ‖X.trace‖ < 2 * Real.pi) :
    X.trace = 0 := by
  rcases hquant with ⟨k, hk⟩
  by_cases hk0 : k = 0
  · subst k
    simpa using hk
  · have hint : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
    have habs : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast hint
    rw [hk, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity),
      abs_of_pos Real.pi_pos] at hsmall
    nlinarith [Real.pi_pos]

/-- **No-winding reduction for the physical Mercator coordinate.**  If the
trace quantization producer and the strict dimension-times-logarithm budget
are available, the near-identity unitary logarithm is traceless.  The previous
CFC endpoint identifies this logarithm with `I • Unitary.argSelfAdjoint D`, so an
angular budget can discharge `hnoWinding` without being duplicated here. -/
theorem trace_nearLog_unitary_sub_one_eq_zero_of_quantized_of_noWinding
    (D : unitary (Matrix (Fin Nc) (Fin Nc) ℂ))
    (hquant : MatrixTraceQuantized
      (nearLog ((D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)))
    (hnoWinding : (Nc : ℝ) *
      ‖nearLog ((D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    Matrix.trace (nearLog ((D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) = 0 := by
  apply trace_eq_zero_of_quantized_of_norm_lt_two_pi _ hquant
  calc
    ‖Matrix.trace (nearLog ((D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1))‖
        ≤ (Nc : ℝ) * ‖nearLog ((D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ :=
      norm_matrix_trace_le_card_mul_l2_opNorm _
    _ < 2 * Real.pi := hnoWinding

end

end YangMills.RG
