/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80GlobalPotential

/-!
# Ordered minimizer telescoping for CMP102 equation (80)

The equation-(80) potential is nonlinear in the rectangular minimizer.
Consequently, a convergent walk expansion of the minimizer cannot simply be
passed termwise through the potential.  This module gives the exact finite
ordered replacement: add one minimizer term at a time and telescope the
literal four-term potential.

No infinite sums are exchanged.  No connectivity is asserted for an
isolated minimizer term.  The anchor-dependent potential and the new walk
term first meet inside one exact increment; localization belongs at that
level.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- Exact change of the CMP102 equation-(80) potential when a rectangular
minimizer `T` is added after a prefix `P`.  The quadratic cross terms and
the nonlinear `V₀` difference remain literal. -/
noncomputable def cmp102Eq80MinimizerIncrement
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (P T : F →L[ℝ] E) (Δπ : E →L[ℝ] E)
    (J A' : E) : ℝ :=
  - inner ℝ (T (D₃ A')) J
  - inner ℝ A' (Δπ (T (D A')))
  + (1 / 2 : ℝ) *
      (inner ℝ (T (D A')) (Δπ (P (D A'))) +
       inner ℝ (P (D A')) (Δπ (T (D A'))) +
       inner ℝ (T (D A')) (Δπ (T (D A'))))
  + (V₀ (A' - (P (D A') + T (D A'))) -
      V₀ (A' - P (D A')))

/-- One exact ordered increment.  This is a purely algebraic identity and
does not require differentiability or a convergence hypothesis. -/
theorem cmp102Eq80GlobalPotential_add_minimizer
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (P T : F →L[ℝ] E) (Δπ : E →L[ℝ] E)
    (J A' : E) :
    cmp102Eq80GlobalPotential D D₃ V₀ (P + T) Δπ J A' =
      cmp102Eq80GlobalPotential D D₃ V₀ P Δπ J A' +
        cmp102Eq80MinimizerIncrement D D₃ V₀ P T Δπ J A' := by
  simp only [cmp102Eq80GlobalPotential,
    cmp102Eq80MinimizerIncrement,
    ContinuousLinearMap.add_apply, map_add,
    inner_add_left, inner_add_right]
  ring

/-- Ordered prefix of a minimizer series. -/
noncomputable def cmp102Eq80MinimizerPartialSum
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (term : ℕ → (F →L[ℝ] E)) (n : ℕ) : F →L[ℝ] E :=
  ∑ i ∈ Finset.range n, term i

@[simp]
theorem cmp102Eq80MinimizerPartialSum_zero
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (term : ℕ → (F →L[ℝ] E)) :
    cmp102Eq80MinimizerPartialSum term 0 = 0 := by
  simp [cmp102Eq80MinimizerPartialSum]

theorem cmp102Eq80MinimizerPartialSum_succ
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (term : ℕ → (F →L[ℝ] E)) (n : ℕ) :
    cmp102Eq80MinimizerPartialSum term (n + 1) =
      cmp102Eq80MinimizerPartialSum term n + term n := by
  simp [cmp102Eq80MinimizerPartialSum, Finset.sum_range_succ]

/-- Exact finite ordered telescoping of the nonlinear equation-(80)
potential along minimizer partial sums. -/
theorem cmp102Eq80GlobalPotential_partialSum_eq_sum_increments
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (term : ℕ → (F →L[ℝ] E))
    (Δπ : E →L[ℝ] E) (J A' : E) :
    ∀ n : ℕ,
      cmp102Eq80GlobalPotential D D₃ V₀
          (cmp102Eq80MinimizerPartialSum term n) Δπ J A' =
        cmp102Eq80GlobalPotential D D₃ V₀ 0 Δπ J A' +
          ∑ i ∈ Finset.range n,
            cmp102Eq80MinimizerIncrement D D₃ V₀
              (cmp102Eq80MinimizerPartialSum term i) (term i)
              Δπ J A' := by
  intro n
  induction n with
  | zero =>
      simp [cmp102Eq80MinimizerPartialSum]
  | succ n ih =>
      rw [cmp102Eq80MinimizerPartialSum_succ,
        cmp102Eq80GlobalPotential_add_minimizer, ih,
        Finset.sum_range_succ]
      ring

end

end YangMills.RG
