import YangMills.RG.BalabanCMP89SourceNeumannTwoLevelPoincareComposition

/-!
# Recursive CMP89 Neumann Poincare coefficient

This module records the exact scalar recurrence required to extend the sealed
two-scale Neumann Poincare argument through a finite retained prefix.  A single
inductive budget contains every adjacent feedback contraction.  It does not
accept a family of Poincare certificates, backgrounds or averaging operators.
-/

namespace YangMills.RG

noncomputable section

/-- Coefficient of a retained Neumann prefix with `steps + 1` scales, starting
at `level`.  The zero-step case is the literal one-scale coefficient.  Each
successor uses the already constructed coefficient of the complete coarse
tail, rather than a second one-scale surrogate. -/
noncomputable def cmp89SourceNeumannRecursivePoincareCoefficient
    (oneScale derivative feedback : ℕ → ℝ) : ℕ → ℕ → ℝ
  | level, 0 => oneScale level
  | level, steps + 1 =>
      cmp89SourceNeumannTwoLevelPoincareConstant
        (oneScale level)
        (cmp89SourceNeumannRecursivePoincareCoefficient
          oneScale derivative feedback (level + 1) steps)
        (derivative level)
        (feedback level)

/-- One proof-carrying record of every adjacent contraction in a finite
retained prefix.  The tail is stored recursively, so omitting an intermediate
scale or supplying unrelated per-prefix certificates is impossible. -/
inductive CMP89SourceNeumannRecursiveContractionBudget
    (oneScale derivative feedback : ℕ → ℝ) : ℕ → ℕ → Type
  | last (level : ℕ)
      (oneScale_pos : 0 < oneScale level) :
      CMP89SourceNeumannRecursiveContractionBudget
        oneScale derivative feedback level 0
  | step (level steps : ℕ)
      (fine_pos : 0 < oneScale level)
      (derivative_nonneg : 0 ≤ derivative level)
      (feedback_small :
        oneScale level *
            cmp89SourceNeumannRecursivePoincareCoefficient
              oneScale derivative feedback (level + 1) steps *
            feedback level < 1)
      (tail : CMP89SourceNeumannRecursiveContractionBudget
        oneScale derivative feedback (level + 1) steps) :
      CMP89SourceNeumannRecursiveContractionBudget
        oneScale derivative feedback level (steps + 1)

/-- Every recursive coefficient is strictly positive once the single terminal
budget carries the literal adjacent contractions.  No global upper bound is
inferred: positivity uses each denominator exactly where it occurs. -/
theorem cmp89SourceNeumannRecursivePoincareCoefficient_pos
    {oneScale derivative feedback : ℕ → ℝ} {level steps : ℕ}
    (budget : CMP89SourceNeumannRecursiveContractionBudget
      oneScale derivative feedback level steps) :
    0 < cmp89SourceNeumannRecursivePoincareCoefficient
      oneScale derivative feedback level steps := by
  induction budget with
  | last level hpos =>
      simpa [cmp89SourceNeumannRecursivePoincareCoefficient] using hpos
  | step level steps hfine hderivative hsmall tail ih =>
      simp only [cmp89SourceNeumannRecursivePoincareCoefficient,
        cmp89SourceNeumannTwoLevelPoincareConstant]
      have hden :
          0 < 1 - oneScale level *
            cmp89SourceNeumannRecursivePoincareCoefficient
              oneScale derivative feedback (level + 1) steps *
            feedback level :=
        sub_pos.mpr hsmall
      have hinterior :
          0 < 1 +
            cmp89SourceNeumannRecursivePoincareCoefficient
                oneScale derivative feedback (level + 1) steps *
              derivative level :=
        add_pos_of_pos_of_nonneg zero_lt_one
          (mul_nonneg ih.le hderivative)
      have hnum :
          0 < oneScale level *
                (1 +
                  cmp89SourceNeumannRecursivePoincareCoefficient
                      oneScale derivative feedback (level + 1) steps *
                    derivative level) +
              oneScale level *
                cmp89SourceNeumannRecursivePoincareCoefficient
                  oneScale derivative feedback (level + 1) steps :=
        add_pos_of_pos_of_nonneg
          (mul_pos hfine hinterior)
          (mul_nonneg hfine.le ih.le)
      exact div_pos hnum hden

/-- The head denominator of a nontrivial retained prefix is positive by the
first literal contraction stored in its recursive terminal budget. -/
theorem cmp89SourceNeumannRecursivePoincareCoefficient_headDenominator_pos
    {oneScale derivative feedback : ℕ → ℝ} {level steps : ℕ}
    (budget : CMP89SourceNeumannRecursiveContractionBudget
      oneScale derivative feedback level (steps + 1)) :
    0 < 1 - oneScale level *
      cmp89SourceNeumannRecursivePoincareCoefficient
        oneScale derivative feedback (level + 1) steps *
      feedback level := by
  cases budget with
  | step _ _ _ _ hsmall _ => exact sub_pos.mpr hsmall

end

end YangMills.RG
