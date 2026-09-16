import tmp.P2cCoarseCovariance

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

Scratch-only scalar normalization gate for CMP85 (2.41)--(2.42).

The identities below are specialized to the exact source recurrence
`cmp99SourceMassParameter`; none is accepted as a caller-supplied law.
This file is not compiler evidence and is not imported by the tracked tree.
-/

namespace YangMills.RG

noncomputable section

/-- Printed coefficient `b_j = a_j * spacing_j^(-2)`. -/
def scratch_cmp85RecurrenceB (a L spacingJ : ℝ) (n : ℕ) : ℝ :=
  cmp99SourceMassParameter a L n * spacingJ⁻¹ ^ 2

/-- Printed one-step coefficient
`c_j = a * spacing_(j+1)^(-2)` with `spacing_(j+1)=L*spacing_j`. -/
def scratch_cmp85RecurrenceC (a L spacingJ : ℝ) : ℝ :=
  a * (L * spacingJ)⁻¹ ^ 2

/-- Printed next precision coefficient
`beta_j = a_(j+1) * spacing_(j+1)^(-2)`. -/
def scratch_cmp85RecurrenceBeta (a L spacingJ : ℝ) (n : ℕ) : ℝ :=
  cmp99SourceMassParameter a L (n + 1) * (L * spacingJ)⁻¹ ^ 2

theorem scratch_cmp85RecurrenceB_pos
    {a L spacingJ : ℝ} (ha : 0 < a) (hL : 0 < L)
    (hspacing : 0 < spacingJ) (n : ℕ) :
    0 < scratch_cmp85RecurrenceB a L spacingJ n := by
  unfold scratch_cmp85RecurrenceB
  exact mul_pos (cmp99SourceMassParameter_pos ha hL n)
    (pow_pos (inv_pos.mpr hspacing) 2)

theorem scratch_cmp85RecurrenceC_pos
    {a L spacingJ : ℝ} (ha : 0 < a) (hL : 0 < L)
    (hspacing : 0 < spacingJ) :
    0 < scratch_cmp85RecurrenceC a L spacingJ := by
  unfold scratch_cmp85RecurrenceC
  exact mul_pos ha (pow_pos (inv_pos.mpr (mul_pos hL hspacing)) 2)

theorem scratch_cmp85RecurrenceBeta_pos
    {a L spacingJ : ℝ} (ha : 0 < a) (hL : 0 < L)
    (hspacing : 0 < spacingJ) (n : ℕ) :
    0 < scratch_cmp85RecurrenceBeta a L spacingJ n := by
  unfold scratch_cmp85RecurrenceBeta
  exact mul_pos (cmp99SourceMassParameter_pos ha hL (n + 1))
    (pow_pos (inv_pos.mpr (mul_pos hL hspacing)) 2)

/-- Exact scalar Schur relation consumed by the generic block-Gaussian
algebra: `beta * (b+c) = b*c`. -/
theorem scratch_cmp85RecurrenceBeta_mul_add_eq_mul
    {a L spacingJ : ℝ} (ha : 0 < a) (hL : 0 < L)
    (hspacing : 0 < spacingJ) (n : ℕ) :
    scratch_cmp85RecurrenceBeta a L spacingJ n *
        (scratch_cmp85RecurrenceB a L spacingJ n +
          scratch_cmp85RecurrenceC a L spacingJ) =
      scratch_cmp85RecurrenceB a L spacingJ n *
        scratch_cmp85RecurrenceC a L spacingJ := by
  have han : 0 < cmp99SourceMassParameter a L n :=
    cmp99SourceMassParameter_pos ha hL n
  have hden : 0 < a * (L ^ 2)⁻¹ +
      cmp99SourceMassParameter a L n :=
    add_pos (mul_pos ha (inv_pos.mpr (sq_pos_of_pos hL))) han
  unfold scratch_cmp85RecurrenceBeta scratch_cmp85RecurrenceB
    scratch_cmp85RecurrenceC
  rw [cmp99SourceMassParameter_succ]
  field_simp [ha.ne', hL.ne', hspacing.ne', han.ne', hden.ne']
  ring

/-- The normalization used in (2.41):
`b+c = (a*a_j/a_(j+1))*spacing_j^(-2)`. -/
theorem scratch_cmp85Recurrence_add_eq_eq241Coefficient
    {a L spacingJ : ℝ} (ha : 0 < a) (hL : 0 < L)
    (hspacing : 0 < spacingJ) (n : ℕ) :
    scratch_cmp85RecurrenceB a L spacingJ n +
        scratch_cmp85RecurrenceC a L spacingJ =
      (a * cmp99SourceMassParameter a L n /
          cmp99SourceMassParameter a L (n + 1)) * spacingJ⁻¹ ^ 2 := by
  have han : 0 < cmp99SourceMassParameter a L n :=
    cmp99SourceMassParameter_pos ha hL n
  have hanext : 0 < cmp99SourceMassParameter a L (n + 1) :=
    cmp99SourceMassParameter_pos ha hL (n + 1)
  have hden : 0 < a * (L ^ 2)⁻¹ +
      cmp99SourceMassParameter a L n :=
    add_pos (mul_pos ha (inv_pos.mpr (sq_pos_of_pos hL))) han
  unfold scratch_cmp85RecurrenceB scratch_cmp85RecurrenceC
  rw [cmp99SourceMassParameter_succ]
  field_simp [ha.ne', hL.ne', hspacing.ne', han.ne', hanext.ne', hden.ne']
  ring

/-- The coefficient in (2.42) remains visibly
`a_j^2 * spacing_j^(-4)`. -/
theorem scratch_cmp85RecurrenceB_sq
    (a L spacingJ : ℝ) (n : ℕ) :
    scratch_cmp85RecurrenceB a L spacingJ n ^ 2 =
      cmp99SourceMassParameter a L n ^ 2 * spacingJ⁻¹ ^ 4 := by
  unfold scratch_cmp85RecurrenceB
  ring

end

end YangMills.RG
