import Mathlib

/-!
PRE-VALIDATION: Mathlib-only scalar reproduction.  This file has no
materialized `.olean` and no compiler or axiom-oracle verdict.

It isolates the two rational inequalities needed by the future closed complex
Eq. (3.37) radius-chain producer.  It deliberately contains no project object
and is never promoted as source evidence.
-/

namespace YangMills.RG

/-- If the literal deviation radius is below `1/4`, the logarithm followed by
the second-order exponential remainder costs at most `4 * delta`. -/
theorem cmp99ComplexRadiusScalar_expRadius_le_four_mul
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (hdelta_small : delta < (1 / 4 : ℝ)) :
    let theta := delta / (1 - delta)
    theta + theta ^ 2 / (1 - theta) ≤ 4 * delta := by
  dsimp only
  let theta := delta / (1 - delta)
  change theta + theta ^ 2 / (1 - theta) ≤ 4 * delta
  have hdenDelta : 0 < 1 - delta := by linarith
  have htheta_nonneg : 0 ≤ theta := by
    exact div_nonneg hdelta_nonneg hdenDelta.le
  have htheta_le_two_delta : theta ≤ 2 * delta := by
    dsimp only [theta]
    rw [div_le_iff₀ hdenDelta]
    nlinarith
  have htheta_lt_half : theta < (1 / 2 : ℝ) := by
    dsimp only [theta]
    rw [div_lt_iff₀ hdenDelta]
    nlinarith
  have hdenTheta : 0 < 1 - theta := by linarith
  have hremainder : theta ^ 2 / (1 - theta) ≤ theta := by
    rw [div_le_iff₀ hdenTheta]
    nlinarith [sq_nonneg theta]
  nlinarith

/-- Below `1/2`, the non-unitary inverse orientation costs at most a factor
two. -/
theorem cmp99ComplexRadiusScalar_orientedInverse_le_two_mul
    {q : ℝ} (hq_nonneg : 0 ≤ q) (hq_small : q < (1 / 2 : ℝ)) :
    q / (1 - q) ≤ 2 * q := by
  have hden : 0 < 1 - q := by linarith
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg q]

#print axioms cmp99ComplexRadiusScalar_expRadius_le_four_mul
#print axioms cmp99ComplexRadiusScalar_orientedInverse_le_two_mul

end YangMills.RG
