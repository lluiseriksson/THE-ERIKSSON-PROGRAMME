import Mathlib

/-!
PRE-VALIDATION: Mathlib-only scalar reproduction.  This file has no
materialized `.olean` and no compiler or axiom-oracle verdict.

It isolates the proof-free scalar recursion intended for the closed complex
Eq. (3.37) radius-chain producer.  The project-facing module will separately
identify these scalar functions with the literal no-winding record.
-/

namespace YangMills.RG

/-- The common norm envelope for a path of length at most `L`. -/
def cmp99ComplexClosedRadiusFactorEnvelope (L : ℕ) (R : ℝ) : ℝ :=
  (1 + R) ^ L

/-- The proof-free literal four-path deviation radius. -/
def cmp99ComplexClosedRadiusDeviation (L : ℕ) (r : ℝ) : ℝ :=
  let F := cmp99ComplexClosedRadiusFactorEnvelope L r
  (L : ℝ) * r * (F ^ 4 + F ^ 3 + F ^ 2 + F)

/-- A radius-`R` coefficient bounding the literal four-path deviation. -/
def cmp99ComplexClosedRadiusDeviationCoefficient (L : ℕ) (R : ℝ) : ℝ :=
  let F := cmp99ComplexClosedRadiusFactorEnvelope L R
  (L : ℝ) * (F ^ 4 + F ^ 3 + F ^ 2 + F)

/-- Proof-free logarithm radius attached to a deviation radius. -/
def cmp99ComplexClosedRadiusLog (delta : ℝ) : ℝ :=
  delta / (1 - delta)

/-- Proof-free exponential radius attached to a deviation radius. -/
def cmp99ComplexClosedRadiusExp (delta : ℝ) : ℝ :=
  let theta := cmp99ComplexClosedRadiusLog delta
  theta + theta ^ 2 / (1 - theta)

/-- The positive-edge radius after one complex source step. -/
def cmp99ComplexClosedRadiusNextLink (L M : ℕ) (r : ℝ) : ℝ :=
  cmp99ComplexClosedRadiusExp (cmp99ComplexClosedRadiusDeviation L r) *
      (1 + r) ^ M +
    (M : ℝ) * r * (1 + r) ^ M

/-- The all-orientation radius after paying the complex inverse loss. -/
def cmp99ComplexClosedRadiusNext (L M : ℕ) (r : ℝ) : ℝ :=
  let q := cmp99ComplexClosedRadiusNextLink L M r
  q / (1 - q)

/-- Linear coefficient for the positive-edge radius on `[0,R]`. -/
def cmp99ComplexClosedRadiusLinkCoefficient (L M : ℕ) (R : ℝ) : ℝ :=
  (4 * cmp99ComplexClosedRadiusDeviationCoefficient L R + (M : ℝ)) *
    (1 + R) ^ M

/-- Conservative linear growth factor for the all-orientation radius. -/
def cmp99ComplexClosedRadiusGrowthFactor (L M : ℕ) (R : ℝ) : ℝ :=
  max 1 (2 * cmp99ComplexClosedRadiusLinkCoefficient L M R)

/-- The radius obtained after `k` exact complex source steps. -/
def cmp99ComplexClosedRadiusAt (L M : ℕ) (r0 : ℝ) : ℕ → ℝ
  | 0 => r0
  | k + 1 => cmp99ComplexClosedRadiusNext L M
      (cmp99ComplexClosedRadiusAt L M r0 k)

@[simp] theorem cmp99ComplexClosedRadiusAt_zero
    (L M : ℕ) (r0 : ℝ) :
    cmp99ComplexClosedRadiusAt L M r0 0 = r0 := rfl

@[simp] theorem cmp99ComplexClosedRadiusAt_succ
    (L M : ℕ) (r0 : ℝ) (k : ℕ) :
    cmp99ComplexClosedRadiusAt L M r0 (k + 1) =
      cmp99ComplexClosedRadiusNext L M
        (cmp99ComplexClosedRadiusAt L M r0 k) := rfl

/-- Restarting the exact scalar recursion after one step shifts the index. -/
theorem cmp99ComplexClosedRadiusAt_next
    (L M : ℕ) (r0 : ℝ) (k : ℕ) :
    cmp99ComplexClosedRadiusAt L M
        (cmp99ComplexClosedRadiusNext L M r0) k =
      cmp99ComplexClosedRadiusAt L M r0 (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc
        cmp99ComplexClosedRadiusAt L M
            (cmp99ComplexClosedRadiusNext L M r0) (k + 1) =
          cmp99ComplexClosedRadiusNext L M
            (cmp99ComplexClosedRadiusAt L M
              (cmp99ComplexClosedRadiusNext L M r0) k) := rfl
        _ = cmp99ComplexClosedRadiusNext L M
            (cmp99ComplexClosedRadiusAt L M r0 (k + 1)) := by rw [ih]
        _ = cmp99ComplexClosedRadiusAt L M r0 (k + 1 + 1) := rfl

/-- The exact path envelope is monotone on nonnegative radii. -/
theorem cmp99ComplexClosedRadiusFactorEnvelope_mono
    (L : ℕ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    cmp99ComplexClosedRadiusFactorEnvelope L r ≤
      cmp99ComplexClosedRadiusFactorEnvelope L R := by
  unfold cmp99ComplexClosedRadiusFactorEnvelope
  exact pow_le_pow_left₀ (by linarith) (by linarith)

/-- The literal deviation is bounded by its radius-`R` linear coefficient. -/
theorem cmp99ComplexClosedRadiusDeviation_le_coefficient_mul
    (L : ℕ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    cmp99ComplexClosedRadiusDeviation L r ≤
      cmp99ComplexClosedRadiusDeviationCoefficient L R * r := by
  let f := cmp99ComplexClosedRadiusFactorEnvelope L r
  let F := cmp99ComplexClosedRadiusFactorEnvelope L R
  have hf : f ≤ F := by
    exact cmp99ComplexClosedRadiusFactorEnvelope_mono L hr hrR
  have hf0 : 0 ≤ f := by
    dsimp only [f, cmp99ComplexClosedRadiusFactorEnvelope]
    positivity
  have hF0 : 0 ≤ F := by
    dsimp only [F, cmp99ComplexClosedRadiusFactorEnvelope]
    positivity
  have hs : f ^ 4 + f ^ 3 + f ^ 2 + f ≤
      F ^ 4 + F ^ 3 + F ^ 2 + F := by
    gcongr
  unfold cmp99ComplexClosedRadiusDeviation
  unfold cmp99ComplexClosedRadiusDeviationCoefficient
  change (L : ℝ) * r * (f ^ 4 + f ^ 3 + f ^ 2 + f) ≤
    (L : ℝ) * (F ^ 4 + F ^ 3 + F ^ 2 + F) * r
  calc
    (L : ℝ) * r * (f ^ 4 + f ^ 3 + f ^ 2 + f) ≤
        (L : ℝ) * r * (F ^ 4 + F ^ 3 + F ^ 2 + F) := by
      exact mul_le_mul_of_nonneg_left hs
        (mul_nonneg (Nat.cast_nonneg L) hr)
    _ = (L : ℝ) * (F ^ 4 + F ^ 3 + F ^ 2 + F) * r := by ring

/-- The exact four-path deviation is nonnegative at a nonnegative radius. -/
theorem cmp99ComplexClosedRadiusDeviation_nonneg
    (L : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ cmp99ComplexClosedRadiusDeviation L r := by
  unfold cmp99ComplexClosedRadiusDeviation
  dsimp only [cmp99ComplexClosedRadiusFactorEnvelope]
  positivity

/-- Below `1/4`, the logarithm and exponential remainders cost at most four
times the literal deviation radius. -/
theorem cmp99ComplexClosedRadiusExp_le_four_mul
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (hdelta_small : delta < (1 / 4 : ℝ)) :
    cmp99ComplexClosedRadiusExp delta ≤ 4 * delta := by
  unfold cmp99ComplexClosedRadiusExp cmp99ComplexClosedRadiusLog
  let theta := delta / (1 - delta)
  change theta + theta ^ 2 / (1 - theta) ≤ 4 * delta
  have hdenDelta : 0 < 1 - delta := by linarith
  have htheta_nonneg : 0 ≤ theta := div_nonneg hdelta_nonneg hdenDelta.le
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

/-- On `[0,R]`, the positive-edge radius is bounded by its visible linear
coefficient. -/
theorem cmp99ComplexClosedRadiusNextLink_le_coefficient_mul
    (L M : ℕ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (hdelta_small : cmp99ComplexClosedRadiusDeviation L r < (1 / 4 : ℝ)) :
    cmp99ComplexClosedRadiusNextLink L M r ≤
      cmp99ComplexClosedRadiusLinkCoefficient L M R * r := by
  let delta := cmp99ComplexClosedRadiusDeviation L r
  let C := cmp99ComplexClosedRadiusDeviationCoefficient L R
  let f := (1 + r) ^ M
  let F := (1 + R) ^ M
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta, cmp99ComplexClosedRadiusDeviation,
      cmp99ComplexClosedRadiusFactorEnvelope]
    positivity
  have hdelta_le : delta ≤ C * r := by
    exact cmp99ComplexClosedRadiusDeviation_le_coefficient_mul L hr hrR
  have hexp := cmp99ComplexClosedRadiusExp_le_four_mul hdelta0 hdelta_small
  have hf : f ≤ F := by
    dsimp only [f, F]
    exact pow_le_pow_left₀ (by linarith) (by linarith)
  have hf0 : 0 ≤ f := by dsimp only [f]; positivity
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hC0 : 0 ≤ C := by
    dsimp only [C, cmp99ComplexClosedRadiusDeviationCoefficient,
      cmp99ComplexClosedRadiusFactorEnvelope]
    positivity
  have hexp0 : 0 ≤ cmp99ComplexClosedRadiusExp delta := by
    dsimp only [cmp99ComplexClosedRadiusExp, cmp99ComplexClosedRadiusLog]
    have hdenDelta : 0 < 1 - delta := by linarith
    have htheta0 : 0 ≤ delta / (1 - delta) :=
      div_nonneg hdelta0 hdenDelta.le
    have htheta_lt_one : delta / (1 - delta) < 1 := by
      rw [div_lt_one hdenDelta]
      linarith
    positivity
  unfold cmp99ComplexClosedRadiusNextLink
  unfold cmp99ComplexClosedRadiusLinkCoefficient
  change cmp99ComplexClosedRadiusExp delta * f + (M : ℝ) * r * f ≤
    (4 * C + (M : ℝ)) * F * r
  calc
    cmp99ComplexClosedRadiusExp delta * f + (M : ℝ) * r * f ≤
        (4 * delta) * F + (M : ℝ) * r * F := by
      exact add_le_add
        (mul_le_mul hexp hf hf0 (mul_nonneg (by norm_num) hdelta0))
        (mul_le_mul_of_nonneg_left hf
          (mul_nonneg (Nat.cast_nonneg M) hr))
    _ ≤ (4 * (C * r)) * F + (M : ℝ) * r * F := by
      gcongr
    _ = (4 * C + (M : ℝ)) * F * r := by ring

/-- The positive-edge radius is nonnegative in the quarter-deviation regime. -/
theorem cmp99ComplexClosedRadiusNextLink_nonneg
    (L M : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hdelta_small : cmp99ComplexClosedRadiusDeviation L r < (1 / 4 : ℝ)) :
    0 ≤ cmp99ComplexClosedRadiusNextLink L M r := by
  let delta := cmp99ComplexClosedRadiusDeviation L r
  have hdelta0 : 0 ≤ delta :=
    cmp99ComplexClosedRadiusDeviation_nonneg L hr
  have hdenDelta : 0 < 1 - delta := by
    dsimp only [delta] at hdelta_small ⊢
    linarith
  have htheta0 : 0 ≤ cmp99ComplexClosedRadiusLog delta := by
    unfold cmp99ComplexClosedRadiusLog
    exact div_nonneg hdelta0 hdenDelta.le
  have htheta_lt_one : cmp99ComplexClosedRadiusLog delta < 1 := by
    unfold cmp99ComplexClosedRadiusLog
    rw [div_lt_one hdenDelta]
    dsimp only [delta] at hdelta_small ⊢
    linarith
  have hexp0 : 0 ≤ cmp99ComplexClosedRadiusExp delta := by
    unfold cmp99ComplexClosedRadiusExp
    positivity
  unfold cmp99ComplexClosedRadiusNextLink
  exact add_nonneg
    (mul_nonneg hexp0 (pow_nonneg (by linarith) M))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg M) hr)
      (pow_nonneg (by linarith) M))

/-- Below `1/2`, the all-orientation inverse radius loses at most a factor
two. -/
theorem cmp99ComplexClosedRadiusNext_le_two_mul
    (L M : ℕ) {r : ℝ}
    (hq_nonneg : 0 ≤ cmp99ComplexClosedRadiusNextLink L M r)
    (hq_small : cmp99ComplexClosedRadiusNextLink L M r < (1 / 2 : ℝ)) :
    cmp99ComplexClosedRadiusNext L M r ≤
      2 * cmp99ComplexClosedRadiusNextLink L M r := by
  unfold cmp99ComplexClosedRadiusNext
  let q := cmp99ComplexClosedRadiusNextLink L M r
  change q / (1 - q) ≤ 2 * q
  have hden : 0 < 1 - q := by linarith
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg q]

/-- The all-orientation radius remains nonnegative when the positive-edge
radius is below one. -/
theorem cmp99ComplexClosedRadiusNext_nonneg
    (L M : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hdelta_small : cmp99ComplexClosedRadiusDeviation L r < (1 / 4 : ℝ))
    (hq_small : cmp99ComplexClosedRadiusNextLink L M r < 1) :
    0 ≤ cmp99ComplexClosedRadiusNext L M r := by
  have hq0 := cmp99ComplexClosedRadiusNextLink_nonneg
    L M hr hdelta_small
  unfold cmp99ComplexClosedRadiusNext
  exact div_nonneg hq0 (sub_nonneg.mpr hq_small.le)

/-- The proof-free one-step radius is bounded by the declared growth factor. -/
theorem cmp99ComplexClosedRadiusNext_le_growthFactor_mul
    (L M : ℕ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (hdelta_small : cmp99ComplexClosedRadiusDeviation L r < (1 / 4 : ℝ))
    (hq_nonneg : 0 ≤ cmp99ComplexClosedRadiusNextLink L M r)
    (hq_small : cmp99ComplexClosedRadiusNextLink L M r < (1 / 2 : ℝ)) :
    cmp99ComplexClosedRadiusNext L M r ≤
      cmp99ComplexClosedRadiusGrowthFactor L M R * r := by
  have hq := cmp99ComplexClosedRadiusNextLink_le_coefficient_mul
    L M hr hrR hdelta_small
  have hinv := cmp99ComplexClosedRadiusNext_le_two_mul
    L M hq_nonneg hq_small
  calc
    cmp99ComplexClosedRadiusNext L M r ≤
        2 * cmp99ComplexClosedRadiusNextLink L M r := hinv
    _ ≤ 2 * cmp99ComplexClosedRadiusLinkCoefficient L M R * r := by
      nlinarith
    _ ≤ cmp99ComplexClosedRadiusGrowthFactor L M R * r := by
      unfold cmp99ComplexClosedRadiusGrowthFactor
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hr

#print axioms cmp99ComplexClosedRadiusFactorEnvelope_mono
#print axioms cmp99ComplexClosedRadiusAt_next
#print axioms cmp99ComplexClosedRadiusDeviation_le_coefficient_mul
#print axioms cmp99ComplexClosedRadiusDeviation_nonneg
#print axioms cmp99ComplexClosedRadiusExp_le_four_mul
#print axioms cmp99ComplexClosedRadiusNextLink_le_coefficient_mul
#print axioms cmp99ComplexClosedRadiusNextLink_nonneg
#print axioms cmp99ComplexClosedRadiusNext_le_two_mul
#print axioms cmp99ComplexClosedRadiusNext_nonneg
#print axioms cmp99ComplexClosedRadiusNext_le_growthFactor_mul

end YangMills.RG
