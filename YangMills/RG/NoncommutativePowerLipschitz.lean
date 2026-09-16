/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLogLipschitz

/-!
# Quantitative variation of powers in a noncommutative normed ring

The Mercator derivative is an ordered sum of left and right powers.  Its
second-order control therefore needs the elementary noncommutative estimate
`‖Y^n - Z^n‖ ≤ n r^(n-1) ‖Y-Z‖` on a common radius-`r` ball.  The proof uses
the ordered telescoping identity and never commutes `Y` with `Z`.
-/

namespace YangMills.RG

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- Lipschitz bound for an integer power on a common closed ball in a
possibly noncommutative normed ring. -/
theorem norm_pow_sub_pow_le
    (Y Z : A) (r : ℝ) (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r) (n : ℕ) :
    ‖Y ^ n - Z ^ n‖ ≤ (n : ℝ) * r ^ n.pred * ‖Y - Z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simp
      | succ k =>
          have hr0 : 0 ≤ r := (norm_nonneg Y).trans hY
          have hdecomp :
              Y ^ (Nat.succ (Nat.succ k)) - Z ^ (Nat.succ (Nat.succ k)) =
                (Y ^ Nat.succ k - Z ^ Nat.succ k) * Y +
                  Z ^ Nat.succ k * (Y - Z) := by
            rw [pow_succ, pow_succ]
            noncomm_ring
          rw [hdecomp]
          calc
            ‖(Y ^ Nat.succ k - Z ^ Nat.succ k) * Y +
                  Z ^ Nat.succ k * (Y - Z)‖
                ≤ ‖(Y ^ Nat.succ k - Z ^ Nat.succ k) * Y‖ +
                    ‖Z ^ Nat.succ k * (Y - Z)‖ := norm_add_le _ _
            _ ≤ ‖Y ^ Nat.succ k - Z ^ Nat.succ k‖ * ‖Y‖ +
                    ‖Z ^ Nat.succ k‖ * ‖Y - Z‖ :=
              add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
            _ ≤ ((Nat.succ k : ℕ) : ℝ) * r ^ k * ‖Y - Z‖ * r +
                    r ^ Nat.succ k * ‖Y - Z‖ := by
              gcongr
              · simpa using ih
              · exact norm_pow_le Z (Nat.succ k) |>.trans (by gcongr)
            _ = (Nat.succ (Nat.succ k) : ℕ) *
                  r ^ (Nat.succ (Nat.succ k)).pred * ‖Y - Z‖ := by
              push_cast
              simp only [Nat.pred_succ, pow_succ]
              ring

/-- Two-sided ordered monomials have the expected total-degree Lipschitz
constant.  This is the exact shape of every insertion in the derivative of
a noncommutative power. -/
theorem norm_pow_mul_mul_pow_sub_pow_mul_mul_pow_le
    (Y Z H : A) (r : ℝ) (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r)
    (a b : ℕ) :
    ‖Y ^ a * H * Y ^ b - Z ^ a * H * Z ^ b‖ ≤
      ((a + b : ℕ) : ℝ) * r ^ (a + b).pred * ‖Y - Z‖ * ‖H‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg Y).trans hY
  have hdecomp :
      Y ^ a * H * Y ^ b - Z ^ a * H * Z ^ b =
        (Y ^ a - Z ^ a) * H * Y ^ b +
          Z ^ a * H * (Y ^ b - Z ^ b) := by
    noncomm_ring
  rw [hdecomp]
  calc
    ‖(Y ^ a - Z ^ a) * H * Y ^ b +
          Z ^ a * H * (Y ^ b - Z ^ b)‖
        ≤ ‖(Y ^ a - Z ^ a) * H * Y ^ b‖ +
            ‖Z ^ a * H * (Y ^ b - Z ^ b)‖ := norm_add_le _ _
    _ ≤ (‖Y ^ a - Z ^ a‖ * ‖H‖) * ‖Y ^ b‖ +
          (‖Z ^ a‖ * ‖H‖) * ‖Y ^ b - Z ^ b‖ := by
      exact add_le_add
        ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
        ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
    _ ≤ (((a : ℝ) * r ^ a.pred * ‖Y - Z‖) * ‖H‖) * r ^ b +
          (r ^ a * ‖H‖) *
            ((b : ℝ) * r ^ b.pred * ‖Y - Z‖) := by
      gcongr
      · exact norm_pow_sub_pow_le Y Z r hY hZ a
      · exact (norm_pow_le Y b).trans (by gcongr)
      · exact (norm_pow_le Z a).trans (by gcongr)
      · exact norm_pow_sub_pow_le Y Z r hY hZ b
    _ = ((a + b : ℕ) : ℝ) * r ^ (a + b).pred * ‖Y - Z‖ * ‖H‖ := by
      cases a with
      | zero => simp [mul_comm]
      | succ a =>
          cases b with
          | zero => simp [mul_comm]
          | succ b =>
              have hp : (Nat.succ a + Nat.succ b).pred =
                  Nat.succ (a + b) := by
                calc
                  (Nat.succ a + Nat.succ b).pred =
                      (Nat.succ (a + Nat.succ b)).pred := by
                        rw [Nat.succ_add]
                  _ = a + Nat.succ b := Nat.pred_succ _
                  _ = Nat.succ (a + b) := Nat.add_succ _ _
              push_cast
              rw [hp]
              simp only [Nat.pred_succ, pow_succ, pow_add]
              ring

/-- Pointwise Lipschitz estimate for one ordered-insertion Mercator
derivative.  The two natural factors count the insertion position and the
remaining background slot. -/
theorem norm_nearLogTermFDeriv_sub_apply_le
    [NormedAlgebra ℝ A] [CompleteSpace A]
    (Y Z H : A) (r : ℝ) (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r) (n : ℕ) :
    ‖(nearLogTermFDeriv Y n - nearLogTermFDeriv Z n) H‖ ≤
      (n : ℝ) * n.pred * r ^ n.pred.pred * ‖Y - Z‖ * ‖H‖ := by
  rw [ContinuousLinearMap.sub_apply, nearLogTermFDeriv_apply,
    nearLogTermFDeriv_apply, ← smul_sub, norm_smul, Real.norm_eq_abs]
  calc
    |logCoeff n| *
          ‖(∑ i ∈ Finset.range n, Y ^ (n.pred - i) * H * Y ^ i) -
            ∑ i ∈ Finset.range n, Z ^ (n.pred - i) * H * Z ^ i‖
        ≤ 1 * ∑ i ∈ Finset.range n,
            ‖Y ^ (n.pred - i) * H * Y ^ i -
              Z ^ (n.pred - i) * H * Z ^ i‖ := by
          gcongr
          · exact abs_logCoeff_le_one n
          · rw [← Finset.sum_sub_distrib]
            exact norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range n,
          (n.pred : ℝ) * r ^ n.pred.pred * ‖Y - Z‖ * ‖H‖ := by
      simp only [one_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      have hle : i ≤ n.pred := Nat.le_pred_of_lt hin
      have hsum : n.pred - i + i = n.pred := Nat.sub_add_cancel hle
      simpa only [hsum] using
        norm_pow_mul_mul_pow_sub_pow_mul_mul_pow_le
          Y Z H r hY hZ (n.pred - i) i
    _ = (n : ℝ) * n.pred * r ^ n.pred.pred * ‖Y - Z‖ * ‖H‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- Operator-norm version of the termwise Mercator derivative Lipschitz
estimate. -/
theorem norm_nearLogTermFDeriv_sub_le
    [NormedAlgebra ℝ A] [CompleteSpace A]
    (Y Z : A) (r : ℝ) (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r) (n : ℕ) :
    ‖nearLogTermFDeriv Y n - nearLogTermFDeriv Z n‖ ≤
      (n : ℝ) * n.pred * r ^ n.pred.pred * ‖Y - Z‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg Y).trans hY
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro H
  simpa [mul_assoc] using
    norm_nearLogTermFDeriv_sub_apply_le Y Z H r hY hZ n

/-- Summed Lipschitz budget for the Fréchet derivative of the Mercator
series on the closed radius-`r` ball. -/
def nearLogSecondDerivativeBudget (r : ℝ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) * n.pred * r ^ n.pred.pred

/-- The explicit second-derivative majorant is summable on every strict
sub-ball of the Mercator domain. -/
theorem summable_nearLogSecondDerivativeMajorant
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) * n.pred * r ^ n.pred.pred) := by
  rw [← summable_nat_add_iff 2]
  have hrnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have h2 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hrnorm)
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm)
  have h0 : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  have hpoly : Summable (fun n : ℕ =>
      ((n : ℝ) ^ 2 + 3 * n + 2) * r ^ n) := by
    convert h2.add ((h1.mul_left 3).add (h0.mul_left 2)) using 1
    funext n
    ring
  refine hpoly.congr (fun n => ?_)
  push_cast
  simp only [Nat.cast_add, Nat.cast_one, Nat.pred_succ]
  ring

theorem nearLogSecondDerivativeBudget_nonneg
    (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ nearLogSecondDerivativeBudget r := by
  unfold nearLogSecondDerivativeBudget
  exact tsum_nonneg fun n => by positivity

/-- The Fréchet derivative of the complete noncommutative Mercator series
is Lipschitz on every strict closed sub-ball, with the explicit summed
second-derivative budget. -/
theorem norm_fderiv_nearLog_sub_le_secondDerivativeBudget
    [NormedAlgebra ℝ A] [CompleteSpace A]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {Y Z : A} (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r) :
    ‖fderiv ℝ (nearLog : A → A) Y -
        fderiv ℝ (nearLog : A → A) Z‖ ≤
      nearLogSecondDerivativeBudget r * ‖Y - Z‖ := by
  have hYlt : ‖Y‖ < 1 := hY.trans_lt hr1
  have hZlt : ‖Z‖ < 1 := hZ.trans_lt hr1
  have hYSum := summable_nearLogTermFDeriv_of_norm_lt_one hYlt
  have hZSum := summable_nearLogTermFDeriv_of_norm_lt_one hZlt
  have hmajor := summable_nearLogSecondDerivativeMajorant hr0 hr1
  have hmajorDiff : Summable (fun n : ℕ =>
      ((n : ℝ) * n.pred * r ^ n.pred.pred) * ‖Y - Z‖) :=
    hmajor.mul_right ‖Y - Z‖
  have hdiffNorm : Summable (fun n : ℕ =>
      ‖nearLogTermFDeriv Y n - nearLogTermFDeriv Z n‖) :=
    hmajorDiff.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
      exact norm_nearLogTermFDeriv_sub_le Y Z r hY hZ n)
  rw [(hasFDerivAt_nearLog_of_norm_lt_one hYlt).fderiv,
    (hasFDerivAt_nearLog_of_norm_lt_one hZlt).fderiv,
    ← hYSum.tsum_sub hZSum]
  calc
    ‖∑' n : ℕ, (nearLogTermFDeriv Y n - nearLogTermFDeriv Z n)‖
        ≤ ∑' n : ℕ,
            ‖nearLogTermFDeriv Y n - nearLogTermFDeriv Z n‖ :=
      norm_tsum_le_tsum_norm hdiffNorm
    _ ≤ ∑' n : ℕ,
          ((n : ℝ) * n.pred * r ^ n.pred.pred) * ‖Y - Z‖ := by
      exact hdiffNorm.tsum_le_tsum
        (fun n => norm_nearLogTermFDeriv_sub_le Y Z r hY hZ n)
        hmajorDiff
    _ = nearLogSecondDerivativeBudget r * ‖Y - Z‖ := by
      rw [tsum_mul_right]
      rfl

/-- Explicit quadratic two-point Taylor remainder for the noncommutative
Mercator logarithm.  The constant is the convergent derivative-Lipschitz
series; no abstract second-derivative bound is supplied. -/
theorem norm_nearLog_sub_nearLog_sub_fderiv_le
    [NormedAlgebra ℝ A] [CompleteSpace A]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {Y Z : A} (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r) :
    ‖nearLog Y - nearLog Z -
        (fderiv ℝ (nearLog : A → A) Z) (Y - Z)‖ ≤
      nearLogSecondDerivativeBudget r * ‖Y - Z‖ ^ 2 := by
  let H : A := Y - Z
  let LZ : A →L[ℝ] A := fderiv ℝ (nearLog : A → A) Z
  let g : ℝ → A := fun s =>
    nearLog (Z + s • H) - nearLog Z - s • LZ H
  have hsegment : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖Z + s • H‖ ≤ r := by
    intro s hs
    have hsz : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
    have hsy : 0 ≤ s := hs.1
    have heq : Z + s • H = (1 - s) • Z + s • Y := by
      dsimp only [H]
      module
    rw [heq]
    calc
      ‖(1 - s) • Z + s • Y‖
          ≤ ‖(1 - s) • Z‖ + ‖s • Y‖ := norm_add_le _ _
      _ = (1 - s) * ‖Z‖ + s * ‖Y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hsz, abs_of_nonneg hsy]
      _ ≤ (1 - s) * r + s * r := by gcongr
      _ = r := by ring
  have hgDeriv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt g
        ((fderiv ℝ (nearLog : A → A) (Z + s • H) - LZ) H)
        (Set.Icc (0 : ℝ) 1) s := by
    intro s hs
    have hWlt : ‖Z + s • H‖ < 1 := (hsegment s hs).trans_lt hr1
    have hline : HasDerivAt (fun q : ℝ => Z + q • H) H s := by
      convert (hasDerivAt_const s Z).add
        ((hasDerivAt_id s).smul_const H) using 1
      all_goals simp
    have hnear : HasDerivAt (fun q : ℝ => nearLog (Z + q • H))
        ((fderiv ℝ (nearLog : A → A) (Z + s • H)) H) s := by
      have hlog := hasFDerivAt_nearLog_of_norm_lt_one hWlt
      have hcomp := hlog.comp_hasDerivAt s hline
      rw [hlog.fderiv]
      simpa only [Function.comp_apply] using hcomp
    have hlin : HasDerivAt (fun q : ℝ => q • LZ H) (LZ H) s := by
      simpa using (hasDerivAt_id s).smul_const (LZ H)
    have hraw := (hnear.sub_const (nearLog Z)).sub hlin
    have hderivEq :
        (fderiv ℝ (nearLog : A → A) (Z + s • H)) H - LZ H =
          (fderiv ℝ (nearLog : A → A) (Z + s • H) - LZ) H := by
      simp
    simpa only [g, hderivEq] using hraw.hasDerivWithinAt
  have hgBound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ‖(fderiv ℝ (nearLog : A → A) (Z + s • H) - LZ) H‖ ≤
        nearLogSecondDerivativeBudget r * ‖H‖ ^ 2 := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have hW := hsegment s hsIcc
    have hLip := norm_fderiv_nearLog_sub_le_secondDerivativeBudget
      hr0 hr1 hW hZ
    have hWs : ‖(Z + s • H) - Z‖ ≤ ‖H‖ := by
      have hsabs : |s| ≤ 1 := by
        rw [abs_of_nonneg hs.1]
        exact hs.2.le
      have heq : (Z + s • H) - Z = s • H := by abel
      rw [heq, norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg H) hsabs
    calc
      ‖(fderiv ℝ (nearLog : A → A) (Z + s • H) - LZ) H‖
          ≤ ‖fderiv ℝ (nearLog : A → A) (Z + s • H) - LZ‖ * ‖H‖ :=
        ContinuousLinearMap.le_opNorm _ H
      _ ≤ (nearLogSecondDerivativeBudget r *
            ‖(Z + s • H) - Z‖) * ‖H‖ := by gcongr
      _ ≤ (nearLogSecondDerivativeBudget r * ‖H‖) * ‖H‖ := by
        gcongr
        exact nearLogSecondDerivativeBudget_nonneg r hr0
      _ = nearLogSecondDerivativeBudget r * ‖H‖ ^ 2 := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    hgDeriv hgBound
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : g 1 = nearLog Y - nearLog Z - LZ H := by
    dsimp only [g]
    have hZH : Z + (1 : ℝ) • H = Y := by
      dsimp only [H]
      module
    rw [hZH, one_smul]
  rw [hg0, sub_zero, hg1] at hmv
  simpa only [H, LZ] using hmv

end

end YangMills.RG
