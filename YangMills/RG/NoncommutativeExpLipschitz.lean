/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98NoncommutativeExpFDeriv
import YangMills.RG.NoncommutativePowerLipschitz

/-!
# Quantitative variation of the noncommutative exponential derivative

The ordered insertion formula for the Fréchet derivative of the exponential
is already available in arbitrary real Banach algebras.  Here its factorial
series is controlled uniformly on a closed ball.  The resulting derivative
Lipschitz estimate supplies a source-explicit quadratic two-point Taylor
remainder for the outer exponential in CMP98 (123).
-/

namespace YangMills.RG

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [CompleteSpace A] [NormOneClass A]

/-- One ordered exponential derivative summand is Lipschitz on a common
closed ball.  The factor `n.pred` counts the non-insertion slots. -/
theorem norm_expTermFDeriv_sub_apply_le
    (Y Z H : A) (r : ℝ) (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r) (n : ℕ) :
    ‖(expTermFDeriv Y n - expTermFDeriv Z n) H‖ ≤
      ((n : ℝ) / n.factorial) * n.pred * r ^ n.pred.pred *
        ‖Y - Z‖ * ‖H‖ := by
  rw [ContinuousLinearMap.sub_apply, expTermFDeriv_apply,
    expTermFDeriv_apply, ← smul_sub, norm_smul, Real.norm_eq_abs]
  have hcoeff : 0 ≤ ((n.factorial : ℝ)⁻¹) := by positivity
  rw [abs_of_nonneg hcoeff]
  calc
    ((n.factorial : ℝ)⁻¹) *
          ‖(∑ i ∈ Finset.range n, Y ^ (n.pred - i) * H * Y ^ i) -
            ∑ i ∈ Finset.range n, Z ^ (n.pred - i) * H * Z ^ i‖
        ≤ ((n.factorial : ℝ)⁻¹) * ∑ i ∈ Finset.range n,
            ‖Y ^ (n.pred - i) * H * Y ^ i -
              Z ^ (n.pred - i) * H * Z ^ i‖ := by
          gcongr
          rw [← Finset.sum_sub_distrib]
          exact norm_sum_le _ _
    _ ≤ ((n.factorial : ℝ)⁻¹) * ∑ _i ∈ Finset.range n,
          (n.pred : ℝ) * r ^ n.pred.pred * ‖Y - Z‖ * ‖H‖ := by
      gcongr with i hi
      have hin : i < n := Finset.mem_range.mp hi
      have hle : i ≤ n.pred := Nat.le_pred_of_lt hin
      have hsum : n.pred - i + i = n.pred := Nat.sub_add_cancel hle
      simpa only [hsum] using
        norm_pow_mul_mul_pow_sub_pow_mul_mul_pow_le
          Y Z H r hY hZ (n.pred - i) i
    _ = ((n : ℝ) / n.factorial) * n.pred * r ^ n.pred.pred *
          ‖Y - Z‖ * ‖H‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp [div_eq_mul_inv]
      ring

/-- Operator-norm form of the termwise exponential derivative estimate. -/
theorem norm_expTermFDeriv_sub_le
    (Y Z : A) (r : ℝ) (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r) (n : ℕ) :
    ‖expTermFDeriv Y n - expTermFDeriv Z n‖ ≤
      ((n : ℝ) / n.factorial) * n.pred * r ^ n.pred.pred * ‖Y - Z‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg Y).trans hY
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro H
  simpa [mul_assoc] using
    norm_expTermFDeriv_sub_apply_le Y Z H r hY hZ n

/-- Uniform first-derivative budget for the noncommutative exponential on a
closed radius-`r` ball. -/
def expDerivativeBudget (r : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) / n.factorial) * r ^ n.pred

/-- Uniform derivative-Lipschitz budget for the noncommutative exponential. -/
def expSecondDerivativeBudget (r : ℝ) : ℝ :=
  ∑' n : ℕ,
    ((n : ℝ) / n.factorial) * n.pred * r ^ n.pred.pred

theorem expDerivativeBudget_nonneg (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ expDerivativeBudget r := by
  unfold expDerivativeBudget
  exact tsum_nonneg fun n => by positivity

theorem expSecondDerivativeBudget_nonneg (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ expSecondDerivativeBudget r := by
  unfold expSecondDerivativeBudget
  exact tsum_nonneg fun n => by positivity

/-- The second-derivative factorial majorant is summable at every finite
radius.  After shifting by two it is exactly the exponential series. -/
theorem summable_expSecondDerivativeMajorant (r : ℝ) :
    Summable (fun n : ℕ =>
      ((n : ℝ) / n.factorial) * n.pred * r ^ n.pred.pred) := by
  rw [← summable_nat_add_iff 2]
  convert Real.summable_pow_div_factorial r using 1
  funext n
  simp only [Nat.pred_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The ordered exponential derivative has the explicit uniform operator
norm bound on every closed ball. -/
theorem norm_fderiv_exp_le_derivativeBudget
    {r : ℝ} {Y : A} (hY : ‖Y‖ ≤ r) :
    ‖fderiv ℝ (NormedSpace.exp : A → A) Y‖ ≤ expDerivativeBudget r := by
  have hmajor := summable_natCast_div_factorial_mul_pow_pred r
  have htermsNorm : Summable (fun n : ℕ => ‖expTermFDeriv Y n‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n =>
      (norm_expTermFDeriv_le Y n).trans (by gcongr))
  rw [fderiv_exp_eq_ordered]
  calc
    ‖∑' n : ℕ, expTermFDeriv Y n‖
        ≤ ∑' n : ℕ, ‖expTermFDeriv Y n‖ :=
      norm_tsum_le_tsum_norm htermsNorm
    _ ≤ ∑' n : ℕ, ((n : ℝ) / n.factorial) * r ^ n.pred := by
      exact htermsNorm.tsum_le_tsum
        (fun n => (norm_expTermFDeriv_le Y n).trans (by gcongr)) hmajor
    _ = expDerivativeBudget r := rfl

/-- The full noncommutative exponential derivative is Lipschitz on every
closed ball, with its explicit factorial-series budget. -/
theorem norm_fderiv_exp_sub_le_secondDerivativeBudget
    {r : ℝ} {Y Z : A}
    (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r) :
    ‖fderiv ℝ (NormedSpace.exp : A → A) Y -
        fderiv ℝ (NormedSpace.exp : A → A) Z‖ ≤
      expSecondDerivativeBudget r * ‖Y - Z‖ := by
  have hYSum := summable_natCast_div_factorial_mul_pow_pred ‖Y‖
  have hZSum := summable_natCast_div_factorial_mul_pow_pred ‖Z‖
  have hYDeriv : Summable (fun n : ℕ => expTermFDeriv Y n) :=
    (hYSum.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_expTermFDeriv_le Y n)).of_norm
  have hZDeriv : Summable (fun n : ℕ => expTermFDeriv Z n) :=
    (hZSum.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_expTermFDeriv_le Z n)).of_norm
  have hmajor := summable_expSecondDerivativeMajorant r
  have hmajorDiff : Summable (fun n : ℕ =>
      (((n : ℝ) / n.factorial) * n.pred * r ^ n.pred.pred) * ‖Y - Z‖) :=
    hmajor.mul_right ‖Y - Z‖
  have hdiffNorm : Summable (fun n : ℕ =>
      ‖expTermFDeriv Y n - expTermFDeriv Z n‖) :=
    hmajorDiff.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n =>
      norm_expTermFDeriv_sub_le Y Z r hY hZ n)
  rw [fderiv_exp_eq_ordered, fderiv_exp_eq_ordered,
    ← hYDeriv.tsum_sub hZDeriv]
  calc
    ‖∑' n : ℕ, (expTermFDeriv Y n - expTermFDeriv Z n)‖
        ≤ ∑' n : ℕ, ‖expTermFDeriv Y n - expTermFDeriv Z n‖ :=
      norm_tsum_le_tsum_norm hdiffNorm
    _ ≤ ∑' n : ℕ,
          (((n : ℝ) / n.factorial) * n.pred * r ^ n.pred.pred) *
            ‖Y - Z‖ := by
      exact hdiffNorm.tsum_le_tsum
        (fun n => norm_expTermFDeriv_sub_le Y Z r hY hZ n) hmajorDiff
    _ = expSecondDerivativeBudget r * ‖Y - Z‖ := by
      rw [tsum_mul_right]
      rfl

/-- Explicit quadratic two-point Taylor remainder for the noncommutative
exponential. -/
theorem norm_exp_sub_exp_sub_fderiv_le
    {r : ℝ} (hr0 : 0 ≤ r) {Y Z : A}
    (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r) :
    ‖NormedSpace.exp Y - NormedSpace.exp Z -
        (fderiv ℝ (NormedSpace.exp : A → A) Z) (Y - Z)‖ ≤
      expSecondDerivativeBudget r * ‖Y - Z‖ ^ 2 := by
  let H : A := Y - Z
  let LZ : A →L[ℝ] A := fderiv ℝ (NormedSpace.exp : A → A) Z
  let g : ℝ → A := fun s =>
    NormedSpace.exp (Z + s • H) - NormedSpace.exp Z - s • LZ H
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
        ((fderiv ℝ (NormedSpace.exp : A → A) (Z + s • H) - LZ) H)
        (Set.Icc (0 : ℝ) 1) s := by
    intro s hs
    have hline : HasDerivAt (fun q : ℝ => Z + q • H) H s := by
      convert (hasDerivAt_const s Z).add
        ((hasDerivAt_id s).smul_const H) using 1
      all_goals simp
    have hexp : HasDerivAt
        (fun q : ℝ => NormedSpace.exp (Z + q • H))
        ((fderiv ℝ (NormedSpace.exp : A → A) (Z + s • H)) H) s := by
      have hraw := (hasFDerivAt_exp_ordered (Z + s • H)).comp_hasDerivAt s hline
      rw [(hasFDerivAt_exp_ordered (Z + s • H)).fderiv]
      simpa only [Function.comp_apply] using hraw
    have hlin : HasDerivAt (fun q : ℝ => q • LZ H) (LZ H) s := by
      simpa using (hasDerivAt_id s).smul_const (LZ H)
    have hraw := (hexp.sub_const (NormedSpace.exp Z)).sub hlin
    have hderivEq :
        (fderiv ℝ (NormedSpace.exp : A → A) (Z + s • H)) H - LZ H =
          (fderiv ℝ (NormedSpace.exp : A → A) (Z + s • H) - LZ) H := by
      simp
    simpa only [g, hderivEq] using hraw.hasDerivWithinAt
  have hgBound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ‖(fderiv ℝ (NormedSpace.exp : A → A) (Z + s • H) - LZ) H‖ ≤
        expSecondDerivativeBudget r * ‖H‖ ^ 2 := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have hW := hsegment s hsIcc
    have hLip := norm_fderiv_exp_sub_le_secondDerivativeBudget hW hZ
    have hWs : ‖(Z + s • H) - Z‖ ≤ ‖H‖ := by
      have hsabs : |s| ≤ 1 := by
        rw [abs_of_nonneg hs.1]
        exact hs.2.le
      have heq : (Z + s • H) - Z = s • H := by abel
      rw [heq, norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg H) hsabs
    calc
      ‖(fderiv ℝ (NormedSpace.exp : A → A) (Z + s • H) - LZ) H‖
          ≤ ‖fderiv ℝ (NormedSpace.exp : A → A) (Z + s • H) - LZ‖ * ‖H‖ :=
        ContinuousLinearMap.le_opNorm _ H
      _ ≤ (expSecondDerivativeBudget r * ‖(Z + s • H) - Z‖) * ‖H‖ := by
        gcongr
      _ ≤ (expSecondDerivativeBudget r * ‖H‖) * ‖H‖ := by
        gcongr
        exact expSecondDerivativeBudget_nonneg r hr0
      _ = expSecondDerivativeBudget r * ‖H‖ ^ 2 := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' hgDeriv hgBound
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : g 1 =
      NormedSpace.exp Y - NormedSpace.exp Z - LZ H := by
    dsimp only [g]
    have hZH : Z + (1 : ℝ) • H = Y := by
      dsimp only [H]
      module
    rw [hZH, one_smul]
  rw [hg0, sub_zero, hg1] at hmv
  simpa only [H, LZ] using hmv

/-- Source-friendly displacement estimate obtained from the same quadratic
Taylor theorem and the explicit first-derivative budget. -/
theorem norm_exp_sub_exp_le_derivativeBudgets
    {r : ℝ} (hr0 : 0 ≤ r) {Y Z : A}
    (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r) :
    ‖NormedSpace.exp Y - NormedSpace.exp Z‖ ≤
      expSecondDerivativeBudget r * ‖Y - Z‖ ^ 2 +
        expDerivativeBudget r * ‖Y - Z‖ := by
  let LZ := fderiv ℝ (NormedSpace.exp : A → A) Z
  have hTaylor := norm_exp_sub_exp_sub_fderiv_le hr0 hY hZ
  have hL : ‖LZ‖ ≤ expDerivativeBudget r := by
    simpa [LZ] using norm_fderiv_exp_le_derivativeBudget hZ
  have hdecomp : NormedSpace.exp Y - NormedSpace.exp Z =
      (NormedSpace.exp Y - NormedSpace.exp Z - LZ (Y - Z)) +
        LZ (Y - Z) := by abel
  rw [hdecomp]
  calc
    ‖(NormedSpace.exp Y - NormedSpace.exp Z - LZ (Y - Z)) +
          LZ (Y - Z)‖
        ≤ ‖NormedSpace.exp Y - NormedSpace.exp Z - LZ (Y - Z)‖ +
            ‖LZ (Y - Z)‖ := norm_add_le _ _
    _ ≤ expSecondDerivativeBudget r * ‖Y - Z‖ ^ 2 +
          ‖LZ‖ * ‖Y - Z‖ := by
      exact add_le_add (by simpa [LZ] using hTaylor) (LZ.le_opNorm _)
    _ ≤ expSecondDerivativeBudget r * ‖Y - Z‖ ^ 2 +
          expDerivativeBudget r * ‖Y - Z‖ := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right hL (norm_nonneg (Y - Z)))

/-- Explicit norm budget for the noncommutative exponential on a closed
ball.  It is deliberately expressed using the already audited derivative
series, so no separate exponential majorant is introduced. -/
theorem norm_exp_le_derivativeBudgets
    {r : ℝ} (hr0 : 0 ≤ r) {Y : A} (hY : ‖Y‖ ≤ r) :
    ‖NormedSpace.exp Y‖ ≤
      1 + expSecondDerivativeBudget r * r ^ 2 +
        expDerivativeBudget r * r := by
  have hzero : ‖(0 : A)‖ ≤ r := by simpa using hr0
  have hdisp := norm_exp_sub_exp_le_derivativeBudgets hr0 hY hzero
  have hB2 : 0 ≤ expSecondDerivativeBudget r :=
    expSecondDerivativeBudget_nonneg r hr0
  have hB1 : 0 ≤ expDerivativeBudget r :=
    expDerivativeBudget_nonneg r hr0
  have hsq : ‖Y - (0 : A)‖ ^ 2 ≤ r ^ 2 :=
    sq_le_sq₀ (norm_nonneg _) hr0 |>.2 (by simpa using hY)
  have hlin : ‖Y - (0 : A)‖ ≤ r := by simpa using hY
  have htri : ‖NormedSpace.exp Y‖ ≤
      ‖NormedSpace.exp Y - NormedSpace.exp (0 : A)‖ + 1 := by
    have h := norm_add_le
      (NormedSpace.exp Y - NormedSpace.exp (0 : A))
      (NormedSpace.exp (0 : A))
    simpa using h
  calc
    ‖NormedSpace.exp Y‖
        ≤ ‖NormedSpace.exp Y - NormedSpace.exp (0 : A)‖ + 1 := htri
    _ ≤ (expSecondDerivativeBudget r * ‖Y - (0 : A)‖ ^ 2 +
          expDerivativeBudget r * ‖Y - (0 : A)‖) + 1 :=
      add_le_add hdisp (le_refl (1 : ℝ))
    _ ≤ (expSecondDerivativeBudget r * r ^ 2 +
          expDerivativeBudget r * r) + 1 := by
      gcongr
    _ = 1 + expSecondDerivativeBudget r * r ^ 2 +
          expDerivativeBudget r * r := by ring

end

end YangMills.RG
