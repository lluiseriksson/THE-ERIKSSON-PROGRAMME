/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLogFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Noncommutative derivatives of the Mercator terms

For a noncommutative Banach algebra the derivative of `Y ^ n` is the ordered
insertion sum

`H ↦ ∑ i < n, Y ^ (n - 1 - i) * H * Y ^ i`.

This is the termwise analytic structure behind the `g(ad y)` corrections in
CMP98 (124).  The present file constructs each continuous linear derivative
and proves its exact Fréchet-derivative identity.  It does not yet interchange
the derivative with the infinite Mercator sum.
-/

namespace YangMills.RG

open scoped BigOperators RightActions

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The exact noncommutative derivative of the `n`-th Mercator summand at
`Y`, packaged as a continuous real-linear map. -/
noncomputable def nearLogTermFDeriv (Y : 𝔸) (n : ℕ) : 𝔸 →L[ℝ] 𝔸 :=
  logCoeff n •
    ∑ i ∈ Finset.range n,
      Y ^ (n.pred - i) •> ContinuousLinearMap.id ℝ 𝔸 <• Y ^ i

/-- Pointwise form of the ordered insertion derivative. -/
theorem nearLogTermFDeriv_apply (Y H : 𝔸) (n : ℕ) :
    nearLogTermFDeriv Y n H =
      logCoeff n • ∑ i ∈ Finset.range n,
        Y ^ (n.pred - i) * H * Y ^ i := by
  simp [nearLogTermFDeriv]

/-- Uniform pointwise majorant for one noncommutative Mercator derivative.
There are exactly `n` insertion positions and every ordered product has total
background degree `n - 1`. -/
theorem norm_nearLogTermFDeriv_apply_le [NormOneClass 𝔸]
    (Y H : 𝔸) (n : ℕ) :
    ‖nearLogTermFDeriv Y n H‖ ≤
      (n : ℝ) * ‖Y‖ ^ n.pred * ‖H‖ := by
  rw [nearLogTermFDeriv_apply, norm_smul, Real.norm_eq_abs]
  calc
    |logCoeff n| * ‖∑ i ∈ Finset.range n,
        Y ^ (n.pred - i) * H * Y ^ i‖
        ≤ 1 * ∑ i ∈ Finset.range n,
            ‖Y ^ (n.pred - i) * H * Y ^ i‖ := by
          gcongr
          · exact abs_logCoeff_le_one n
          · exact norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n,
          (‖Y‖ ^ n.pred * ‖H‖) := by
        simp only [one_mul]
        apply Finset.sum_le_sum
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        have hle : i ≤ n.pred := Nat.le_pred_of_lt hin
        calc
          ‖Y ^ (n.pred - i) * H * Y ^ i‖
              ≤ (‖Y ^ (n.pred - i)‖ * ‖H‖) * ‖Y ^ i‖ := by
                exact (norm_mul_le _ _).trans
                  (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ (‖Y‖ ^ (n.pred - i) * ‖H‖) * ‖Y‖ ^ i := by
                gcongr
                · exact norm_pow_le _ _
                · exact norm_pow_le _ _
          _ = ‖Y‖ ^ n.pred * ‖H‖ := by
                calc
                  ‖Y‖ ^ (n.pred - i) * ‖H‖ * ‖Y‖ ^ i =
                      (‖Y‖ ^ (n.pred - i) * ‖Y‖ ^ i) * ‖H‖ := by ring
                  _ = ‖Y‖ ^ ((n.pred - i) + i) * ‖H‖ := by rw [pow_add]
                  _ = ‖Y‖ ^ n.pred * ‖H‖ := by rw [Nat.sub_add_cancel hle]
    _ = (n : ℝ) * ‖Y‖ ^ n.pred * ‖H‖ := by
      simp [mul_assoc]

/-- Operator-norm version of the termwise derivative majorant. -/
theorem norm_nearLogTermFDeriv_le [NormOneClass 𝔸]
    (Y : 𝔸) (n : ℕ) :
    ‖nearLogTermFDeriv Y n‖ ≤ (n : ℝ) * ‖Y‖ ^ n.pred := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro H
  simpa [mul_assoc] using norm_nearLogTermFDeriv_apply_le Y H n

/-- Each Mercator summand has the ordered insertion derivative printed in
`nearLogTermFDeriv`. -/
theorem hasFDerivAt_logCoeff_smul_pow
    (Y : 𝔸) (n : ℕ) :
    HasFDerivAt
      (fun Z : 𝔸 => logCoeff n • Z ^ n)
      (nearLogTermFDeriv Y n) Y := by
  simpa [nearLogTermFDeriv] using
    ((hasFDerivAt_pow' (𝕜 := ℝ) n (x := Y)).const_smul (logCoeff n))

/-- The derivative majorants are summable on every strictly smaller
Mercator ball. -/
theorem summable_natCast_mul_pow_pred {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) * r ^ n.pred) := by
  rw [← summable_nat_add_iff 1]
  have hrnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hpow : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm)
  have hgeo : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  simpa [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, add_mul] using
    hpow.add hgeo

/- **General noncommutative Mercator derivative.**  At every point inside
the open unit ball, `nearLog` has the absolutely convergent ordered-insertion
derivative obtained by summing `nearLogTermFDeriv`. -/
set_option maxHeartbeats 2000000 in
theorem hasFDerivAt_nearLog_of_norm_lt_one [NormOneClass 𝔸]
    {Y : 𝔸} (hY : ‖Y‖ < 1) :
    HasFDerivAt (nearLog : 𝔸 → 𝔸)
      (∑' n : ℕ, nearLogTermFDeriv Y n) Y := by
  let r : ℝ := (‖Y‖ + 1) / 2
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hYr : ‖Y‖ < r := by
    dsimp [r]
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have hu : Summable (fun n : ℕ => (n : ℝ) * r ^ n.pred) :=
    summable_natCast_mul_pow_pred hr0 hr1
  have hbound : ∀ n (Z : 𝔸), Z ∈ Metric.ball (0 : 𝔸) r →
      ‖nearLogTermFDeriv Z n‖ ≤ (n : ℝ) * r ^ n.pred := by
    intro n Z hZ
    have hnorm : ‖Z‖ < r := by
      simpa [mem_ball_zero_iff] using hZ
    calc
      ‖nearLogTermFDeriv Z n‖ ≤ (n : ℝ) * ‖Z‖ ^ n.pred :=
        norm_nearLogTermFDeriv_le Z n
      _ ≤ (n : ℝ) * r ^ n.pred := by
        gcongr
  have hseries := hasFDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => (n : ℝ) * r ^ n.pred)
    (s := Metric.ball (0 : 𝔸) r)
    (f := fun n Z => logCoeff n • Z ^ n)
    (f' := fun n Z => nearLogTermFDeriv Z n)
    (x₀ := (0 : 𝔸)) (x := Y)
    hu Metric.isOpen_ball (convex_ball (0 : 𝔸) r).isPreconnected
    (fun n Z _ => hasFDerivAt_logCoeff_smul_pow Z n)
    hbound (Metric.mem_ball_self (by positivity))
    (summable_logCoeff_smul_pow (Y := (0 : 𝔸)) (by simp))
    (by simpa [mem_ball_zero_iff] using hYr)
  simpa [nearLog] using hseries

/-- Chain rule at a nontrivial near-identity background.  This is the exact
interface used by the complete CMP98 average: the ordered-insertion Mercator
derivative is composed with the derivative of the physical holonomy
deviation. -/
theorem HasFDerivAt.nearLog_of_norm_lt_one [NormOneClass 𝔸]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → 𝔸} {F' : E →L[ℝ] 𝔸} {x : E}
    (hF : HasFDerivAt F F' x) (hnorm : ‖F x‖ < 1) :
    HasFDerivAt (fun y => nearLog (F y))
      ((∑' n : ℕ, nearLogTermFDeriv (F x) n).comp F') x := by
  exact (hasFDerivAt_nearLog_of_norm_lt_one hnorm).comp x hF

@[simp]
theorem nearLogTermFDeriv_zero :
    nearLogTermFDeriv (0 : 𝔸) 0 = 0 := by
  simp [nearLogTermFDeriv]

@[simp]
theorem nearLogTermFDeriv_one (Y : 𝔸) :
    nearLogTermFDeriv Y 1 = ContinuousLinearMap.id ℝ 𝔸 := by
  simp [nearLogTermFDeriv, logCoeff]

end

end YangMills.RG
