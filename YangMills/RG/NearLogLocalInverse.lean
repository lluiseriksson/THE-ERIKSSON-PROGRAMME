/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLogTermFDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The noncommutative local inverse of the Mercator logarithm

This file proves the missing Banach-algebra identity

`exp (nearLog Y) = 1 + Y`, for `‖Y‖ < 1`.

The proof stays inside the one-generator commutative slice of the possibly
noncommutative ambient algebra.  Along `t ↦ t • Y`, the derivative of the
Mercator series is the geometric inverse of `1 + t • Y`, and the derivative
of the exponential has the ordinary commuting form.  Consequently

`exp (nearLog (t • Y)) * (1 + t • Y)⁻¹`

has derivative zero on the Mercator interval.  Evaluation at `t = 0` and
`t = 1` gives the claimed identity.  No matrix diagonalisation, logarithm
primitive, or renamed inverse hypothesis is used.
-/

namespace YangMills.RG

open scoped BigOperators RightActions

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- Every insertion position has the same value on the radial direction. -/
private theorem smul_pow_sub_mul_self_mul_smul_pow
    (t : ℝ) (Y : 𝔸) {n i : ℕ} (hi : i ≤ n) :
    (t • Y) ^ (n - i) * Y * (t • Y) ^ i =
      t ^ n • Y ^ (n + 1) := by
  rw [smul_pow, smul_pow]
  calc
    (t ^ (n - i) • Y ^ (n - i)) * Y * (t ^ i • Y ^ i) =
        (t ^ (n - i) * t ^ i) • (Y ^ (n - i) * Y * Y ^ i) := by
          simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
          rw [mul_comm (t ^ i)]
    _ = t ^ n • Y ^ (n + 1) := by
      rw [← pow_add, Nat.sub_add_cancel hi]
      congr 1
      rw [← pow_succ, ← pow_add]
      congr 1
      omega

/-- The scalar coefficient cancellation in one positive Mercator degree. -/
private theorem logCoeff_succ_mul_natCast_mul_pow (t : ℝ) (n : ℕ) :
    logCoeff (n + 1) * (n + 1 : ℕ) * t ^ n = (-t) ^ n := by
  rw [logCoeff, if_neg (Nat.succ_ne_zero n)]
  push_cast
  have hpow : (-1 : ℝ) ^ (n + 1 + 1) = (-1 : ℝ) ^ n := by
    rw [show n + 1 + 1 = n + 2 by omega, pow_add]
    norm_num
  rw [hpow]
  have hneg : (-t) ^ n = (-1 : ℝ) ^ n * t ^ n := neg_pow t n
  rw [hneg]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- On the radial line through `Y`, the derivative of one positive-degree
Mercator term collapses to a single monomial. -/
theorem nearLogTermFDeriv_smul_apply_self (t : ℝ) (Y : 𝔸) (n : ℕ) :
    nearLogTermFDeriv (t • Y) (n + 1) Y =
      (-t) ^ n • Y ^ (n + 1) := by
  rw [nearLogTermFDeriv_apply]
  simp only [Nat.pred_succ]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (t • Y) ^ (n - i) * Y * (t • Y) ^ i =
        t ^ n • Y ^ (n + 1) := by
    intro i hi
    have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact smul_pow_sub_mul_self_mul_smul_pow t Y hin
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, smul_smul, logCoeff_succ_mul_natCast_mul_pow]

/-- The Mercator derivative series is summable at every point of the open
unit ball. -/
theorem summable_nearLogTermFDeriv_of_norm_lt_one {Z : 𝔸} (hZ : ‖Z‖ < 1) :
    Summable (fun n : ℕ => nearLogTermFDeriv Z n) := by
  apply Summable.of_norm
  exact (summable_natCast_mul_pow_pred (norm_nonneg Z) hZ).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => norm_nearLogTermFDeriv_le Z n)

set_option maxHeartbeats 2000000 in
/-- Exact radial derivative of the noncommutative Mercator logarithm.  The
answer is the genuine ring inverse supplied by the convergent geometric
series, not an abstract inverse certificate. -/
theorem nearLogRadialFDeriv_apply_self (t : ℝ) (Y : 𝔸)
    (hZ : ‖t • Y‖ < 1) :
    (∑' n : ℕ, nearLogTermFDeriv (t • Y) n) Y =
      Ring.inverse (1 + t • Y) * Y := by
  have hder := summable_nearLogTermFDeriv_of_norm_lt_one hZ
  have hpoint : Summable (fun n : ℕ => nearLogTermFDeriv (t • Y) n Y) :=
    ((ContinuousLinearMap.apply ℝ 𝔸 Y).summable hder)
  have hgeomNorm : ‖(-t) • Y‖ < 1 := by simpa [norm_smul] using hZ
  have hgeom : Summable (fun n : ℕ => ((-t) • Y) ^ n) :=
    summable_geometric_of_norm_lt_one hgeomNorm
  calc
    (∑' n : ℕ, nearLogTermFDeriv (t • Y) n) Y =
        ∑' n : ℕ, nearLogTermFDeriv (t • Y) n Y := by
          exact (ContinuousLinearMap.apply ℝ 𝔸 Y).map_tsum hder
    _ = ∑' n : ℕ, nearLogTermFDeriv (t • Y) (n + 1) Y := by
          rw [hpoint.tsum_eq_zero_add]
          simp [nearLogTermFDeriv]
    _ = ∑' n : ℕ, (-t) ^ n • Y ^ (n + 1) := by
          apply tsum_congr
          exact fun n => nearLogTermFDeriv_smul_apply_self t Y n
    _ = ∑' n : ℕ, ((-t) • Y) ^ n * Y := by
          apply tsum_congr
          intro n
          rw [smul_pow, pow_succ]
          exact (Algebra.smul_mul_assoc _ _ _).symm
    _ = (∑' n : ℕ, ((-t) • Y) ^ n) * Y :=
          hgeom.tsum_mul_right Y
    _ = Ring.inverse (1 - ((-t) • Y)) * Y := by
          rw [geom_series_eq_inverse _ hgeomNorm]
    _ = Ring.inverse (1 + t • Y) * Y := by
          congr 2
          simp

/-- Two Mercator logarithms on the same radial line commute, even though the
ambient Banach algebra need not be commutative. -/
theorem nearLog_smul_commute_nearLog_smul (s t : ℝ) (Y : 𝔸) :
    Commute (nearLog (s • Y)) (nearLog (t • Y)) := by
  rw [nearLog, nearLog]
  apply Commute.tsum_left
  intro n
  apply Commute.tsum_right
  intro m
  exact (((Commute.refl Y).smul_left s).smul_right t).pow_pow n m
    |>.smul_left (logCoeff n) |>.smul_right (logCoeff m)

set_option maxHeartbeats 1000000 in
/-- The exponential of the radial Mercator logarithm has the expected
ordinary derivative.  The proof uses the exact commuting increment
factorisation, so no noncommutative derivative simplification is assumed. -/
theorem hasDerivAt_exp_nearLog_smul (t : ℝ) (Y : 𝔸)
    (hZ : ‖t • Y‖ < 1) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (nearLog (s • Y)))
      (NormedSpace.exp (nearLog (t • Y)) *
        (Ring.inverse (1 + t • Y) * Y)) t := by
  have hline : HasDerivAt (fun s : ℝ => s • Y) Y t :=
    by simpa using (hasDerivAt_id t).smul_const Y
  have hlogRaw :=
    (hasFDerivAt_nearLog_of_norm_lt_one hZ).comp t hline.hasFDerivAt
  have hlog : HasDerivAt (fun s : ℝ => nearLog (s • Y))
      (Ring.inverse (1 + t • Y) * Y) t := by
    have h := hlogRaw.hasDerivAt
    convert h using 1
    simpa [ContinuousLinearMap.comp_apply] using
      (nearLogRadialFDeriv_apply_self t Y hZ).symm
  have hdiff : HasDerivAt
      (fun s : ℝ => nearLog (s • Y) - nearLog (t • Y))
      (Ring.inverse (1 + t • Y) * Y) t :=
    hlog.sub_const _
  have hexpDiff : HasDerivAt
      (fun s : ℝ => NormedSpace.exp
        (nearLog (s • Y) - nearLog (t • Y)))
      (Ring.inverse (1 + t • Y) * Y) t := by
    have hexp0 : HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸)
        (1 : 𝔸 →L[ℝ] 𝔸)
        (nearLog (t • Y) - nearLog (t • Y)) := by
      simpa using (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸))
    have hcomp := hexp0.comp t hdiff.hasFDerivAt
    simpa using hcomp.hasDerivAt
  have hrhs := hexpDiff.hasFDerivAt.const_mul
    (NormedSpace.exp (nearLog (t • Y)))
  have hrhs' : HasDerivAt
      (fun s : ℝ => NormedSpace.exp (nearLog (t • Y)) *
        NormedSpace.exp (nearLog (s • Y) - nearLog (t • Y)))
      (NormedSpace.exp (nearLog (t • Y)) *
        (Ring.inverse (1 + t • Y) * Y)) t := by
    convert hrhs.hasDerivAt using 1
    simp
  apply hrhs'.congr_of_eventuallyEq
  filter_upwards [] with s
  have hcomm : Commute (nearLog (t • Y))
      (nearLog (s • Y) - nearLog (t • Y)) :=
    (nearLog_smul_commute_nearLog_smul t s Y).sub_right (Commute.refl _)
  calc
    NormedSpace.exp (nearLog (s • Y)) =
        NormedSpace.exp
          (nearLog (t • Y) +
            (nearLog (s • Y) - nearLog (t • Y))) := by
          congr 1
          abel
    _ = NormedSpace.exp (nearLog (t • Y)) *
          NormedSpace.exp
            (nearLog (s • Y) - nearLog (t • Y)) := by
          exact NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hcomm
            ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
            ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

/-- Derivative of the genuine ring inverse along the near-identity radial
line. -/
theorem hasDerivAt_ringInverse_one_add_smul (t : ℝ) (Y : 𝔸)
    (hZ : ‖t • Y‖ < 1) :
    HasDerivAt (fun s : ℝ => Ring.inverse (1 + s • Y))
      (-(Ring.inverse (1 + t • Y) * Y *
        Ring.inverse (1 + t • Y))) t := by
  have hneg : ‖(-t) • Y‖ < 1 := by simpa [norm_smul] using hZ
  have hunit : IsUnit (1 + t • Y) := by
    simpa using isUnit_one_sub_of_norm_lt_one (x := (-t) • Y) hneg
  rcases hunit with ⟨u, hu⟩
  have huinv : (↑u⁻¹ : 𝔸) = Ring.inverse (1 + t • Y) := by
    rw [← Ring.inverse_unit u, hu]
  have hinv : HasFDerivAt (Ring.inverse : 𝔸 → 𝔸)
      (-ContinuousLinearMap.mulLeftRight ℝ 𝔸
        (Ring.inverse (1 + t • Y)) (Ring.inverse (1 + t • Y)))
      (1 + t • Y) := by
    simpa only [hu, huinv] using (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
  have hline : HasDerivAt (fun s : ℝ => 1 + s • Y) Y t := by
    simpa using ((hasDerivAt_id t).smul_const Y).const_add (1 : 𝔸)
  have hcomp := hinv.comp t hline.hasFDerivAt
  convert hcomp.hasDerivAt using 1
  simp [ContinuousLinearMap.mulLeftRight_apply]

set_option maxHeartbeats 1000000 in
/-- The multiplicative comparison between `exp (nearLog (tY))` and
`1+tY` has zero derivative throughout the Mercator interval. -/
theorem hasDerivAt_exp_nearLog_mul_ringInverse (t : ℝ) (Y : 𝔸)
    (hZ : ‖t • Y‖ < 1) :
    HasDerivAt
      (fun s : ℝ => NormedSpace.exp (nearLog (s • Y)) *
        Ring.inverse (1 + s • Y)) 0 t := by
  have hE := hasDerivAt_exp_nearLog_smul t Y hZ
  have hI := hasDerivAt_ringInverse_one_add_smul t Y hZ
  have hmul := hE.mul hI
  convert hmul using 1
  noncomm_ring

set_option maxHeartbeats 2000000 in
/-- **Noncommutative Banach-algebra local inverse.**  On the full Mercator
ball, exponentiating the near-identity logarithm recovers the original
near-identity element exactly. -/
theorem exp_nearLog_eq_one_add {Y : 𝔸} (hY : ‖Y‖ < 1) :
    NormedSpace.exp (nearLog Y) = 1 + Y := by
  let L : ℝ →L[ℝ] 𝔸 := ContinuousLinearMap.toSpanSingleton ℝ Y
  let s : Set ℝ := L ⁻¹' Metric.ball (0 : 𝔸) 1
  let F : ℝ → 𝔸 := fun t =>
    NormedSpace.exp (nearLog (t • Y)) * Ring.inverse (1 + t • Y)
  have hsOpen : IsOpen s := Metric.isOpen_ball.preimage L.continuous
  have hsConvex : Convex ℝ s :=
    (convex_ball (0 : 𝔸) (1 : ℝ)).linear_preimage L.toLinearMap
  have hmem_iff (t : ℝ) : t ∈ s ↔ ‖t • Y‖ < 1 := by
    simp [s, L, Metric.mem_ball, dist_eq_norm,
      ContinuousLinearMap.toSpanSingleton_apply]
  have hFdiff : DifferentiableOn ℝ F s := by
    intro t ht
    exact (hasDerivAt_exp_nearLog_mul_ringInverse t Y
      ((hmem_iff t).mp ht)).differentiableAt.differentiableWithinAt
  have hFzero : s.EqOn (deriv F) 0 := by
    intro t ht
    exact (hasDerivAt_exp_nearLog_mul_ringInverse t Y
      ((hmem_iff t).mp ht)).deriv
  have hzero : (0 : ℝ) ∈ s := (hmem_iff 0).mpr (by simp)
  have hone : (1 : ℝ) ∈ s := (hmem_iff 1).mpr (by simpa using hY)
  have hconst : F 1 = F 0 :=
    hsOpen.is_const_of_deriv_eq_zero hsConvex.isPreconnected hFdiff hFzero hone hzero
  have hcompare : NormedSpace.exp (nearLog Y) * Ring.inverse (1 + Y) = 1 := by
    simpa [F] using hconst
  have hneg : ‖(-1 : ℝ) • Y‖ < 1 := by simpa [norm_smul] using hY
  have hunit : IsUnit (1 + Y) := by
    simpa using isUnit_one_sub_of_norm_lt_one (x := (-1 : ℝ) • Y) hneg
  calc
    NormedSpace.exp (nearLog Y) =
        NormedSpace.exp (nearLog Y) * Ring.inverse (1 + Y) * (1 + Y) :=
      (Ring.inverse_mul_cancel_right (1 + Y)
        (NormedSpace.exp (nearLog Y)) hunit).symm
    _ = 1 * (1 + Y) := by rw [hcompare]
    _ = 1 + Y := one_mul _

end

end YangMills.RG
