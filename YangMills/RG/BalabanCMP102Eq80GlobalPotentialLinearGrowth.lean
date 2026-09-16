/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80GlobalPotential

/-!
# First-order normalization from linear growth of the CMP102 correction

The background correction in equation (80) need not be differentiated in
order to prove that the global higher-order potential has zero derivative.
It is enough that the correction vanish at zero and grow at most linearly.
The two occurrences of that correction are then genuinely quadratic, while
the `V₀` remainder is composed with a map that is merely `O(A)`.
-/

open scoped RealInnerProductSpace Topology

namespace YangMills.RG

noncomputable section

open Asymptotics Filter

set_option maxHeartbeats 10000000 in
/-- Equation (80) has zero derivative at the origin when its background
correction is only known to have linear growth.  No continuity or
differentiability hypothesis on `D` is used. -/
theorem cmp102Eq80GlobalPotential_hasFDerivAt_zero_of_linearGrowth
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (H : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (J : E)
    (C : ℝ) (hC : 0 ≤ C)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hDgrowth : ∀ᶠ A in 𝓝 0, ‖D A‖ ≤ C * ‖A‖)
    (hD₃ : HasFDerivAt D₃ (0 : E →L[ℝ] F) 0)
    (hV₀ : HasFDerivAt V₀ (0 : E →L[ℝ] ℝ) 0) :
    HasFDerivAt (cmp102Eq80GlobalPotential D D₃ V₀ H Δπ J)
      (0 : E →L[ℝ] ℝ) 0 := by
  let g : E → E := fun A => A - H (D A)
  have hD_bigO : D =O[𝓝 0] (fun A : E => A) :=
    IsBigO.of_bound C hDgrowth
  have hHD_bigO : (fun A => H (D A)) =O[𝓝 0] (fun A : E => A) := by
    apply IsBigO.of_bound (‖H‖ * C)
    filter_upwards [hDgrowth] with A hDA
    calc
      ‖H (D A)‖ ≤ ‖H‖ * ‖D A‖ := H.le_opNorm (D A)
      _ ≤ ‖H‖ * (C * ‖A‖) :=
        mul_le_mul_of_nonneg_left hDA (norm_nonneg H)
      _ = (‖H‖ * C) * ‖A‖ := by ring
  have hg_bigO : g =O[𝓝 0] (fun A : E => A) := by
    exact (isBigO_refl (fun A : E => A) (𝓝 0)).sub hHD_bigO
  have hg_tendsto : Tendsto g (𝓝 0) (𝓝 0) :=
    hg_bigO.trans_tendsto (continuous_id.tendsto 0)
  have hfirst :
      (fun A => - inner ℝ (H (D₃ A)) J) =o[𝓝 0] (fun A : E => A) := by
    have hHD₃ : HasFDerivAt (fun A => H (D₃ A))
        (0 : E →L[ℝ] E) 0 := by
      simpa using H.hasFDerivAt.comp 0 hD₃
    have hJ : HasFDerivAt (fun _ : E => J)
        (0 : E →L[ℝ] E) 0 :=
      hasFDerivAt_const (x := (0 : E)) (c := J)
    have h :
        HasFDerivAt (fun A => - inner ℝ (H (D₃ A)) J)
          (0 : E →L[ℝ] ℝ) 0 := by
      convert (hHD₃.inner ℝ hJ).neg using 1
      ext v
      simp [hD₃0]
    simpa [hD₃0] using h.isLittleO
  have hsecond_bigO :
      (fun A => - inner ℝ A (Δπ (H (D A)))) =O[𝓝 0]
        (fun A : E => ‖A‖ ^ 2) := by
    apply IsBigO.of_bound (‖Δπ‖ * ‖H‖ * C)
    filter_upwards [hDgrowth] with A hDA
    rw [Real.norm_eq_abs, abs_neg]
    calc
      |inner ℝ A (Δπ (H (D A)))|
          ≤ ‖A‖ * ‖Δπ (H (D A))‖ := abs_real_inner_le_norm A _
      _ ≤ ‖A‖ * (‖Δπ‖ * ‖H (D A)‖) := by
        gcongr
        exact Δπ.le_opNorm (H (D A))
      _ ≤ ‖A‖ * (‖Δπ‖ * (‖H‖ * ‖D A‖)) := by
        gcongr
        exact H.le_opNorm (D A)
      _ ≤ ‖A‖ * (‖Δπ‖ * (‖H‖ * (C * ‖A‖))) := by
        gcongr
      _ = (‖Δπ‖ * ‖H‖ * C) * ‖‖A‖ ^ 2‖ := by
        rw [Real.norm_of_nonneg (sq_nonneg ‖A‖)]
        ring
  have hsecond :
      (fun A => - inner ℝ A (Δπ (H (D A)))) =o[𝓝 0]
        (fun A : E => A) :=
    hsecond_bigO.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  have hthird_bigO :
      (fun A => (1 / 2 : ℝ) *
          inner ℝ (H (D A)) (Δπ (H (D A)))) =O[𝓝 0]
        (fun A : E => ‖A‖ ^ 2) := by
    apply IsBigO.of_bound
      ((1 / 2 : ℝ) * ‖Δπ‖ * (‖H‖ * C) ^ 2)
    filter_upwards [hDgrowth] with A hDA
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc
      (1 / 2 : ℝ) * |inner ℝ (H (D A)) (Δπ (H (D A)))|
          ≤ (1 / 2 : ℝ) *
              (‖H (D A)‖ * ‖Δπ (H (D A))‖) := by
        gcongr
        exact abs_real_inner_le_norm _ _
      _ ≤ (1 / 2 : ℝ) *
          ((‖H‖ * ‖D A‖) * (‖Δπ‖ * (‖H‖ * ‖D A‖))) := by
        gcongr
        · exact H.le_opNorm (D A)
        · exact (Δπ.le_opNorm (H (D A))).trans
            (mul_le_mul_of_nonneg_left
              (H.le_opNorm (D A)) (norm_nonneg Δπ))
      _ ≤ (1 / 2 : ℝ) *
          ((‖H‖ * (C * ‖A‖)) *
            (‖Δπ‖ * (‖H‖ * (C * ‖A‖)))) := by
        gcongr
      _ = ((1 / 2 : ℝ) * ‖Δπ‖ * (‖H‖ * C) ^ 2) *
          ‖‖A‖ ^ 2‖ := by
        rw [Real.norm_of_nonneg (sq_nonneg ‖A‖)]
        ring
  have hthird :
      (fun A => (1 / 2 : ℝ) *
          inner ℝ (H (D A)) (Δπ (H (D A)))) =o[𝓝 0]
        (fun A : E => A) :=
    hthird_bigO.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  have hV₀_little :
      (fun x => V₀ x - V₀ 0) =o[𝓝 0] (fun x : E => x) := by
    simpa using hV₀.isLittleO
  have hfourth :
      (fun A => V₀ (g A) - V₀ 0) =o[𝓝 0] (fun A : E => A) := by
    exact (hV₀_little.comp_tendsto hg_tendsto).trans_isBigO hg_bigO
  have hsum :=
    ((hfirst.add hsecond).add hthird).add hfourth
  apply HasFDerivAt.of_isLittleO
  convert hsum using 1
  · funext A
    simp [cmp102Eq80GlobalPotential, g, hD0, hD₃0]
    ring
  · funext A
    simp

end

end YangMills.RG
