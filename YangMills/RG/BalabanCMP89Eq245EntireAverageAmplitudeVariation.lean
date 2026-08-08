/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Algebra.BigOperators.Fin
import YangMills.RG.BalabanCMP89Eq245EntireAverageVerticalVariation

/-!
# Coordinatewise variation of the CMP89 entire average

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

This module telescopes the sealed one-coordinate vertical estimate through
the product over momentum coordinates.  It keeps the dimension factor and
every strip-growth factor explicit.  The resulting estimate is deliberately
slightly coarse but uniform in the averaging scale and reciprocal alias.

No stabilized-denominator variation, strip radius, `B0`, contour shift or
regional-Green estimate is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Coordinatewise real projection of a complex momentum. -/
def cmp89Eq245ComplexMomentumRealSlice
    {d : ℕ} (z : Fin d → ℂ) : Fin d → ℂ :=
  fun mu => ((z mu).re : ℂ)

/-- A finite product varies by at most `d * eps * R^d` if every factor is
bounded by `R >= 1` and varies by at most `eps`.  The extra power of `R` keeps
the formula uniform at `d = 0` and avoids a hidden predecessor convention. -/
theorem norm_fin_prod_sub_prod_le_card_mul
    (d : ℕ) (f g : Fin d → ℂ) {R eps : ℝ}
    (hR : 1 ≤ R) (heps : 0 ≤ eps)
    (hf : ∀ i, ‖f i‖ ≤ R) (hg : ∀ i, ‖g i‖ ≤ R)
    (hfg : ∀ i, ‖f i - g i‖ ≤ eps) :
    ‖(∏ i, f i) - ∏ i, g i‖ ≤ (d : ℝ) * eps * R ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      have hR0 : 0 ≤ R := zero_le_one.trans hR
      have hprodF : ‖∏ i : Fin d, f i.succ‖ ≤ R ^ d := by
        rw [norm_prod]
        calc
          ∏ i : Fin d, ‖f i.succ‖ ≤ ∏ _i : Fin d, R := by
            exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
              (fun i _ => hf i.succ)
          _ = R ^ d := by simp
      have htail :
          ‖(∏ i : Fin d, f i.succ) - ∏ i : Fin d, g i.succ‖ ≤
            (d : ℝ) * eps * R ^ d := by
        exact ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hf i.succ) (fun i => hg i.succ)
          (fun i => hfg i.succ)
      have hrewrite :
          f 0 * (∏ i : Fin d, f i.succ) -
              g 0 * (∏ i : Fin d, g i.succ) =
            (f 0 - g 0) * (∏ i : Fin d, f i.succ) +
              g 0 * ((∏ i : Fin d, f i.succ) -
                ∏ i : Fin d, g i.succ) := by ring
      rw [hrewrite]
      calc
        ‖(f 0 - g 0) * (∏ i : Fin d, f i.succ) +
            g 0 * ((∏ i : Fin d, f i.succ) -
              ∏ i : Fin d, g i.succ)‖ ≤
          ‖(f 0 - g 0) * (∏ i : Fin d, f i.succ)‖ +
            ‖g 0 * ((∏ i : Fin d, f i.succ) -
              ∏ i : Fin d, g i.succ)‖ := norm_add_le _ _
        _ = ‖f 0 - g 0‖ * ‖∏ i : Fin d, f i.succ‖ +
              ‖g 0‖ * ‖(∏ i : Fin d, f i.succ) -
                ∏ i : Fin d, g i.succ‖ := by rw [norm_mul, norm_mul]
        _ ≤ eps * R ^ d + R * ((d : ℝ) * eps * R ^ d) := by
          exact add_le_add
            (mul_le_mul (hfg 0) hprodF (norm_nonneg _) heps)
            (mul_le_mul (hg 0) htail (norm_nonneg _) hR0)
        _ ≤ ((d + 1 : ℕ) : ℝ) * eps * R ^ (d + 1) := by
          have hx : 0 ≤ eps * R ^ d := mul_nonneg heps (pow_nonneg hR0 d)
          calc
            eps * R ^ d + R * ((d : ℝ) * eps * R ^ d) =
                (1 + (d : ℝ) * R) * (eps * R ^ d) := by ring
            _ ≤ (((d : ℝ) + 1) * R) * (eps * R ^ d) := by
              apply mul_le_mul_of_nonneg_right _ hx
              calc
                1 + (d : ℝ) * R ≤ R + (d : ℝ) * R :=
                  by simpa [add_comm] using
                    add_le_add_right hR ((d : ℝ) * R)
                _ = ((d : ℝ) + 1) * R := by ring
            _ = ((d + 1 : ℕ) : ℝ) * eps * R ^ (d + 1) := by
              push_cast
              rw [pow_succ]
              ring

/-- The full `d`-coordinate average varies vertically with an explicit,
scale-uniform product cost. -/
theorem norm_cmp89Eq245EntireAverageAmplitude_sub_realSlice_le
    {d N : ℕ} (hN : 0 < N) {z : Fin d → ℂ} {rho : ℝ}
    (hrho : 0 ≤ rho) (hz : ∀ mu, |(z mu).im| ≤ rho) :
    ‖cmp89Eq245EntireAverageAmplitude d N z -
        cmp89Eq245EntireAverageAmplitude d N
          (cmp89Eq245ComplexMomentumRealSlice z)‖ ≤
      (d : ℝ) * (rho * Real.exp rho) * (Real.exp rho) ^ d := by
  unfold cmp89Eq245EntireAverageAmplitude
  apply norm_fin_prod_sub_prod_le_card_mul d
    (fun mu => cmp89Eq245EntireAverageFactor N (z mu))
    (fun mu => cmp89Eq245EntireAverageFactor N
      (cmp89Eq245ComplexMomentumRealSlice z mu))
  · exact Real.one_le_exp hrho
  · exact mul_nonneg hrho (Real.exp_pos rho).le
  · intro mu
    exact norm_cmp89Eq245EntireAverageFactor_le_exp hN hrho (hz mu)
  · intro mu
    apply norm_cmp89Eq245EntireAverageFactor_le_exp hN hrho
    simp [cmp89Eq245ComplexMomentumRealSlice, hrho]
  · intro mu
    exact norm_cmp89Eq245EntireAverageFactor_sub_realSlice_le hN hrho (hz mu)

/-- Negation commutes exactly with coordinatewise projection to the real
slice. -/
theorem cmp89Eq245ComplexMomentumRealSlice_neg
    {d : ℕ} (z : Fin d → ℂ) :
    cmp89Eq245ComplexMomentumRealSlice (-z) =
      -cmp89Eq245ComplexMomentumRealSlice z := by
  funext mu
  simp [cmp89Eq245ComplexMomentumRealSlice]

/-- The holomorphic opposite-momentum pairing has a scale-uniform vertical
variation bound.  Both product-rule contributions and both strip-growth
factors remain visible. -/
theorem norm_cmp89Eq245EntireAverageAmplitude_pair_sub_realSlice_le
    {d N : ℕ} (hN : 0 < N) {z : Fin d → ℂ} {rho : ℝ}
    (hrho : 0 ≤ rho) (hz : ∀ mu, |(z mu).im| ≤ rho) :
    ‖cmp89Eq245EntireAverageAmplitude d N z *
          cmp89Eq245EntireAverageAmplitude d N (-z) -
        cmp89Eq245EntireAverageAmplitude d N
            (cmp89Eq245ComplexMomentumRealSlice z) *
          cmp89Eq245EntireAverageAmplitude d N
            (-cmp89Eq245ComplexMomentumRealSlice z)‖ ≤
      2 * ((d : ℝ) * (rho * Real.exp rho) * (Real.exp rho) ^ d) *
        (Real.exp rho) ^ d := by
  let A := cmp89Eq245EntireAverageAmplitude d N z
  let B := cmp89Eq245EntireAverageAmplitude d N (-z)
  let A0 := cmp89Eq245EntireAverageAmplitude d N
    (cmp89Eq245ComplexMomentumRealSlice z)
  let B0 := cmp89Eq245EntireAverageAmplitude d N
    (-cmp89Eq245ComplexMomentumRealSlice z)
  have hA : ‖A - A0‖ ≤
      (d : ℝ) * (rho * Real.exp rho) * (Real.exp rho) ^ d := by
    exact norm_cmp89Eq245EntireAverageAmplitude_sub_realSlice_le hN hrho hz
  have hB : ‖B - B0‖ ≤
      (d : ℝ) * (rho * Real.exp rho) * (Real.exp rho) ^ d := by
    have hzneg : ∀ mu, |((-z) mu).im| ≤ rho := by
      intro mu
      simpa using hz mu
    simpa [B, B0, cmp89Eq245ComplexMomentumRealSlice_neg] using
      norm_cmp89Eq245EntireAverageAmplitude_sub_realSlice_le
        (d := d) (N := N) hN hrho hzneg
  have hBnorm : ‖B‖ ≤ (Real.exp rho) ^ d := by
    exact norm_cmp89Eq245EntireAverageAmplitude_le_exp_pow hN hrho
      (fun mu => by simpa using hz mu)
  have hA0norm : ‖A0‖ ≤ (Real.exp rho) ^ d := by
    apply norm_cmp89Eq245EntireAverageAmplitude_le_exp_pow hN hrho
    intro mu
    simp [cmp89Eq245ComplexMomentumRealSlice, hrho]
  have hrewrite : A * B - A0 * B0 = (A - A0) * B + A0 * (B - B0) := by
    ring
  change ‖A * B - A0 * B0‖ ≤ _
  rw [hrewrite]
  calc
    ‖(A - A0) * B + A0 * (B - B0)‖ ≤
        ‖(A - A0) * B‖ + ‖A0 * (B - B0)‖ := norm_add_le _ _
    _ = ‖A - A0‖ * ‖B‖ + ‖A0‖ * ‖B - B0‖ := by rw [norm_mul, norm_mul]
    _ ≤ ((d : ℝ) * (rho * Real.exp rho) * (Real.exp rho) ^ d) *
          (Real.exp rho) ^ d +
        (Real.exp rho) ^ d *
          ((d : ℝ) * (rho * Real.exp rho) * (Real.exp rho) ^ d) := by
      gcongr
    _ = 2 * ((d : ℝ) * (rho * Real.exp rho) * (Real.exp rho) ^ d) *
          (Real.exp rho) ^ d := by ring

end

end YangMills.RG
