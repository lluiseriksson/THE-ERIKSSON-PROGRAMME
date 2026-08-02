/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalCriticalRescalingNoGoAllCoarse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Fourier transverse obstruction for the critical flat block form

This module replaces the block-periodic square witness by the first complex
Fourier mode, embedded in a real two-plane of `SUNLieCoord Nc`.  Its exact
Rayleigh quotient is the first-cycle eigenvalue

`‖exp (2π i / L) - 1‖² = 4 sin² (π / L) ≤ 4π² / L²`.

The mode exists for every `L ≥ 2`, has exact zero block average and exact zero
flat divergence, and strengthens the full-space critical no-go from an
`O(L⁻¹)` subsequence witness to an `O(L⁻²)` all-scales witness.
-/

namespace YangMills.RG

open Matrix Module

/-! ## A primitive root and its real Lie-coordinate plane -/

/-- The primitive `L`-th root of unity used by the fine Fourier profile. -/
noncomputable def blockFourierRoot (L : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (L : ℂ))

theorem blockFourierRoot_pow_eq_one (L : ℕ) [NeZero L] :
    blockFourierRoot L ^ L = 1 := by
  unfold blockFourierRoot
  rw [← Complex.exp_nat_mul]
  have hLne : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hrew : (L : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (L : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I := by
    field_simp
  rw [hrew]
  exact Complex.exp_two_pi_mul_I

theorem blockFourierRoot_ne_one (L : ℕ) [NeZero L] (hL : 2 ≤ L) :
    blockFourierRoot L ≠ 1 := by
  intro hEq
  unfold blockFourierRoot at hEq
  rw [Complex.exp_eq_one_iff] at hEq
  obtain ⟨n, hn⟩ := hEq
  have h2piI_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    refine mul_ne_zero two_ne_zero ?_
    exact_mod_cast Real.pi_ne_zero
  have hLne : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hflipped : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
      (2 * (Real.pi : ℂ) * Complex.I) / (L : ℂ) := hn.symm
  have hmulL : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (L : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I := by
    rw [hflipped, div_mul_cancel₀ _ hLne]
  have h1C : (1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
      ((n : ℂ) * (L : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [one_mul]
    calc
      2 * (Real.pi : ℂ) * Complex.I =
          (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (L : ℂ) := hmulL.symm
      _ = ((n : ℂ) * (L : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
  have h1 : (1 : ℂ) = (n : ℂ) * (L : ℂ) :=
    mul_right_cancel₀ h2piI_ne h1C
  have hRe : (1 : ℝ) = (n : ℝ) * (L : ℝ) := by
    have := congrArg Complex.re h1
    simpa using this
  have hLR : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLRpos : (0 : ℝ) < (L : ℝ) := by linarith
  rcases lt_trichotomy (n : ℝ) 0 with hneg | hzero | hpos
  · have hprod_neg : (n : ℝ) * (L : ℝ) < 0 :=
      mul_neg_of_neg_of_pos hneg hLRpos
    linarith
  · rw [hzero, zero_mul] at hRe
    exact absurd hRe one_ne_zero
  · have hn_int_pos : (1 : ℤ) ≤ n := by
      have h0 : (0 : ℤ) < n := by exact_mod_cast hpos
      omega
    have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_int_pos
    have hprod_ge_two : (2 : ℝ) ≤ (n : ℝ) * (L : ℝ) := by
      calc
        (2 : ℝ) = 1 * 2 := by norm_num
        _ ≤ (n : ℝ) * (L : ℝ) :=
          mul_le_mul hn_ge_one hLR (by norm_num) (by linarith)
    linarith

theorem sum_blockFourierRoot_pow_eq_zero
    (L : ℕ) [NeZero L] (hL : 2 ≤ L) :
    ∑ r : Fin L, blockFourierRoot L ^ r.val = 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  rw [geom_sum_eq (blockFourierRoot_ne_one L hL)]
  rw [blockFourierRoot_pow_eq_one, sub_self, zero_div]

theorem norm_blockFourierRoot (L : ℕ) : ‖blockFourierRoot L‖ = 1 := by
  unfold blockFourierRoot
  rw [Complex.norm_exp]
  simp

theorem blockFourierRoot_eq_exp_I
    (L : ℕ) [NeZero L] :
    blockFourierRoot L =
      Complex.exp (Complex.I * (((2 * Real.pi / L : ℝ)) : ℂ)) := by
  unfold blockFourierRoot
  congr 1
  push_cast
  ring

theorem norm_blockFourierRoot_sub_one_le
    (L : ℕ) [NeZero L] :
    ‖blockFourierRoot L - 1‖ ≤ 2 * Real.pi / L := by
  rw [blockFourierRoot_eq_exp_I]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := 2 * Real.pi / (L : ℝ))
  rw [Real.norm_of_nonneg (by positivity)] at h
  exact h

/-- First coordinate of a real two-plane inside `SUNLieCoord Nc`. -/
def fourierLieIndexZero (Nc : ℕ) (hNc : 2 ≤ Nc) : Fin (Nc ^ 2 - 1) :=
  ⟨0, by
    have h4 : 2 * 2 ≤ Nc * Nc := Nat.mul_le_mul hNc hNc
    have hsq : Nc ^ 2 = Nc * Nc := by ring
    rw [hsq]
    omega⟩

/-- Second coordinate of the same real two-plane. -/
def fourierLieIndexOne (Nc : ℕ) (hNc : 2 ≤ Nc) : Fin (Nc ^ 2 - 1) :=
  ⟨1, by
    have h4 : 2 * 2 ≤ Nc * Nc := Nat.mul_le_mul hNc hNc
    have hsq : Nc ^ 2 = Nc * Nc := by ring
    rw [hsq]
    omega⟩

theorem fourierLieIndexZero_ne_one (Nc : ℕ) (hNc : 2 ≤ Nc) :
    fourierLieIndexZero Nc hNc ≠ fourierLieIndexOne Nc hNc := by
  intro h
  have := congrArg Fin.val h
  simp [fourierLieIndexZero, fourierLieIndexOne] at this

/-- Real-linear isometric embedding of `ℂ ≅ ℝ²` into two Lie coordinates. -/
noncomputable def complexLiePlaneEmbedding (Nc : ℕ) (hNc : 2 ≤ Nc) :
    ℂ →ₗ[ℝ] SUNLieCoord Nc where
  toFun z :=
    EuclideanSpace.single (fourierLieIndexZero Nc hNc) z.re +
      EuclideanSpace.single (fourierLieIndexOne Nc hNc) z.im
  map_add' z w := by
    apply PiLp.ext
    intro k
    by_cases h0 : k = fourierLieIndexZero Nc hNc <;>
      by_cases h1 : k = fourierLieIndexOne Nc hNc <;>
      simp [PiLp.add_apply, h0, h1, fourierLieIndexZero_ne_one Nc hNc,
        Ne.symm (fourierLieIndexZero_ne_one Nc hNc)]
  map_smul' c z := by
    have hre : (c • z).re = c * z.re := by
      change ((c : ℂ) * z).re = c * z.re
      exact Complex.re_ofReal_mul c z
    have him : (c • z).im = c * z.im := by
      change ((c : ℂ) * z).im = c * z.im
      exact Complex.im_ofReal_mul c z
    apply PiLp.ext
    intro k
    by_cases h0 : k = fourierLieIndexZero Nc hNc <;>
      by_cases h1 : k = fourierLieIndexOne Nc hNc <;>
      simp [PiLp.add_apply, PiLp.smul_apply, h0, h1,
        fourierLieIndexZero_ne_one Nc hNc,
        Ne.symm (fourierLieIndexZero_ne_one Nc hNc)] <;>
      first | exact hre | exact him

@[simp]
theorem complexLiePlaneEmbedding_apply
    (Nc : ℕ) (hNc : 2 ≤ Nc) (z : ℂ) :
    complexLiePlaneEmbedding Nc hNc z =
      EuclideanSpace.single (fourierLieIndexZero Nc hNc) z.re +
        EuclideanSpace.single (fourierLieIndexOne Nc hNc) z.im := rfl

theorem norm_sq_complexLiePlaneEmbedding
    (Nc : ℕ) (hNc : 2 ≤ Nc) (z : ℂ) :
    ‖complexLiePlaneEmbedding Nc hNc z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [complexLiePlaneEmbedding_apply]
  have hinner :
      inner ℝ
          (EuclideanSpace.single (fourierLieIndexZero Nc hNc) z.re)
          (EuclideanSpace.single (fourierLieIndexOne Nc hNc) z.im) = 0 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases h0 : k = fourierLieIndexZero Nc hNc <;>
      by_cases h1 : k = fourierLieIndexOne Nc hNc <;>
      simp [EuclideanSpace.single_apply, h0, h1,
        fourierLieIndexZero_ne_one Nc hNc,
        Ne.symm (fourierLieIndexZero_ne_one Nc hNc)]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (EuclideanSpace.single (fourierLieIndexZero Nc hNc) z.re)
    (EuclideanSpace.single (fourierLieIndexOne Nc hNc) z.im) hinner
  calc
    ‖EuclideanSpace.single (fourierLieIndexZero Nc hNc) z.re +
        EuclideanSpace.single (fourierLieIndexOne Nc hNc) z.im‖ ^ 2 =
        ‖EuclideanSpace.single (fourierLieIndexZero Nc hNc) z.re‖ ^ 2 +
          ‖EuclideanSpace.single (fourierLieIndexOne Nc hNc) z.im‖ ^ 2 := by
            simpa only [pow_two] using hp
    _ = z.re ^ 2 + z.im ^ 2 := by
      simp only [EuclideanSpace.norm_single, Real.norm_eq_abs, sq_abs]
    _ = ‖z‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply, pow_two]

end YangMills.RG
