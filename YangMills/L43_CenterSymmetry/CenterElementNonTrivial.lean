/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import YangMills.L43_CenterSymmetry.CenterGroup
import YangMills.L43_CenterSymmetry.DeconfinementCriterion

/-!
# `L43_CenterSymmetry.CenterElementNonTrivial`: `centerElement N 1 ≠ 1` for `N ≥ 2`

This module addresses **P0 open question §1.3** from `OPEN_QUESTIONS.md`:
the L43 hypothesis-conditioning from Phase 437 left
`centerElement N 1 ≠ 1` (i.e., the primitive `N`-th root of unity is
not 1 for `N ≥ 2`) as an explicit input. This file resolves that
input by proving the fact from `Complex.exp_eq_one_iff`.

## Mathematical content

The primitive `N`-th root of unity is

  `ω_N = exp(2πi/N)`.

For `N ≥ 2`, we have `2πi/N ≠ k · 2πi` for any integer `k` (since
that would require `1/N = k`, but `N ≥ 2` is a natural number).
Hence by `Complex.exp_eq_one_iff`, `ω_N ≠ 1`.

## Status

This file closes the L43 hypothesis-conditioning gap, allowing
`polyakov_invariant_implies_zero` to be applied with `centerElement N 1`
as the explicit non-trivial center element for any `N ≥ 2`.

**Status (2026-04-25 Phase 458)**: produced in workspace, not yet
built with `lake build`. Proof uses `Complex.exp_eq_one_iff` (Mathlib).
-/

namespace L43_CenterSymmetry

open Complex

/-! ## §1. The primitive root inequality -/

/-- **`primitiveRoot N ≠ 1` for `N ≥ 2`**.

    Equivalently, `exp(2πi/N) ≠ 1` for `N ≥ 2`.

    Proof via `Complex.exp_eq_one_iff`: `exp(z) = 1 ↔ ∃ n : ℤ, z = n · 2πi`.
    For `z = 2πi/N` with `N ≥ 2`, this would require `1/N = n` for
    some integer `n`, which is impossible (`1/N ∈ (0, 1/2]` is not
    a non-zero integer; `N ≥ 2` rules out `n = 0` since that would
    give `1/N = 0`, contradicting `N` finite). -/
theorem primitiveRoot_ne_one {N : ℕ} (hN : 2 ≤ N) :
    primitiveRoot N ≠ 1 := by
  unfold primitiveRoot
  intro h_eq
  -- Apply Complex.exp_eq_one_iff: ∃ n : ℤ, 2πi/N = n · 2πi.
  rw [Complex.exp_eq_one_iff] at h_eq
  obtain ⟨n, hn⟩ := h_eq
  -- hn : 2 * π * I / (N : ℂ) = n * (2 * π * I)
  -- Divide both sides by 2πi (which is non-zero).
  have h_2πi_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have h_pi_ne : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have h_I_ne : Complex.I ≠ 0 := Complex.I_ne_zero
    have h_2_ne : (2 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero h_2_ne h_pi_ne) h_I_ne
  have h_N_pos : (0 : ℂ) < (N : ℂ) := by
    have : 0 < N := by linarith
    exact_mod_cast this
  have h_N_ne : (N : ℂ) ≠ 0 := ne_of_gt h_N_pos
  -- From 2πi/N = n · 2πi, divide both sides by 2πi to get 1/N = n.
  -- Equivalent: 2πi = N · n · 2πi, then divide by 2πi: 1 = N · n.
  have h_div : (1 : ℂ) = N * n := by
    have h_rearrange : (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) * (N : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I := by
      field_simp
    have h_left : (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) * (N : ℂ) =
        ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (N : ℂ) := by
      rw [hn]
    rw [h_rearrange] at h_left
    -- 2πi = n · 2πi · N = (n · N) · 2πi
    have h_simp : ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (N : ℂ) =
        ((n : ℂ) * (N : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h_simp] at h_left
    -- Cancel the 2πi on both sides.
    have h_one_eq : (1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
        ((n : ℂ) * (N : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [one_mul]; exact h_left
    have h_cancel : (1 : ℂ) = (n : ℂ) * (N : ℂ) :=
      mul_right_cancel₀ h_2πi_ne h_one_eq
    -- (n : ℂ) * (N : ℂ) = (N : ℂ) * (n : ℂ).
    rw [mul_comm] at h_cancel
    exact h_cancel
  -- Now h_div : 1 = N · n in ℂ. Cast back to integers.
  -- N ≥ 2 (in ℕ), n : ℤ. We need N · n = 1 in ℤ, then derive contradiction.
  have h_int_eq : (N : ℤ) * n = 1 := by
    have h_int_cast : ((N : ℤ) * n : ℂ) = ((1 : ℤ) : ℂ) := by
      push_cast
      linear_combination -h_div
    exact_mod_cast h_int_cast
  -- N ≥ 2 ⟹ |N · n| ≥ 2 · |n|. For 1 = N · n, |N · n| = 1 < 2.
  -- So |n| · 2 ≤ 1, impossible for integer |n| ≥ 1; and n = 0 gives N · 0 = 0 ≠ 1.
  -- Hence contradiction.
  have h_N_ge_2 : (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have h_N_pos_int : 0 < (N : ℤ) := by linarith
  -- N · n = 1 with N ≥ 2 ⟹ contradiction by integer divisibility.
  -- N · n = 1 ⟹ N ∣ 1, so N = ±1, but N ≥ 2.
  have h_dvd : (N : ℤ) ∣ 1 := ⟨n, h_int_eq.symm⟩
  have h_N_le_1 : (N : ℤ) ≤ 1 := Int.le_of_dvd Int.one_pos h_dvd
  linarith

#print axioms primitiveRoot_ne_one

/-! ## §2. Specialisation: `centerElement N 1 ≠ 1` for `N ≥ 2` -/

/-- **`centerElement N 1 ≠ 1` for `N ≥ 2`**: the first non-trivial
    `Z_N` center element is not the identity. -/
theorem centerElement_one_ne_one {N : ℕ} (hN : 2 ≤ N) :
    centerElement N 1 ≠ 1 := by
  unfold centerElement
  rw [pow_one]
  exact primitiveRoot_ne_one hN

#print axioms centerElement_one_ne_one

/-! ## §3. Strengthened L43 confinement criterion -/

/-- **Strengthened criterion**: combines `polyakov_invariant_implies_zero`
    (Phase 437) with `centerElement_one_ne_one` (this Phase 458) to
    give the **fully unconditional** `IsConfined ⟺ centerInvariant`
    biconditional for `N ≥ 2`.

    This closes the hypothesis-conditioning gap from Phase 437. -/
theorem isConfined_iff_centerElement_one_invariant
    {N : ℕ} (hN : 2 ≤ N) (poly : PolyakovExpectation N) :
    IsConfined poly ↔ centerElement N 1 * poly.P = poly.P := by
  apply isConfined_iff_centerInvariant
  exact centerElement_one_ne_one hN

#print axioms isConfined_iff_centerElement_one_invariant

end L43_CenterSymmetry
