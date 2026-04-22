/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.ClayCore.SchurZeroMean

/-!
# Trace-power vanishing on SU(N_c)

Generalizes `sunHaarProb_trace_complex_integral_zero` (the degree-1
case) to all natural powers:

  `sunHaarProb_trace_pow_integral_zero`:
  `∫ (tr U)^k dHaar = 0`    on SU(N_c), for every `k : ℕ` with `¬ N_c ∣ k`.

## Proof

Same central-element technique as in `SchurZeroMean.lean` with `ω^k` in
place of `ω`.  Take `Ω := ω·I ∈ SU(N_c)` where `ω = exp(2πi/N_c)`.  By
left-invariance of Haar,
`J := ∫ (tr U)^k = ∫ (tr(Ω·U))^k = ∫ (ω·tr U)^k = ω^k · J`.
Hence `(1 - ω^k)·J = 0`; when `N_c ∤ k` we have `ω^k ≠ 1` (ω is a
primitive `N_c`-th root of unity), so `J = 0`.

## Representation-theoretic meaning

The power `(tr U)^k` decomposes into characters of the irreducible
summands of `(ℂ^{N_c})^⊗k` (Schur functors on Young diagrams with `k`
boxes).  When `N_c ∤ k`, none of these summands is the trivial
representation, so by character orthogonality with the trivial rep the
integral vanishes.  When `N_c ∣ k` the decomposition contains
`det^{k/N_c} = triv`, and the integral is generically non-zero.

## Corollaries

- `k = 1`:  recovers `sunHaarProb_trace_complex_integral_zero` (for `N_c ≥ 2`).
- `k = 2`:  `∫ (tr U)² = 0` for `N_c ≥ 3`.
- `k = 3`:  `∫ (tr U)³ = 0` for `N_c ≥ 4`.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry.  No new axioms.
-/

namespace YangMills

open MeasureTheory Matrix Complex Real

noncomputable section

/-! ## ω^k ≠ 1 when N_c ∤ k -/

/-- **Primitive-root-of-unity condition.**  The `k`-th power of
`ω = exp(2πi/N_c)` differs from 1 whenever `N_c ∤ k`.  Generalizes
`rootOfUnity_ne_one` (the `k = 1` case, which needs `N_c ≥ 2`). -/
theorem rootOfUnity_pow_ne_one (N_c : ℕ) [NeZero N_c] {k : ℕ}
    (hkN : ¬ N_c ∣ k) : rootOfUnity N_c ^ k ≠ 1 := by
  intro hEq
  unfold rootOfUnity at hEq
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at hEq
  obtain ⟨n, hn⟩ := hEq
  -- hn : (↑k : ℂ) * (2 * ↑π * I / ↑N_c) = ↑n * (2 * ↑π * I)
  have h2piI_ne : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hNne : (N_c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N_c)
  -- Clear the denominator in hn to get (↑k : ℂ) * 2πI = (↑n * ↑N_c) * 2πI
  have hfield : (k : ℂ) * (2 * (π : ℂ) * Complex.I) =
                ((n : ℂ) * (N_c : ℂ)) * (2 * (π : ℂ) * Complex.I) := by
    calc (k : ℂ) * (2 * (π : ℂ) * Complex.I)
        = (k : ℂ) * (2 * (π : ℂ) * Complex.I / (N_c : ℂ) * (N_c : ℂ)) := by
          rw [div_mul_cancel₀ _ hNne]
      _ = ((k : ℂ) * (2 * (π : ℂ) * Complex.I / (N_c : ℂ))) * (N_c : ℂ) := by ring
      _ = ((n : ℂ) * (2 * (π : ℂ) * Complex.I)) * (N_c : ℂ) := by rw [hn]
      _ = ((n : ℂ) * (N_c : ℂ)) * (2 * (π : ℂ) * Complex.I) := by ring
  have hk_eq : (k : ℂ) = (n : ℂ) * (N_c : ℂ) :=
    mul_right_cancel₀ h2piI_ne hfield
  -- Transport to ℝ then to ℤ to extract divisibility
  have hkR : (k : ℝ) = (n : ℝ) * (N_c : ℝ) := by
    have := congr_arg Complex.re hk_eq
    push_cast at this
    simpa using this
  have hk_int : (k : ℤ) = n * (N_c : ℤ) := by exact_mod_cast hkR
  have hk_dvd_int : (N_c : ℤ) ∣ (k : ℤ) := ⟨n, by rw [hk_int]; ring⟩
  exact hkN (by exact_mod_cast hk_dvd_int)

/-! ## Trace-power under scalar-center multiplication -/

/-- `tr((ω·I) · U)^k = ω^k · (tr U)^k`.  Immediate from
`trace_scalarCenter_mul` (degree-1 case) via `mul_pow`. -/
theorem trace_scalarCenter_mul_pow (N_c : ℕ) [NeZero N_c]
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (k : ℕ) :
    ((scalarCenterElement N_c * U).val).trace ^ k =
    rootOfUnity N_c ^ k * U.val.trace ^ k := by
  rw [trace_scalarCenter_mul, mul_pow]

/-! ## Main theorem -/

/-- **Main theorem — trace-power vanishing.**  For any `k : ℕ` with
`¬ N_c ∣ k`, the Haar integral of `(tr U)^k` over SU(N_c) vanishes.

Specializes to `sunHaarProb_trace_complex_integral_zero` at `k = 1`
(which requires `N_c ≥ 2`, the case `¬ N_c ∣ 1`). -/
theorem sunHaarProb_trace_pow_integral_zero (N_c : ℕ) [NeZero N_c]
    {k : ℕ} (hkN : ¬ N_c ∣ k) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      U.val.trace ^ k ∂(sunHaarProb N_c) = 0 := by
  set J : ℂ := ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      U.val.trace ^ k ∂(sunHaarProb N_c) with hJdef
  -- Step 1: Haar left-invariance with Ω = ω·I
  have hinv : J = ∫ U, ((scalarCenterElement N_c * U).val).trace ^ k
                      ∂(sunHaarProb N_c) := by
    rw [hJdef]; symm
    exact MeasureTheory.integral_mul_left_eq_self
          (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => U.val.trace ^ k)
          (scalarCenterElement N_c)
  -- Step 2: pointwise rewrite of the integrand
  have heq : (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
               ((scalarCenterElement N_c * U).val).trace ^ k) =
             (fun U => rootOfUnity N_c ^ k * U.val.trace ^ k) := by
    funext U; exact trace_scalarCenter_mul_pow N_c U k
  -- Step 3: pull ω^k out of the integral
  have hmul : (∫ U, ((scalarCenterElement N_c * U).val).trace ^ k
                      ∂(sunHaarProb N_c)) =
              rootOfUnity N_c ^ k * J := by
    calc ∫ U, ((scalarCenterElement N_c * U).val).trace ^ k ∂(sunHaarProb N_c)
        = ∫ U, rootOfUnity N_c ^ k * U.val.trace ^ k ∂(sunHaarProb N_c) := by
          rw [heq]
      _ = rootOfUnity N_c ^ k * ∫ U, U.val.trace ^ k ∂(sunHaarProb N_c) :=
          MeasureTheory.integral_const_mul _ _
      _ = rootOfUnity N_c ^ k * J := by rw [← hJdef]
  -- Step 4: (1 - ω^k)·J = 0, and ω^k ≠ 1 forces J = 0
  rw [hmul] at hinv
  have hfactor : (1 - rootOfUnity N_c ^ k) * J = 0 := by linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exact absurd (sub_eq_zero.mp h1).symm (rootOfUnity_pow_ne_one N_c hkN)
  · exact h2

/-! ## Concrete low-degree corollaries -/

/-- `∫ (tr U)² dHaar = 0` on SU(N_c) for every `N_c ≥ 3`. -/
theorem sunHaarProb_trace_sq_integral_zero (N_c : ℕ) [NeZero N_c]
    (hN : 3 ≤ N_c) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      U.val.trace ^ 2 ∂(sunHaarProb N_c) = 0 := by
  refine sunHaarProb_trace_pow_integral_zero N_c ?_
  intro h
  have : N_c ≤ 2 := Nat.le_of_dvd (by norm_num) h
  omega

/-- `∫ (tr U)³ dHaar = 0` on SU(N_c) for every `N_c ≥ 4`. -/
theorem sunHaarProb_trace_cube_integral_zero (N_c : ℕ) [NeZero N_c]
    (hN : 4 ≤ N_c) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      U.val.trace ^ 3 ∂(sunHaarProb N_c) = 0 := by
  refine sunHaarProb_trace_pow_integral_zero N_c ?_
  intro h
  have : N_c ≤ 3 := Nat.le_of_dvd (by norm_num) h
  omega

/-! ## Non-triviality witness -/

/-- The integrand `(tr U)^k` is non-trivial: at `1 ∈ SU(N_c)` it equals `N_c^k`. -/
theorem sunHaarProb_trace_pow_at_one (N_c : ℕ) [NeZero N_c] (k : ℕ) :
    (((1 : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)).val.trace) ^ k : ℂ)
      = (N_c : ℂ) ^ k := by
  have hval : (1 : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)).val =
      (1 : Matrix (Fin N_c) (Fin N_c) ℂ) := rfl
  rw [hval, Matrix.trace_one, Fintype.card_fin]

end

end YangMills
