/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.SchurZeroMean

/-!
# Milestone L2.3+: the Z_N center selection rule for trace moments on SU(N_c)

This file generalises `sunHaarProb_trace_complex_integral_zero` (the `k = 1`
fundamental zero-mean fact, `SchurZeroMean.lean`) to the full family of
**trace-power moments**:

  `∫ (tr U)^k dHaar = 0`     whenever `¬ (N_c ∣ k)`.

Physically this is the **Z_N center symmetry / N-ality selection rule**: the
SU(N_c) Haar measure is invariant under the centre `Z(SU(N_c)) = ⟨ω·I⟩`, and a
monomial `(tr U)^k` carries N-ality `k mod N_c`, so its Haar average must vanish
unless its N-ality is trivial (`N_c ∣ k`). It is the mechanism behind character
orthogonality `∫ χ_ρ dHaar = 0` for non-trivial irreducible `ρ`, and hence sits
on Layer 2 of the Peter–Weyl / Osterwalder–Seiler critical path
(`PETER_WEYL_ROADMAP.md`, `FOUNDATIONS.md §6`).

## Proof strategy

Exactly the centre-element argument of `SchurZeroMean.lean`, raised to a power.
With `ω = exp(2πi/N_c)` and `g = ω·I ∈ SU(N_c)` (`scalarCenterElement`), left
invariance of Haar gives, for `J := ∫ (tr U)^k`,

  `J = ∫ (tr(g·U))^k = ∫ (ω · tr U)^k = ω^k · J`,

so `(1 - ω^k)·J = 0`. The new ingredient is the **primitivity** of `ω`:
`ω^k = 1 ↔ N_c ∣ k`. We only need the forward direction
(`rootOfUnity_pow_ne_one_of_not_dvd`), proved from `Complex.exp_eq_one_iff` in
the same style as `rootOfUnity_ne_one`. When `N_c ∤ k`, `ω^k ≠ 1`, forcing
`J = 0`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no new axioms.

NOTE. This file was written to mirror the *proven* patterns and Mathlib lemmas
already used in `SchurZeroMean.lean`; it has not yet been put through `lake build`
in this environment. It must be compiled and `#print axioms`-checked before being
reported as closed, in keeping with the project's working rules.
-/

namespace YangMills

open MeasureTheory Matrix Complex Real

noncomputable section

/-! ## Primitivity of the root of unity -/

/-- **Primitivity (the direction we need).** For `N_c ≥ 1`, if `N_c ∤ k` then
`ω^k ≠ 1`, where `ω = exp(2πi/N_c)`.  Generalises `rootOfUnity_ne_one`
(which is the `k = 1` case). -/
theorem rootOfUnity_pow_ne_one_of_not_dvd
    (N_c k : ℕ) [NeZero N_c] (hk : ¬ N_c ∣ k) :
    rootOfUnity N_c ^ k ≠ 1 := by
  intro hEq
  -- ω^k = exp(k · (2πi/N_c)); turn the power into a single exponential.
  unfold rootOfUnity at hEq
  rw [← Complex.exp_nat_mul] at hEq
  rw [Complex.exp_eq_one_iff] at hEq
  obtain ⟨n, hn⟩ := hEq
  -- hn : (k : ℂ) * (2π·I / N_c) = (n : ℂ) * (2π·I)
  have h2piI_ne : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hNne : (N_c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N_c)
  -- Rewrite the LHS so that the common factor `2π·I` is on the right, then cancel.
  have hLHS : (k : ℂ) * (2 * (π : ℂ) * Complex.I / (N_c : ℂ)) =
      ((k : ℂ) / (N_c : ℂ)) * (2 * (π : ℂ) * Complex.I) := by ring
  rw [hLHS] at hn
  have hcancel : (k : ℂ) / (N_c : ℂ) = (n : ℂ) :=
    mul_right_cancel₀ h2piI_ne hn
  have hkeq : (k : ℂ) = (n : ℂ) * (N_c : ℂ) := by
    rw [div_eq_iff hNne] at hcancel
    exact hcancel
  -- Descend the equality to ℤ and read off divisibility.
  have hkZ : (k : ℤ) = n * (N_c : ℤ) := by exact_mod_cast hkeq
  have hdvdZ : (N_c : ℤ) ∣ (k : ℤ) := ⟨n, by rw [hkZ]; ring⟩
  have hdvd : N_c ∣ k := by exact_mod_cast hdvdZ
  exact hk hdvd

/-! ## Integrability of trace powers -/

/-- `(tr U)^k` is integrable against `sunHaarProb N_c` (continuous on a compact
group). -/
theorem tracePow_integrable (N_c k : ℕ) [NeZero N_c] :
    Integrable
      (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => (U.val.trace) ^ k)
      (sunHaarProb N_c) :=
  ((continuous_trace_sub N_c).pow k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-! ## The Z_N center selection rule -/

/-- `(tr((ω·I)·U))^k = ω^k · (tr U)^k`. -/
theorem trace_scalarCenter_mul_pow
    (N_c k : ℕ) [NeZero N_c]
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) :
    ((scalarCenterElement N_c * U).val.trace) ^ k =
    (rootOfUnity N_c) ^ k * (U.val.trace) ^ k := by
  rw [trace_scalarCenter_mul N_c U, mul_pow]

/-- **Main theorem — Z_N center selection rule (complex form).**

`∫ (tr U)^k dHaar = 0` on SU(N_c) whenever `N_c ∤ k`.  The `k = 1`, `N_c ≥ 2`
case recovers `sunHaarProb_trace_complex_integral_zero`. -/
theorem sunHaarProb_trace_pow_complex_integral_zero
    (N_c k : ℕ) [NeZero N_c] (hk : ¬ N_c ∣ k) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      (U.val.trace) ^ k ∂(sunHaarProb N_c) = 0 := by
  set J : ℂ := ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      (U.val.trace) ^ k ∂(sunHaarProb N_c) with hJdef
  -- Left invariance against the centre element ω·I.
  have hinv : J = ∫ U, ((scalarCenterElement N_c * U).val.trace) ^ k
                      ∂(sunHaarProb N_c) := by
    rw [hJdef]
    symm
    exact MeasureTheory.integral_mul_left_eq_self
          (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => (U.val.trace) ^ k)
          (scalarCenterElement N_c)
  have heq : (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
               ((scalarCenterElement N_c * U).val.trace) ^ k) =
             (fun U => (rootOfUnity N_c) ^ k * (U.val.trace) ^ k) := by
    funext U; exact trace_scalarCenter_mul_pow N_c k U
  have hmul : (∫ U, ((scalarCenterElement N_c * U).val.trace) ^ k
                      ∂(sunHaarProb N_c)) =
               (rootOfUnity N_c) ^ k * J := by
    calc ∫ U, ((scalarCenterElement N_c * U).val.trace) ^ k ∂(sunHaarProb N_c)
        = ∫ U, (rootOfUnity N_c) ^ k * (U.val.trace) ^ k ∂(sunHaarProb N_c) := by
          rw [heq]
      _ = (rootOfUnity N_c) ^ k * ∫ U, (U.val.trace) ^ k ∂(sunHaarProb N_c) :=
          MeasureTheory.integral_const_mul _ _
      _ = (rootOfUnity N_c) ^ k * J := by rw [← hJdef]
  rw [hmul] at hinv
  have hfactor : (1 - (rootOfUnity N_c) ^ k) * J = 0 := by linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exfalso
    have hω : (rootOfUnity N_c) ^ k = 1 := (sub_eq_zero.mp h1).symm
    exact rootOfUnity_pow_ne_one_of_not_dvd N_c k hk hω
  · exact h2

/-- The `k = 1` corollary is the original fundamental zero-mean fact; this
re-derivation checks the generalisation is faithful (`N_c ≥ 2 ↔ ¬ N_c ∣ 1`). -/
theorem sunHaarProb_trace_complex_integral_zero'
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      U.val.trace ∂(sunHaarProb N_c) = 0 := by
  have hk : ¬ N_c ∣ 1 := by
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h := sunHaarProb_trace_pow_complex_integral_zero N_c 1 hk
  simpa using h

end

end YangMills
