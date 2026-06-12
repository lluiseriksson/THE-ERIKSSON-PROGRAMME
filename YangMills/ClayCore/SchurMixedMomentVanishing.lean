/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.SchurMomentVanishing

/-!
# Milestone L2.3++: the full Z_N N-ality grading of trace moments on SU(N_c)

This file is the *complete* form of the centre-symmetry selection rule.  Where
`SchurZeroMean.lean` proves `∫ tr U = 0` (N-ality 1) and `SchurMomentVanishing.lean`
proves `∫ (tr U)^k = 0` for `N_c ∤ k` (N-ality `k`), this file proves the full
**mixed-moment** statement that governs *every* polynomial in `tr U` and its
conjugate:

  `∫ (tr U)^a · conj(tr U)^b dHaar = 0`     whenever  `¬ (N_c ∣ (a − b))`.

## Why this is the "right" theorem

A monomial `(tr U)^a · conj(tr U)^b` carries **N-ality** `a − b (mod N_c)` under
the centre `Z(SU(N_c)) = ⟨ω·I⟩`, `ω = exp(2πi/N_c)`: replacing `U ↦ (ω·I)·U`
multiplies it by `ω^a · ω̄^b = ω^{a−b}`.  Haar invariance then forces the average
to vanish unless the N-ality is trivial, i.e. unless `N_c ∣ (a − b)`.

This is exactly the algebraic content behind **confinement / the area law**: only
N-ality-zero (centre-blind) Wilson observables can have a non-vanishing Haar
expectation, and at strong coupling the leading non-vanishing contribution to a
Wilson loop is the one tiling its interior with plaquettes — the perimeter of
admissible configurations is what produces the `exp(−m·dist)` decay targeted by
`ConnectedCorrDecay` (`FOUNDATIONS.md §5`, `PETER_WEYL_ROADMAP.md`).  In
representation-theoretic terms it is the diagonal `(a,b)` shadow of full Schur
orthogonality `∫ ρ_{ij} \overline{σ_{kl}} dHaar = δ_{ρσ}δ_{ik}δ_{jl}/dim ρ` (F4).

## Specialisations (faithfulness checks, proved at the bottom)

* `b = 0`            ↦ `∫ (tr U)^a = 0` for `N_c ∤ a`   (recovers `SchurMomentVanishing`).
* `a = 1, b = 0`     ↦ `∫ tr U = 0` for `N_c ≥ 2`        (recovers F0).
* `a = b`            ↦ N-ality `0`, *not* covered — correctly, since e.g.
                       `∫ |tr U|² dHaar = 1 ≠ 0`.  The theorem never claims a
                       false vanishing.

## Proof strategy

Identical centre-element argument, now tracking the conjugate factor.  With
`g = ω·I` (`scalarCenterElement`) and `J := ∫ (tr U)^a · conj(tr U)^b`,
left invariance of Haar gives

  `J = ∫ (tr(gU))^a · conj(tr(gU))^b = ∫ ω^a ω̄^b · (tr U)^a conj(tr U)^b
     = (ω^a · ω̄^b) · J`,

so `(1 − ω^a ω̄^b)·J = 0`.  The new ingredient is the **primitivity of the
combined phase**: `ω^a · ω̄^b = exp((a−b)·2πi/N_c) = 1 ↔ N_c ∣ (a − b)` over ℤ.
We only need the forward direction (`rootOfUnity_pow_mul_star_pow_ne_one`),
proved from `Complex.exp_eq_one_iff` in the same style as
`rootOfUnity_pow_ne_one_of_not_dvd`, now over the *integer* difference `a − b`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no new axioms.

NOTE. Written to mirror the *proven* patterns and Mathlib lemmas of
`SchurZeroMean.lean` / `SchurMomentVanishing.lean`; not yet put through
`lake build` in this environment.  The integer-cast steps in
`rootOfUnity_pow_mul_star_pow_ne_one` are the residual compile risk and must be
`#print axioms`-checked before this is reported closed (project working rules).
-/

namespace YangMills

open MeasureTheory Matrix Complex Real

noncomputable section

/-! ## The conjugate of the root of unity as an explicit exponential -/

/-- `conj(ω) = exp(−2πi/N_c)`.  This is the `have hstar_eq` block of
`star_rootOfUnity_mul_self` promoted to a reusable top-level lemma. -/
theorem star_rootOfUnity_eq (N_c : ℕ) [NeZero N_c] :
    star (rootOfUnity N_c) =
      Complex.exp (-(2 * (π : ℂ) * Complex.I / (N_c : ℂ))) := by
  show (starRingEnd ℂ) _ = _
  unfold rootOfUnity
  rw [← Complex.exp_conj]
  congr 1
  rw [show (2 * (π : ℂ) * Complex.I / (N_c : ℂ)) =
        ((2 * π / N_c : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-! ## Primitivity of the combined phase `ω^a · ω̄^b` -/

/-- **Primitivity (the direction we need).** For `N_c ≥ 1`, if `N_c ∤ (a − b)`
(over ℤ) then `ω^a · ω̄^b ≠ 1`.  Generalises `rootOfUnity_pow_ne_one_of_not_dvd`
(the `b = 0` case) and `rootOfUnity_ne_one` (the `a = 1, b = 0` case). -/
theorem rootOfUnity_pow_mul_star_pow_ne_one
    (N_c a b : ℕ) [NeZero N_c] (hdvd : ¬ (N_c : ℤ) ∣ ((a : ℤ) - (b : ℤ))) :
    (rootOfUnity N_c) ^ a * (star (rootOfUnity N_c)) ^ b ≠ 1 := by
  intro hEq
  have hNne : (N_c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N_c)
  have h2piI_ne : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  -- Express both powers as single exponentials.
  have h1 : (rootOfUnity N_c) ^ a =
      Complex.exp ((a : ℂ) * (2 * (π : ℂ) * Complex.I / (N_c : ℂ))) := by
    unfold rootOfUnity; rw [← Complex.exp_nat_mul]
  have h2 : (star (rootOfUnity N_c)) ^ b =
      Complex.exp ((b : ℂ) * (-(2 * (π : ℂ) * Complex.I / (N_c : ℂ)))) := by
    rw [star_rootOfUnity_eq, ← Complex.exp_nat_mul]
  rw [h1, h2, ← Complex.exp_add, Complex.exp_eq_one_iff] at hEq
  obtain ⟨n, hn⟩ := hEq
  -- hn : a·z + b·(−z) = n·(2πi),  z = 2πi/N_c.  Collect into ((a−b)/N_c)·(2πi).
  have hLHS : (a : ℂ) * (2 * (π : ℂ) * Complex.I / (N_c : ℂ)) +
      (b : ℂ) * (-(2 * (π : ℂ) * Complex.I / (N_c : ℂ))) =
      ((a : ℂ) - (b : ℂ)) / (N_c : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    field_simp
    ring
  rw [hLHS] at hn
  have hcancel : ((a : ℂ) - (b : ℂ)) / (N_c : ℂ) = (n : ℂ) :=
    mul_right_cancel₀ h2piI_ne hn
  have hdiff : (a : ℂ) - (b : ℂ) = (n : ℂ) * (N_c : ℂ) := by
    rw [div_eq_iff hNne] at hcancel; exact hcancel
  -- Descend to ℤ and read off divisibility.
  have hdiffZ : (a : ℤ) - (b : ℤ) = n * (N_c : ℤ) := by exact_mod_cast hdiff
  have hdvdZ : (N_c : ℤ) ∣ ((a : ℤ) - (b : ℤ)) := ⟨n, by rw [hdiffZ]; ring⟩
  exact hdvd hdvdZ

/-! ## Integrability of the mixed moment -/

/-- `(tr U)^a · conj(tr U)^b` is integrable against `sunHaarProb N_c`
(continuous on a compact group). -/
theorem traceMixedPow_integrable (N_c a b : ℕ) [NeZero N_c] :
    Integrable
      (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
        (U.val.trace) ^ a * (star (U.val.trace)) ^ b)
      (sunHaarProb N_c) :=
  ((((continuous_trace_sub N_c).pow a).mul
      ((continuous_star.comp (continuous_trace_sub N_c)).pow b))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-! ## The conjugation behaviour under the centre element -/

/-- `(tr(gU))^a · conj(tr(gU))^b = (ω^a · ω̄^b) · ((tr U)^a · conj(tr U)^b)`,
for `g = ω·I`.  Uses `star_mul'` (ℂ commutative) and `mul_pow`. -/
theorem trace_scalarCenter_mul_mixedPow
    (N_c a b : ℕ) [NeZero N_c]
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) :
    ((scalarCenterElement N_c * U).val.trace) ^ a *
        (star ((scalarCenterElement N_c * U).val.trace)) ^ b =
    ((rootOfUnity N_c) ^ a * (star (rootOfUnity N_c)) ^ b) *
        ((U.val.trace) ^ a * (star (U.val.trace)) ^ b) := by
  rw [trace_scalarCenter_mul N_c U, star_mul', mul_pow, mul_pow]
  ring

/-! ## The full Z_N selection rule -/

/-- **Main theorem — full Z_N N-ality grading.**

`∫ (tr U)^a · conj(tr U)^b dHaar = 0` on SU(N_c) whenever `N_c ∤ (a − b)`. -/
theorem sunHaarProb_trace_mixedPow_integral_zero
    (N_c a b : ℕ) [NeZero N_c] (hdvd : ¬ (N_c : ℤ) ∣ ((a : ℤ) - (b : ℤ))) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      (U.val.trace) ^ a * (star (U.val.trace)) ^ b ∂(sunHaarProb N_c) = 0 := by
  set J : ℂ := ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      (U.val.trace) ^ a * (star (U.val.trace)) ^ b ∂(sunHaarProb N_c) with hJdef
  -- Left invariance against the centre element ω·I.
  have hinv : J = ∫ U, ((scalarCenterElement N_c * U).val.trace) ^ a *
                      (star ((scalarCenterElement N_c * U).val.trace)) ^ b
                      ∂(sunHaarProb N_c) := by
    rw [hJdef]
    symm
    exact MeasureTheory.integral_mul_left_eq_self
          (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
            (U.val.trace) ^ a * (star (U.val.trace)) ^ b)
          (scalarCenterElement N_c)
  have heq : (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
               ((scalarCenterElement N_c * U).val.trace) ^ a *
               (star ((scalarCenterElement N_c * U).val.trace)) ^ b) =
             (fun U => ((rootOfUnity N_c) ^ a * (star (rootOfUnity N_c)) ^ b) *
               ((U.val.trace) ^ a * (star (U.val.trace)) ^ b)) := by
    funext U; exact trace_scalarCenter_mul_mixedPow N_c a b U
  have hmul : (∫ U, ((scalarCenterElement N_c * U).val.trace) ^ a *
                      (star ((scalarCenterElement N_c * U).val.trace)) ^ b
                      ∂(sunHaarProb N_c)) =
               ((rootOfUnity N_c) ^ a * (star (rootOfUnity N_c)) ^ b) * J := by
    calc ∫ U, ((scalarCenterElement N_c * U).val.trace) ^ a *
              (star ((scalarCenterElement N_c * U).val.trace)) ^ b ∂(sunHaarProb N_c)
        = ∫ U, ((rootOfUnity N_c) ^ a * (star (rootOfUnity N_c)) ^ b) *
              ((U.val.trace) ^ a * (star (U.val.trace)) ^ b) ∂(sunHaarProb N_c) := by
          rw [heq]
      _ = ((rootOfUnity N_c) ^ a * (star (rootOfUnity N_c)) ^ b) *
              ∫ U, (U.val.trace) ^ a * (star (U.val.trace)) ^ b ∂(sunHaarProb N_c) :=
          MeasureTheory.integral_const_mul _ _
      _ = ((rootOfUnity N_c) ^ a * (star (rootOfUnity N_c)) ^ b) * J := by rw [← hJdef]
  rw [hmul] at hinv
  have hfactor : (1 - (rootOfUnity N_c) ^ a * (star (rootOfUnity N_c)) ^ b) * J = 0 := by
    linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exfalso
    have hω : (rootOfUnity N_c) ^ a * (star (rootOfUnity N_c)) ^ b = 1 :=
      (sub_eq_zero.mp h1).symm
    exact rootOfUnity_pow_mul_star_pow_ne_one N_c a b hdvd hω
  · exact h2

/-! ## Faithfulness corollaries -/

/-- `b = 0`: recovers the pure-power Z_N rule `∫ (tr U)^a = 0` for `N_c ∤ a`. -/
theorem sunHaarProb_trace_pow_integral_zero'
    (N_c a : ℕ) [NeZero N_c] (ha : ¬ N_c ∣ a) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      (U.val.trace) ^ a * (star (U.val.trace)) ^ 0 ∂(sunHaarProb N_c) = 0 := by
  refine sunHaarProb_trace_mixedPow_integral_zero N_c a 0 ?_
  -- ¬ N_c ∣ a (over ℕ)  ⇒  ¬ (N_c : ℤ) ∣ (a − 0) (over ℤ)
  simpa using (by
    intro hZ
    have : N_c ∣ a := by
      have hZ' : (N_c : ℤ) ∣ (a : ℤ) := by simpa using hZ
      exact_mod_cast hZ'
    exact ha this)

/-- The "conjugate" pure-power version `∫ conj(tr U)^b = 0` for `N_c ∤ b`,
obtained by symmetry `a = 0`. -/
theorem sunHaarProb_trace_starPow_integral_zero
    (N_c b : ℕ) [NeZero N_c] (hb : ¬ N_c ∣ b) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      (U.val.trace) ^ 0 * (star (U.val.trace)) ^ b ∂(sunHaarProb N_c) = 0 := by
  refine sunHaarProb_trace_mixedPow_integral_zero N_c 0 b ?_
  -- ¬ N_c ∣ b  ⇒  ¬ (N_c : ℤ) ∣ (0 − b)
  intro hZ
  have hZ' : (N_c : ℤ) ∣ (b : ℤ) := by
    have : (N_c : ℤ) ∣ -((b : ℤ)) := by simpa using hZ
    simpa using (dvd_neg.mp this)
  exact hb (by exact_mod_cast hZ')

end

end YangMills
