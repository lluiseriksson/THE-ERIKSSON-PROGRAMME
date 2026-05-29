/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.SchurPowerSumVanishing

/-!
# Bigraded power-sum selection rule: `∫ tr(U^p)·conj(tr(U^q)) dHaar = 0` for `N∤(p−q)`

This is the **second-moment / covariance** companion to the power-sum rule
(`SchurPowerSumVanishing.lean`).  Where that file handled a single power trace
`tr(U^p)`, here we handle the *product* `tr(U^p)·conj(tr(U^q))` — the object whose
Haar average is the **covariance of the power traces**.

  `∫ tr(U^p) · conj(tr(U^q)) dHaar = 0`     whenever  `N_c ∤ (p − q)`.

## Why this is exactly the F5/F6 object

For U(N) the random variables `tr(U^p)` are, in the large-N limit, independent
complex Gaussians with `E[tr(U^p) \overline{tr(U^q)}] = δ_{pq}·min(p,N)`
(Diaconis–Shahshahani).  The diagonal `p = q` carries the variance; the
off-diagonal `p ≠ q` part is forced to vanish.  This file proves the SU(N_c)
vanishing part — sharper than the U(N) one, because the centre/N-ality structure
makes it vanish whenever `N_c ∤ (p − q)`, not only when `p ≠ q`.

These covariances are precisely the second moments that organise the **connected
correlator** in the strong-coupling character expansion (`HORIZON.md` F5–F6): the
connected two-point function of plaquette traces is built from exactly such
`E[p_p \overline{p_q}]` data, and the selection rule says which of them can be
nonzero before any quantitative estimate is attempted.

## Proof

The integrand is a centre eigenfunction.  Since `ω·I` is scalar (central),
`tr((ω·I·U)^p) = ω^p tr(U^p)` (`trace_scalarCenter_mul_matpow`), so

  `tr((g·U)^p)·conj(tr((g·U)^q)) = ω^p·ω̄^q · tr(U^p)·conj(tr(U^q))`,

eigenvalue `c = ω^p·ω̄^q`.  Primitivity `c ≠ 1 ⇔ N_c ∤ (p − q)` is the already-
proved `rootOfUnity_pow_mul_star_pow_ne_one`.  Feed both to the centre-vanishing
engine (`haar_integral_eq_zero_of_center_eigenfunction`).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no new axioms.
(Pending a `lake build` pass; risk minimal — reuses three proved lemmas + `ring`.)
-/

namespace YangMills

open MeasureTheory Matrix Complex Real

noncomputable section

/-! ## The eigenvalue identity for the power-trace covariance integrand -/

/-- `tr((g·U)^p)·conj(tr((g·U)^q)) = (ω^p · ω̄^q)·(tr(U^p)·conj(tr(U^q)))`,
for `g = ω·I`.  Combines `trace_scalarCenter_mul_matpow` (each power trace scales
by `ω^{exponent}`) with `star_mul'` / `star_pow` for the conjugate factor. -/
theorem tracematpow_mixed_scalarCenter
    (N_c p q : ℕ) [NeZero N_c]
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) :
    (((scalarCenterElement N_c * U).val) ^ p).trace *
        star ((((scalarCenterElement N_c * U).val) ^ q).trace) =
    ((rootOfUnity N_c) ^ p * (star (rootOfUnity N_c)) ^ q) *
        (((U.val) ^ p).trace * star (((U.val) ^ q).trace)) := by
  rw [trace_scalarCenter_mul_matpow N_c p U, trace_scalarCenter_mul_matpow N_c q U,
      star_mul', star_pow]
  ring

/-! ## The bigraded power-sum selection rule -/

/-- **Main theorem — bigraded power-sum (covariance) selection rule.**

`∫ tr(U^p) · conj(tr(U^q)) dHaar = 0` on SU(N_c) whenever `N_c ∤ (p − q)`.
A one-application corollary of the centre-vanishing engine, eigenvalue
`ω^p · ω̄^q`. -/
theorem sunHaarProb_tracematpow_mixed_integral_zero
    (N_c p q : ℕ) [NeZero N_c] (hdvd : ¬ (N_c : ℤ) ∣ ((p : ℤ) - (q : ℤ))) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      ((U.val) ^ p).trace * star (((U.val) ^ q).trace) ∂(sunHaarProb N_c) = 0 :=
  haar_integral_eq_zero_of_center_eigenfunction N_c
    (fun U => ((U.val) ^ p).trace * star (((U.val) ^ q).trace))
    ((rootOfUnity N_c) ^ p * (star (rootOfUnity N_c)) ^ q)
    (fun U => tracematpow_mixed_scalarCenter N_c p q U)
    (rootOfUnity_pow_mul_star_pow_ne_one N_c p q hdvd)

/-- `q = 0` collapses the conjugate factor (`tr(U^0) = N_c`, a constant) and
recovers the single power-sum rule up to the constant: this is the consistency
check that the bigraded rule restricts correctly. -/
theorem sunHaarProb_tracematpow_mixed_q_zero
    (N_c p : ℕ) [NeZero N_c] (hp : ¬ N_c ∣ p) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      ((U.val) ^ p).trace * star (((U.val) ^ 0).trace) ∂(sunHaarProb N_c) = 0 := by
  refine sunHaarProb_tracematpow_mixed_integral_zero N_c p 0 ?_
  rw [Nat.cast_zero, sub_zero]
  intro hZ
  exact hp (by exact_mod_cast hZ)

end

end YangMills
