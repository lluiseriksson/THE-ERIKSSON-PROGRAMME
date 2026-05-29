/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.SchurEntryNAlitySelection

/-!
# The centre-eigenfunction vanishing principle — the engine behind every Z_N rule

Four separate results in this development —

* `∫ tr U = 0`                                   (`SchurZeroMean`, F0),
* `∫ (tr U)^k = 0` for `N∤k`                     (`SchurMomentVanishing`),
* `∫ (tr U)^a conj(tr U)^b = 0` for `N∤(a−b)`    (`SchurMixedMomentVanishing`),
* `∫ (∏U_{ij})(∏conj U_{kl}) = 0` for `N∤(n−m)`  (`SchurEntryNAlitySelection`)

— are *the same theorem* applied to different integrands.  Each integrand `f` is
an **eigenfunction of the centre element** `g = ω·I ∈ SU(N_c)`: it satisfies
`f(g·U) = c · f(U)` for a scalar `c` (respectively `ω`, `ω^k`, `ω^a ω̄^b`,
`ω^n ω̄^m`), and each proof then runs the identical three lines
(`J = c·J ⇒ (1−c)J = 0 ⇒ J = 0` when `c ≠ 1`).

This file extracts that common engine as a single reusable lemma and re-derives
all four results as two-line corollaries.  The payoff for a future prover: to show
that *any* new Haar integral vanishes by centre symmetry — an open Wilson line, a
higher matrix-coefficient monomial, a new class function — you no longer reprove
the averaging argument; you only

  1. exhibit the eigenvalue identity `f(g·U) = c·f(U)`, and
  2. show `c ≠ 1` (usually a root-of-unity primitivity fact),

and feed them to `haar_integral_eq_zero_of_center_eigenfunction`.

The lemma needs **no integrability or continuity hypothesis**: it rests only on
left-invariance of `sunHaarProb` (`MeasureTheory.integral_mul_left_eq_self`) and
`integral_const_mul`, both unconditional.  That makes it maximally reusable.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no new axioms.
(Pending a `lake build` pass like the rest of the new ClayCore additions.)
-/

namespace YangMills

open MeasureTheory Matrix Complex Real

noncomputable section

/-! ## The engine -/

/-- **Centre-eigenfunction vanishing principle.**

If `f : SU(N_c) → ℂ` is scaled by a constant `c ≠ 1` under left multiplication by
the centre element `ω·I` (`scalarCenterElement`), then its Haar integral vanishes.

This is the abstract core of every Z_N selection rule in the project. -/
theorem haar_integral_eq_zero_of_center_eigenfunction
    (N_c : ℕ) [NeZero N_c]
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℂ) (c : ℂ)
    (hf : ∀ U, f (scalarCenterElement N_c * U) = c * f U) (hc : c ≠ 1) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ), f U ∂(sunHaarProb N_c) = 0 := by
  set J : ℂ := ∫ U, f U ∂(sunHaarProb N_c) with hJ
  -- Left invariance of Haar against the centre element.
  have hinv : J = ∫ U, f (scalarCenterElement N_c * U) ∂(sunHaarProb N_c) := by
    rw [hJ]
    symm
    exact MeasureTheory.integral_mul_left_eq_self f (scalarCenterElement N_c)
  -- The eigenvalue pulls out of the integral.
  have hmul : (∫ U, f (scalarCenterElement N_c * U) ∂(sunHaarProb N_c)) = c * J := by
    have hfun : (fun U => f (scalarCenterElement N_c * U)) = (fun U => c * f U) :=
      funext hf
    calc ∫ U, f (scalarCenterElement N_c * U) ∂(sunHaarProb N_c)
        = ∫ U, c * f U ∂(sunHaarProb N_c) := by rw [hfun]
      _ = c * ∫ U, f U ∂(sunHaarProb N_c) := integral_const_mul c f
      _ = c * J := by rw [← hJ]
  rw [hmul] at hinv
  -- `J = c·J` with `c ≠ 1` forces `J = 0`.
  have hfactor : (1 - c) * J = 0 := by linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exact absurd (sub_eq_zero.mp h1).symm hc
  · exact h2

/-! ## All four Z_N selection rules as corollaries of the engine

Each is now a one-application proof: plug in the eigenvalue identity and the
primitivity fact already proved in the corresponding file. -/

/-- F0 via the engine: `∫ tr U = 0` for `N_c ≥ 2`.  Eigenvalue `c = ω`. -/
theorem trace_integral_zero_center
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      U.val.trace ∂(sunHaarProb N_c) = 0 :=
  haar_integral_eq_zero_of_center_eigenfunction N_c
    (fun U => U.val.trace) (rootOfUnity N_c)
    (fun U => trace_scalarCenter_mul N_c U)
    (rootOfUnity_ne_one N_c hN)

/-- Pure-power rule via the engine: `∫ (tr U)^k = 0` for `N_c ∤ k`.
Eigenvalue `c = ω^k`. -/
theorem trace_pow_integral_zero_center
    (N_c k : ℕ) [NeZero N_c] (hk : ¬ N_c ∣ k) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      (U.val.trace) ^ k ∂(sunHaarProb N_c) = 0 :=
  haar_integral_eq_zero_of_center_eigenfunction N_c
    (fun U => (U.val.trace) ^ k) ((rootOfUnity N_c) ^ k)
    (fun U => trace_scalarCenter_mul_pow N_c k U)
    (rootOfUnity_pow_ne_one_of_not_dvd N_c k hk)

/-- Mixed-moment rule via the engine: `∫ (tr U)^a conj(tr U)^b = 0` for
`N_c ∤ (a−b)`.  Eigenvalue `c = ω^a ω̄^b`. -/
theorem trace_mixedPow_integral_zero_center
    (N_c a b : ℕ) [NeZero N_c] (hdvd : ¬ (N_c : ℤ) ∣ ((a : ℤ) - (b : ℤ))) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      (U.val.trace) ^ a * (star (U.val.trace)) ^ b ∂(sunHaarProb N_c) = 0 :=
  haar_integral_eq_zero_of_center_eigenfunction N_c
    (fun U => (U.val.trace) ^ a * (star (U.val.trace)) ^ b)
    ((rootOfUnity N_c) ^ a * (star (rootOfUnity N_c)) ^ b)
    (fun U => trace_scalarCenter_mul_mixedPow N_c a b U)
    (rootOfUnity_pow_mul_star_pow_ne_one N_c a b hdvd)

/-- Matrix-coefficient rule via the engine:
`∫ (∏ U_{iₛjₛ})(∏ conj U_{kₜlₜ}) = 0` for `N_c ∤ (n−m)`.
Eigenvalue `c = ω^n ω̄^m`. -/
theorem fundMonomial_integral_zero_center
    (N_c n m : ℕ) [NeZero N_c]
    (i j : Fin n → Fin N_c) (k l : Fin m → Fin N_c)
    (hdvd : ¬ (N_c : ℤ) ∣ ((n : ℤ) - (m : ℤ))) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      fundMonomial N_c n m i j k l U ∂(sunHaarProb N_c) = 0 :=
  haar_integral_eq_zero_of_center_eigenfunction N_c
    (fundMonomial N_c n m i j k l)
    ((rootOfUnity N_c) ^ n * (star (rootOfUnity N_c)) ^ m)
    (fun U => fundMonomial_scalarCenter N_c n m i j k l U)
    (rootOfUnity_pow_mul_star_pow_ne_one N_c n m hdvd)

end

end YangMills
