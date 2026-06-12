/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.CenterVanishing

/-!
# Power-sum selection rule: `∫ tr(U^p) dHaar = 0` for `N_c ∤ p`

This file applies the centre-eigenfunction engine (`CenterVanishing.lean`) to a
*new* and more fundamental integrand than any of the four previous selection
rules: the **Newton power sums**

  `p_p(U) := tr(U^p)`        (trace of the *matrix* power, not the power of the trace).

The `p_p` are the generators of the algebra of class functions / the character
ring of SU(N_c): every irreducible character is a polynomial in them
(Newton–Girard), and the strong-coupling **character expansion** of the Boltzmann
weight `exp(−β Re tr U)` (node F5 of `HORIZON.md`, the heart of the cluster
expansion) is organised by them.  So the power-sum selection rule is exactly the
fact that controls *which terms can survive* in that expansion.

## The eigenvalue identity

The centre element `g = ω·I` is a **scalar** matrix, hence central in the matrix
algebra and in the group.  Therefore `(g·U)^p = g^p · U^p = ω^p · U^p`
(no path-ordering subtlety — central elements commute past everything), and so

  `tr((g·U)^p) = ω^p · tr(U^p)`,

i.e. `p_p` is a centre eigenfunction with eigenvalue `ω^p`.  Feeding this and the
primitivity fact `ω^p ≠ 1` (`rootOfUnity_pow_ne_one_of_not_dvd`, for `N_c ∤ p`)
to `haar_integral_eq_zero_of_center_eigenfunction` closes the result in one line.

This is a genuinely *different* integrand from `(tr U)^k`
(`SchurMomentVanishing`): there, `ω` is pulled out of `k` copies of the trace;
here it is pulled out of the `p`-th matrix power inside a single trace.  Both have
eigenvalue `ω^{exponent}`, which is the unifying point the engine makes manifest.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no new axioms.
(Pending a `lake build` pass.  Risk localised to the induction helper
`cscalar_smul_pow` and the structure-projection `simp only`.)
-/

namespace YangMills

open MeasureTheory Matrix Complex Real

noncomputable section

/-! ## A scalar pulls out of a matrix power -/

/-- `(c • M)^p = c^p • M^p` for a complex scalar acting on square matrices.
Proved by induction; this is the algebraic fact that the centre element, being
scalar, commutes through a matrix power. -/
theorem cscalar_smul_pow {N_c : ℕ} (c : ℂ)
    (M : Matrix (Fin N_c) (Fin N_c) ℂ) (p : ℕ) :
    (c • M) ^ p = c ^ p • M ^ p := by
  induction p with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, ih, pow_succ, pow_succ, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-! ## The eigenvalue identity for power sums -/

/-- `tr((ω·I · U)^p) = ω^p · tr(U^p)`.  The centre element is scalar, hence
central, so it pulls out of the matrix power. -/
theorem trace_scalarCenter_mul_matpow
    (N_c p : ℕ) [NeZero N_c]
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) :
    (((scalarCenterElement N_c * U).val) ^ p).trace =
    (rootOfUnity N_c) ^ p * ((U.val) ^ p).trace := by
  have hval : (scalarCenterElement N_c * U).val = rootOfUnity N_c • U.val := by
    show (scalarCenterElement N_c).val * U.val = rootOfUnity N_c • U.val
    unfold scalarCenterElement
    simp only
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [hval, cscalar_smul_pow, Matrix.trace_smul, smul_eq_mul]

/-! ## The power-sum selection rule -/

/-- **Main theorem — Newton power-sum selection rule.**

`∫ tr(U^p) dHaar = 0` on SU(N_c) whenever `N_c ∤ p`.  Proved by handing the
eigenvalue identity (`trace_scalarCenter_mul_matpow`, eigenvalue `ω^p`) and the
primitivity fact (`rootOfUnity_pow_ne_one_of_not_dvd`) to the centre-vanishing
engine. -/
theorem sunHaarProb_tracematpow_integral_zero
    (N_c p : ℕ) [NeZero N_c] (hp : ¬ N_c ∣ p) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      ((U.val) ^ p).trace ∂(sunHaarProb N_c) = 0 :=
  haar_integral_eq_zero_of_center_eigenfunction N_c
    (fun U => ((U.val) ^ p).trace) ((rootOfUnity N_c) ^ p)
    (fun U => trace_scalarCenter_mul_matpow N_c p U)
    (rootOfUnity_pow_ne_one_of_not_dvd N_c p hp)

/-- `p = 1` sanity check: recovers `∫ tr U = 0` (since `U^1 = U` and `N_c ∤ 1`
for `N_c ≥ 2`), via the power-sum route. -/
theorem sunHaarProb_tracematpow_one_integral_zero
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      ((U.val) ^ 1).trace ∂(sunHaarProb N_c) = 0 := by
  refine sunHaarProb_tracematpow_integral_zero N_c 1 ?_
  intro hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

end

end YangMills
