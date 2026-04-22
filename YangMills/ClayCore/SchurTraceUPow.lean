/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.ClayCore.SchurTracePow

/-!
# Power-sum trace vanishing on SU(N_c)

Companion to `SchurTracePow.lean`.  Where that file proves

  `∫ (tr U)^k dHaar = 0` on SU(N_c) when `N_c ∤ k`,

this file proves the *other* natural family:

  `∫ tr(U^k) dHaar = 0` on SU(N_c) when `N_c ∤ k`.

Both `(tr U)^k` and `tr(U^k)` are class functions on SU(N_c), but they
are genuinely different integrands:
- `(tr U)^k = (∑_i U_{ii})^k` is the `k`-th power of the 1st power sum.
- `tr(U^k) = ∑_i (U^k)_{ii} = ∑_i λ_i^k` is the `k`-th power sum of
  the eigenvalues.

By Newton's identities they span the same subalgebra of class functions
over ℚ, but as integrands each is independent.

## Proof

Same central-element technique as `SchurTracePow.lean`.  With
`Ω := ω·I ∈ SU(N_c)`, since `Ω` is the scalar `ω • 1` acting on matrices:
`Ω · U = ω • U`, hence `(Ω · U)^k = ω^k • U^k`, and therefore
`tr((Ω · U)^k) = ω^k · tr(U^k)`.  Haar left-invariance then gives
`J = ω^k · J`, hence `(1 - ω^k) · J = 0`; when `N_c ∤ k` we have
`ω^k ≠ 1` (by `rootOfUnity_pow_ne_one`), so `J = 0`.

## Representation-theoretic meaning

`tr(U^k)` is the character of the `k`-th Adams operation `ψ^k` applied
to the fundamental representation `V`.  By the Murnaghan-Nakayama
rule on hook-shaped Young diagrams,

  `tr(U^k) = ∑_{r=0}^{k-1} (-1)^r · χ_{[k-r, 1^r]}(U)`,

a signed sum of hook-character contributions.  When `N_c ∤ k`, none of
the hooks `[k-r, 1^r]` with `0 ≤ r ≤ min(k-1, N_c-1)` is the trivial
representation, so character orthogonality against the trivial rep
forces the Haar integral to `0`.

## Corollaries

- `k = 1` and `N_c ≥ 2`:  `∫ tr U dHaar = 0`, recovering the degree-1
  case `sunHaarProb_trace_complex_integral_zero`.
- `k = 2` and `N_c ≥ 3`:  `∫ tr(U²) dHaar = 0`.
- `k = 3` and `N_c ≥ 4`:  `∫ tr(U³) dHaar = 0`.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry.  No new axioms.
-/

namespace YangMills

open MeasureTheory Matrix Complex

noncomputable section

/-! ## (ω·I) · U = ω • U in the underlying matrix ring -/

/-- `(scalarCenterElement N_c * U).val = ω • U.val`, reducing the
scalar-center left-multiplication to the scalar action on matrices. -/
theorem scalarCenter_mul_val_eq_smul (N_c : ℕ) [NeZero N_c]
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) :
    (scalarCenterElement N_c * U).val = rootOfUnity N_c • U.val := by
  show (scalarCenterElement N_c).val * U.val = rootOfUnity N_c • U.val
  unfold scalarCenterElement
  show (rootOfUnity N_c • (1 : Matrix (Fin N_c) (Fin N_c) ℂ)) * U.val =
       rootOfUnity N_c • U.val
  rw [Matrix.smul_mul, Matrix.one_mul]

/-! ## Powers of the smul'd matrix -/

/-- `(c • A)^k = c^k • A^k` for any scalar `c : ℂ` and matrix `A` over ℂ,
by induction on `k`.  Uses only the interaction of `smul` with matrix
multiplication. -/
private theorem smul_pow_matrix {N_c : ℕ} (c : ℂ)
    (A : Matrix (Fin N_c) (Fin N_c) ℂ) :
    ∀ k : ℕ, (c • A) ^ k = c ^ k • A ^ k
  | 0 => by simp
  | (k + 1) => by
      rw [pow_succ, pow_succ c, pow_succ A, smul_pow_matrix c A k]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- `((ω·I) · U)^k = ω^k • U^k`, combining `scalarCenter_mul_val_eq_smul`
with `smul_pow_matrix`. -/
theorem scalarCenter_mul_pow_val (N_c : ℕ) [NeZero N_c]
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (k : ℕ) :
    ((scalarCenterElement N_c * U).val) ^ k =
    (rootOfUnity N_c) ^ k • (U.val) ^ k := by
  rw [scalarCenter_mul_val_eq_smul]
  exact smul_pow_matrix (rootOfUnity N_c) U.val k

/-! ## Trace of U^k under scalar-center left-multiplication -/

/-- `tr(((ω·I) · U)^k) = ω^k · tr(U^k)`.  Combines the matrix-power
identity with the trace-scalar linearity `trace (c • M) = c • trace M`. -/
theorem trace_scalarCenter_mul_Upow (N_c : ℕ) [NeZero N_c]
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (k : ℕ) :
    (((scalarCenterElement N_c * U).val) ^ k).trace =
    (rootOfUnity N_c) ^ k * ((U.val) ^ k).trace := by
  rw [scalarCenter_mul_pow_val, Matrix.trace_smul, smul_eq_mul]

/-! ## Main theorem -/

/-- **Main theorem — power-sum trace vanishing.**  For any `k : ℕ` with
`¬ N_c ∣ k`, the Haar integral of `tr(U^k)` over SU(N_c) vanishes.

Specializes at `k = 1` (with `N_c ≥ 2`, the case `¬ N_c ∣ 1`) to
`sunHaarProb_trace_complex_integral_zero`. -/
theorem sunHaarProb_trace_Upow_integral_zero (N_c : ℕ) [NeZero N_c]
    {k : ℕ} (hkN : ¬ N_c ∣ k) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      ((U.val) ^ k).trace ∂(sunHaarProb N_c) = 0 := by
  set J : ℂ := ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      ((U.val) ^ k).trace ∂(sunHaarProb N_c) with hJdef
  -- Step 1: Haar left-invariance with Ω = ω·I
  have hinv : J = ∫ U, (((scalarCenterElement N_c * U).val) ^ k).trace
                      ∂(sunHaarProb N_c) := by
    rw [hJdef]; symm
    exact MeasureTheory.integral_mul_left_eq_self
          (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
              ((U.val) ^ k).trace)
          (scalarCenterElement N_c)
  -- Step 2: pointwise rewrite of the integrand
  have heq : (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
               (((scalarCenterElement N_c * U).val) ^ k).trace) =
             (fun U => (rootOfUnity N_c) ^ k * ((U.val) ^ k).trace) := by
    funext U; exact trace_scalarCenter_mul_Upow N_c U k
  -- Step 3: pull ω^k out of the integral
  have hmul : (∫ U, (((scalarCenterElement N_c * U).val) ^ k).trace
                      ∂(sunHaarProb N_c)) =
              (rootOfUnity N_c) ^ k * J := by
    calc ∫ U, (((scalarCenterElement N_c * U).val) ^ k).trace ∂(sunHaarProb N_c)
        = ∫ U, (rootOfUnity N_c) ^ k * ((U.val) ^ k).trace ∂(sunHaarProb N_c) := by
          rw [heq]
      _ = (rootOfUnity N_c) ^ k * ∫ U, ((U.val) ^ k).trace ∂(sunHaarProb N_c) :=
          MeasureTheory.integral_const_mul _ _
      _ = (rootOfUnity N_c) ^ k * J := by rw [← hJdef]
  -- Step 4: (1 - ω^k)·J = 0, and ω^k ≠ 1 forces J = 0
  rw [hmul] at hinv
  have hfactor : (1 - (rootOfUnity N_c) ^ k) * J = 0 := by linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exact absurd (sub_eq_zero.mp h1).symm (rootOfUnity_pow_ne_one N_c hkN)
  · exact h2

/-! ## Concrete low-degree corollaries -/

/-- `∫ tr(U²) dHaar = 0` on SU(N_c) for every `N_c ≥ 3`. -/
theorem sunHaarProb_trace_Usq_integral_zero (N_c : ℕ) [NeZero N_c]
    (hN : 3 ≤ N_c) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      ((U.val) ^ 2).trace ∂(sunHaarProb N_c) = 0 := by
  refine sunHaarProb_trace_Upow_integral_zero N_c ?_
  intro h
  have : N_c ≤ 2 := Nat.le_of_dvd (by norm_num) h
  omega

/-- `∫ tr(U³) dHaar = 0` on SU(N_c) for every `N_c ≥ 4`. -/
theorem sunHaarProb_trace_Ucube_integral_zero (N_c : ℕ) [NeZero N_c]
    (hN : 4 ≤ N_c) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      ((U.val) ^ 3).trace ∂(sunHaarProb N_c) = 0 := by
  refine sunHaarProb_trace_Upow_integral_zero N_c ?_
  intro h
  have : N_c ≤ 3 := Nat.le_of_dvd (by norm_num) h
  omega

/-! ## Non-triviality witness -/

/-- The integrand `tr(U^k)` is non-trivial: at `1 ∈ SU(N_c)`, `U^k = 1`
and `tr(1) = N_c`. -/
theorem sunHaarProb_trace_Upow_at_one (N_c : ℕ) [NeZero N_c] (k : ℕ) :
    (((1 : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)).val ^ k).trace : ℂ)
      = (N_c : ℂ) := by
  have hval : (1 : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)).val =
      (1 : Matrix (Fin N_c) (Fin N_c) ℂ) := rfl
  rw [hval, one_pow, Matrix.trace_one, Fintype.card_fin]

end

end YangMills
