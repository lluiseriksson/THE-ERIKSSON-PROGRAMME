/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.P8_PhysicalGap.SUN_StateConstruction

/-!
# Milestone L2.3: Schur zero-mean for SU(N_c)

Proves the first non-trivial Schur-orthogonality fact on SU(N_c)
formalised from `sunHaarProb`:

  `∫ (U.val.trace).re ∂(sunHaarProb N_c) = 0`     for `N_c ≥ 2`.

This is the `ρ = fundamental` case of the general character-orthogonality
identity `∫ χ_ρ(U) dHaar = 0` for non-trivial irreducible `ρ`, and sits
on the critical path of the Peter–Weyl / Osterwalder–Seiler roadmap
(`PETER_WEYL_ROADMAP.md`, Layer 2 first step).

## Proof strategy

Let `ω = exp(2πi/N_c) ∈ ℂ`.  Then `ω · I` is an element of SU(N_c)
(determinant `ω^{N_c} = 1`, unitary because `|ω| = 1`), and for
`N_c ≥ 2` it is distinct from the identity.

By left-invariance of Haar, for any fixed `g ∈ SU(N_c)`,
`∫ f(g · U) dHaar = ∫ f(U) dHaar`.

Apply this with `g = ω · I` and `f(U) = U.val.trace`.  By linearity of
the trace, `tr((ω·I) · U) = ω · tr(U)`; linearity of the Bochner
integral then gives `J = ω · J`, i.e. `(1 - ω) · J = 0`.  Since
`ω ≠ 1`, the complex integral `J` vanishes; the real integral is the
real part of `J`.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry.  No new axioms.
-/

namespace YangMills

open MeasureTheory Matrix Complex Real

noncomputable section

/-! ## The N_c-th root of unity -/

/-- The primitive `N_c`-th root of unity viewed as a complex number:
`ω = exp(2πi / N_c)`. -/
noncomputable def rootOfUnity (N_c : ℕ) : ℂ :=
  Complex.exp (2 * (π : ℂ) * Complex.I / (N_c : ℂ))

/-- `ω^{N_c} = 1`. -/
theorem rootOfUnity_pow_eq_one (N_c : ℕ) [NeZero N_c] :
    rootOfUnity N_c ^ N_c = 1 := by
  unfold rootOfUnity
  rw [← Complex.exp_nat_mul]
  have hNne : (N_c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N_c)
  have hrew : (N_c : ℂ) * (2 * (π : ℂ) * Complex.I / (N_c : ℂ)) =
      2 * (π : ℂ) * Complex.I := by
    field_simp
  rw [hrew]
  exact Complex.exp_two_pi_mul_I

/-- For `N_c ≥ 2`, `ω = exp(2πi/N_c) ≠ 1`. -/
theorem rootOfUnity_ne_one (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c) :
    rootOfUnity N_c ≠ 1 := by
  intro hEq
  unfold rootOfUnity at hEq
  rw [Complex.exp_eq_one_iff] at hEq
  obtain ⟨n, hn⟩ := hEq
  have h2piI_ne : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    refine mul_ne_zero two_ne_zero ?_
    exact_mod_cast Real.pi_ne_zero
  have hNne : (N_c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N_c)
  have hflipped : (n : ℂ) * (2 * (π : ℂ) * Complex.I) =
      (2 * (π : ℂ) * Complex.I) / (N_c : ℂ) := hn.symm
  have hmulN : (n : ℂ) * (2 * (π : ℂ) * Complex.I) * (N_c : ℂ) =
      (2 * (π : ℂ) * Complex.I) := by
    rw [hflipped, div_mul_cancel₀ _ hNne]
  have h1C : (1 : ℂ) * (2 * (π : ℂ) * Complex.I) =
      ((n : ℂ) * (N_c : ℂ)) * (2 * (π : ℂ) * Complex.I) := by
    rw [one_mul]
    calc (2 * (π : ℂ) * Complex.I)
        = (n : ℂ) * (2 * (π : ℂ) * Complex.I) * (N_c : ℂ) := hmulN.symm
      _ = ((n : ℂ) * (N_c : ℂ)) * (2 * (π : ℂ) * Complex.I) := by ring
  have h1 : (1 : ℂ) = (n : ℂ) * (N_c : ℂ) :=
    mul_right_cancel₀ h2piI_ne h1C
  have hRe : (1 : ℝ) = (n : ℝ) * (N_c : ℝ) := by
    have := congr_arg Complex.re h1
    simpa using this
  have hNcR : (2 : ℝ) ≤ (N_c : ℝ) := by exact_mod_cast hN
  have hNcR_pos : (0 : ℝ) < (N_c : ℝ) := by linarith
  rcases lt_trichotomy (n : ℝ) 0 with hneg | hzero | hpos
  · have hprod_neg : (n : ℝ) * (N_c : ℝ) < 0 :=
      mul_neg_of_neg_of_pos hneg hNcR_pos
    linarith
  · rw [hzero, zero_mul] at hRe
    exact absurd hRe one_ne_zero
  · have hn_int_pos : (1 : ℤ) ≤ n := by
      have : (0 : ℝ) < (n : ℝ) := hpos
      have h0 : (0 : ℤ) < n := by exact_mod_cast this
      omega
    have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_int_pos
    have hprod_ge_two : (2 : ℝ) ≤ (n : ℝ) * (N_c : ℝ) := by
      calc (2 : ℝ) = 1 * 2 := by norm_num
        _ ≤ (n : ℝ) * (N_c : ℝ) :=
          mul_le_mul hn_ge_one hNcR (by norm_num) (by linarith)
    linarith

/-! ## The scalar center element `ω · I` ∈ SU(N_c) -/

/-- For `ω = exp(2πi/N_c)`, we have `star(ω) * ω = 1`.  Proved via
`conj(exp z) = exp(conj z)` and the identity `conj(2πi/N_c) = -(2πi/N_c)`,
then `exp(-z) * exp(z) = exp(0) = 1`. -/
theorem star_rootOfUnity_mul_self (N_c : ℕ) [NeZero N_c] :
    star (rootOfUnity N_c) * rootOfUnity N_c = 1 := by
  have hstar_eq : star (rootOfUnity N_c) =
      Complex.exp (-(2 * (π : ℂ) * Complex.I / (N_c : ℂ))) := by
    show (starRingEnd ℂ) _ = _
    unfold rootOfUnity
    rw [← Complex.exp_conj]
    congr 1
    rw [show (2 * (π : ℂ) * Complex.I / (N_c : ℂ)) =
          ((2 * π / N_c : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hstar_eq]
  unfold rootOfUnity
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- `ω · I_{N_c}` is unitary. -/
theorem scalarMatrix_mem_unitaryGroup (N_c : ℕ) [NeZero N_c] :
    rootOfUnity N_c • (1 : Matrix (Fin N_c) (Fin N_c) ℂ) ∈
    Matrix.unitaryGroup (Fin N_c) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  -- `Matrix.mem_unitaryGroup_iff` gives `A * star A = 1`, so we prove
  -- `(ω • 1) * star (ω • 1) = 1`, requiring `ω * star ω = 1`.
  have hconjmul : rootOfUnity N_c * star (rootOfUnity N_c) = 1 := by
    rw [mul_comm]; exact star_rootOfUnity_mul_self N_c
  calc (rootOfUnity N_c • (1 : Matrix (Fin N_c) (Fin N_c) ℂ)) *
        star (rootOfUnity N_c • (1 : Matrix (Fin N_c) (Fin N_c) ℂ))
      = (rootOfUnity N_c • (1 : Matrix (Fin N_c) (Fin N_c) ℂ)) *
         (star (rootOfUnity N_c) • (1 : Matrix (Fin N_c) (Fin N_c) ℂ)) := by
          rw [star_smul, star_one]
    _ = rootOfUnity N_c •
          ((1 : Matrix (Fin N_c) (Fin N_c) ℂ) *
           (star (rootOfUnity N_c) • (1 : Matrix (Fin N_c) (Fin N_c) ℂ))) := by
          rw [Matrix.smul_mul]
    _ = rootOfUnity N_c • star (rootOfUnity N_c) •
          ((1 : Matrix (Fin N_c) (Fin N_c) ℂ) *
           (1 : Matrix (Fin N_c) (Fin N_c) ℂ)) := by
          rw [Matrix.mul_smul]
    _ = rootOfUnity N_c • star (rootOfUnity N_c) •
          (1 : Matrix (Fin N_c) (Fin N_c) ℂ) := by
          rw [Matrix.one_mul]
    _ = (rootOfUnity N_c * star (rootOfUnity N_c)) •
          (1 : Matrix (Fin N_c) (Fin N_c) ℂ) := by
          rw [smul_smul]
    _ = (1 : ℂ) • (1 : Matrix (Fin N_c) (Fin N_c) ℂ) := by
          rw [hconjmul]
    _ = (1 : Matrix (Fin N_c) (Fin N_c) ℂ) := one_smul _ _

/-- `det(ω · I) = ω^{N_c} = 1`. -/
theorem scalarMatrix_det (N_c : ℕ) [NeZero N_c] :
    Matrix.det (rootOfUnity N_c • (1 : Matrix (Fin N_c) (Fin N_c) ℂ)) = 1 := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  exact rootOfUnity_pow_eq_one N_c

/-- `ω · I ∈ SU(N_c)`. -/
theorem scalarMatrix_mem_specialUnitaryGroup (N_c : ℕ) [NeZero N_c] :
    rootOfUnity N_c • (1 : Matrix (Fin N_c) (Fin N_c) ℂ) ∈
    Matrix.specialUnitaryGroup (Fin N_c) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  exact ⟨scalarMatrix_mem_unitaryGroup N_c, scalarMatrix_det N_c⟩

/-- The canonical `ω · I` element of SU(N_c), bundled as a subtype. -/
noncomputable def scalarCenterElement (N_c : ℕ) [NeZero N_c] :
    ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) :=
  ⟨rootOfUnity N_c • (1 : Matrix (Fin N_c) (Fin N_c) ℂ),
   scalarMatrix_mem_specialUnitaryGroup N_c⟩

/-- `tr((ω · I) · U) = ω · tr(U)`. -/
theorem trace_scalarCenter_mul
    (N_c : ℕ) [NeZero N_c]
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) :
    ((scalarCenterElement N_c * U).val).trace =
    rootOfUnity N_c * U.val.trace := by
  show (((scalarCenterElement N_c).val * U.val)).trace = _
  unfold scalarCenterElement
  simp only
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]

/-! ## The zero-mean Schur identity -/

/-- `sunHaarProb N_c` is left-invariant.  Follows from the `IsHaarMeasure`
instance on `Measure.haarMeasure`. -/
instance sunHaarProb_isMulLeftInvariant (N_c : ℕ) [NeZero N_c] :
    Measure.IsMulLeftInvariant (sunHaarProb N_c) := by
  unfold sunHaarProb; infer_instance

/-- Continuity of the trace on SU(N_c). -/
theorem continuous_trace_sub (N_c : ℕ) [NeZero N_c] :
    Continuous
      (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => U.val.trace) := by
  have htr : Continuous (fun M : Matrix (Fin N_c) (Fin N_c) ℂ => M.trace) := by
    show Continuous fun M : Fin N_c → Fin N_c → ℂ => ∑ i, M i i
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact (continuous_apply i).comp (continuous_apply i)
  exact htr.comp continuous_subtype_val

/-- The trace is integrable against `sunHaarProb N_c`. -/
theorem trace_integrable (N_c : ℕ) [NeZero N_c] :
    Integrable
      (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => U.val.trace)
      (sunHaarProb N_c) :=
  (continuous_trace_sub N_c).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **Main theorem, complex form.**

`∫ tr(U) dHaar = 0` on SU(N_c) for every `N_c ≥ 2`.  This is the
`ρ = fundamental` case of Schur orthogonality. -/
theorem sunHaarProb_trace_complex_integral_zero
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      U.val.trace ∂(sunHaarProb N_c) = 0 := by
  set J : ℂ := ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      U.val.trace ∂(sunHaarProb N_c) with hJdef
  have hinv : J = ∫ U, ((scalarCenterElement N_c * U).val).trace
                      ∂(sunHaarProb N_c) := by
    rw [hJdef]
    symm
    exact MeasureTheory.integral_mul_left_eq_self
          (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => U.val.trace)
          (scalarCenterElement N_c)
  have heq : (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
               ((scalarCenterElement N_c * U).val).trace) =
             (fun U => rootOfUnity N_c * U.val.trace) := by
    funext U; exact trace_scalarCenter_mul N_c U
  have hmul : (∫ U, ((scalarCenterElement N_c * U).val).trace
                      ∂(sunHaarProb N_c)) =
               rootOfUnity N_c * J := by
    calc ∫ U, ((scalarCenterElement N_c * U).val).trace ∂(sunHaarProb N_c)
        = ∫ U, rootOfUnity N_c * U.val.trace ∂(sunHaarProb N_c) := by rw [heq]
      _ = rootOfUnity N_c * ∫ U, U.val.trace ∂(sunHaarProb N_c) :=
          MeasureTheory.integral_const_mul _ _
      _ = rootOfUnity N_c * J := by rw [← hJdef]
  rw [hmul] at hinv
  have hfactor : (1 - rootOfUnity N_c) * J = 0 := by linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · have hω_eq : rootOfUnity N_c = 1 := by
      have := sub_eq_zero.mp h1
      exact this.symm
    exact absurd hω_eq (rootOfUnity_ne_one N_c hN)
  · exact h2

/-- **Main theorem (real form, Milestone L2.3).**

`∫ Re(tr(U)) dHaar = 0` on SU(N_c) for every `N_c ≥ 2`.  Taking real
parts of the complex identity, using `Complex.integral_re`. -/
theorem sunHaarProb_trace_re_integral_zero
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      (U.val.trace).re ∂(sunHaarProb N_c) = 0 := by
  have hC := sunHaarProb_trace_complex_integral_zero N_c hN
  have hint := trace_integrable N_c
  have hcomm := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at hcomm
  rw [hcomm, hC]
  rfl

/-! ## Non-triviality witness -/

/-- The integrand is non-trivial: at the identity it attains the value
`N_c ≥ 2`, ruling out the vacuous interpretation where the zero-mean
identity is tautological. -/
theorem sunHaarProb_trace_re_nontrivial
    (N_c : ℕ) [NeZero N_c] :
    ((1 : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)).val.trace).re = (N_c : ℝ) := by
  have hval : (1 : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)).val =
      (1 : Matrix (Fin N_c) (Fin N_c) ℂ) := rfl
  rw [hval, Matrix.trace_one, Fintype.card_fin]
  simp

end

end YangMills
