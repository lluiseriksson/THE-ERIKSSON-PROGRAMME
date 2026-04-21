import YangMills.ClayCore.SchurDiagPhase

/-!
# Schur Entry Orthogonality — Phase setup (L2.6 steps 1a + 1b-i)

Setup for the off-diagonal Schur orthogonality
`∫ U_{ij} · conj(U_{kl}) dHaar = 0` when `i ≠ k`.

We define two antisymmetric two-site angles:
* `antiSymAngle i k m = 1[m=i] - 1[m=k]` (difference = 2)
* `piAntiSymAngle i k m = (π/2) · antiSymAngle i k m` (difference = π)

The second is the one actually used in the integral-vanishing proof,
because the phase factor `exp(I · (θ_i - θ_k)) = exp(I · π) = -1` is
trivially ≠ 1 (no π-irrationality argument needed).
-/

noncomputable section

open Matrix Complex
open scoped BigOperators

namespace YangMills.ClayCore

variable {N : ℕ}

/-- Antisymmetric two-site angle: `+1` on index `i`, `-1` on index `k`, `0` elsewhere. -/
def antiSymAngle (i k : Fin N) : Fin N → ℝ := fun m =>
  (if m = i then (1 : ℝ) else 0) - (if m = k then (1 : ℝ) else 0)

@[simp] lemma antiSymAngle_apply (i k m : Fin N) :
    antiSymAngle i k m =
      (if m = i then (1 : ℝ) else 0) - (if m = k then (1 : ℝ) else 0) := rfl

lemma antiSymAngle_sum_zero (i k : Fin N) :
    ∑ m, antiSymAngle i k m = 0 := by
  simp [antiSymAngle, Finset.sum_sub_distrib, Finset.sum_ite_eq']

lemma antiSymAngle_at_i (i k : Fin N) (hik : i ≠ k) :
    antiSymAngle i k i = 1 := by
  simp [antiSymAngle, hik]

lemma antiSymAngle_at_k (i k : Fin N) (hik : i ≠ k) :
    antiSymAngle i k k = -1 := by
  simp [antiSymAngle, Ne.symm hik]

lemma antiSymAngle_diff (i k : Fin N) (hik : i ≠ k) :
    antiSymAngle i k i - antiSymAngle i k k = 2 := by
  rw [antiSymAngle_at_i i k hik, antiSymAngle_at_k i k hik]
  ring

/-- The SU(N) element built from the antisymmetric angle. -/
def antiSymSU (i k : Fin N) : Matrix.specialUnitaryGroup (Fin N) ℂ :=
  diagPhaseSU (antiSymAngle i k) (antiSymAngle_sum_zero i k)

@[simp] lemma antiSymSU_val (i k : Fin N) :
    (antiSymSU i k).val = diagPhaseMat (antiSymAngle i k) := rfl

/-! ## π-scaled variant

The π-scaled antisymmetric angle: still sums to zero, but now
`θ_i - θ_k = π`, so the phase factor is `exp(I · π) = -1`, which is
manifestly ≠ 1. This is the version used downstream in the integral
vanishing proof. -/

/-- `piAntiSymAngle i k m = (π/2) · antiSymAngle i k m`. -/
def piAntiSymAngle (i k : Fin N) : Fin N → ℝ := fun m =>
  (Real.pi / 2) * antiSymAngle i k m

@[simp] lemma piAntiSymAngle_apply (i k m : Fin N) :
    piAntiSymAngle i k m = (Real.pi / 2) * antiSymAngle i k m := rfl

lemma piAntiSymAngle_sum_zero (i k : Fin N) :
    ∑ m, piAntiSymAngle i k m = 0 := by
  simp only [piAntiSymAngle, ← Finset.mul_sum, antiSymAngle_sum_zero, mul_zero]

lemma piAntiSymAngle_at_i (i k : Fin N) (hik : i ≠ k) :
    piAntiSymAngle i k i = Real.pi / 2 := by
  unfold piAntiSymAngle
  rw [antiSymAngle_at_i i k hik]
  ring

lemma piAntiSymAngle_at_k (i k : Fin N) (hik : i ≠ k) :
    piAntiSymAngle i k k = -(Real.pi / 2) := by
  unfold piAntiSymAngle
  rw [antiSymAngle_at_k i k hik]
  ring

lemma piAntiSymAngle_diff (i k : Fin N) (hik : i ≠ k) :
    piAntiSymAngle i k i - piAntiSymAngle i k k = Real.pi := by
  rw [piAntiSymAngle_at_i i k hik, piAntiSymAngle_at_k i k hik]
  ring

/-- The SU(N) element built from the π-scaled antisymmetric angle. -/
def piAntiSymSU (i k : Fin N) : Matrix.specialUnitaryGroup (Fin N) ℂ :=
  diagPhaseSU (piAntiSymAngle i k) (piAntiSymAngle_sum_zero i k)

@[simp] lemma piAntiSymSU_val (i k : Fin N) :
    (piAntiSymSU i k).val = diagPhaseMat (piAntiSymAngle i k) := rfl

/-- Key phase identity: `exp(I · θ_i) · star(exp(I · θ_k)) = exp(I · π) = -1`
    for the π-scaled antisymmetric angle with `i ≠ k`. -/
lemma piAntiSymSU_phase (i k : Fin N) (hik : i ≠ k) :
    Complex.exp (Complex.I * (piAntiSymAngle i k i : ℂ)) *
      star (Complex.exp (Complex.I * (piAntiSymAngle i k k : ℂ))) = -1 := by
  have hstar : star (Complex.exp (Complex.I * (piAntiSymAngle i k k : ℂ))) =
              Complex.exp (-(Complex.I * (piAntiSymAngle i k k : ℂ))) := by
    show (starRingEnd ℂ) (Complex.exp (Complex.I * (piAntiSymAngle i k k : ℂ))) = _
    rw [← Complex.exp_conj]
    congr 1
    show (starRingEnd ℂ) (Complex.I * (piAntiSymAngle i k k : ℂ)) = _
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hstar, ← Complex.exp_add]
  have hadd : Complex.I * (piAntiSymAngle i k i : ℂ) +
                -(Complex.I * (piAntiSymAngle i k k : ℂ)) =
              Complex.I * ((piAntiSymAngle i k i - piAntiSymAngle i k k : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hadd, piAntiSymAngle_diff i k hik, mul_comm]
  exact Complex.exp_pi_mul_I

end YangMills.ClayCore