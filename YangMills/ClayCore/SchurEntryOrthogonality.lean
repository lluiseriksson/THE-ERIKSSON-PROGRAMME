import YangMills.ClayCore.SchurDiagPhase

/-!
# Schur Entry Orthogonality — Phase setup (L2.6 step 1a)

Setup for the off-diagonal Schur orthogonality
`∫ U_{ij} · conj(U_{kl}) dHaar = 0` when `i ≠ k`.

We define the antisymmetric two-site angle
  `antiSymAngle i k m = 1[m=i] - 1[m=k]`
with `∑ antiSymAngle i k = 0`, and the associated SU(N) phase element
  `antiSymSU i k := diagPhaseSU (antiSymAngle i k) _`.

By construction `antiSymAngle i k i - antiSymAngle i k k = 2`, so
`exp(I · (θ_i - θ_k)) = exp(2·I)` is nontrivial — the obstruction used in the
integral-vanishing proof in a subsequent file.
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

end YangMills.ClayCore