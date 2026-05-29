import YangMills.ClayCore.SchurEntryOrthogonality

/-!
# Schur Entry Orthogonality — off-diagonal vanishing (L2.6 step 1b-ii)

Main theorem: `∫ U_{ij} · star(U_{kl}) dHaar = 0` whenever `i ≠ k`.

Proof: apply the left-invariance of `sunHaarProb` against the phase
element `piAntiSymSU i k`; the phase factor contributes
`exp(I · π) = -1`. The functional equation `I₀ = -I₀` then forces
`I₀ = 0` in ℂ.

This generalizes `sunHaarProb_offdiag_integral_zero` (which was the
special case `j = i`, `l = k`) to arbitrary column indices.
-/

noncomputable section

open Matrix Complex MeasureTheory
open scoped BigOperators

namespace YangMills.ClayCore

variable {N : ℕ}

/-- Entry action of `piAntiSymSU i k` on the left: scales row `m` by the
    phase `exp(I · piAntiSymAngle i k m)`. -/
lemma piAntiSymSU_apply_entry (i k : Fin N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (m j : Fin N) :
    ((piAntiSymSU i k * U).val) m j =
      Complex.exp (Complex.I * (piAntiSymAngle i k m : ℂ)) * U.val m j := by
  show ((diagPhaseSU (piAntiSymAngle i k) (piAntiSymAngle_sum_zero i k) * U).val) m j = _
  rw [diagPhaseSU_apply_entry]
  rfl

/-- The `(i,j) · star (k,l)` integrand flips sign pointwise under left
    multiplication by `piAntiSymSU i k` when `i ≠ k`. -/
lemma piAntiSymSU_entry_prod_flip (i k : Fin N) (hik : i ≠ k) (j l : Fin N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (piAntiSymSU i k * U).val i j * star ((piAntiSymSU i k * U).val k l) =
      -(U.val i j * star (U.val k l)) := by
  rw [piAntiSymSU_apply_entry, piAntiSymSU_apply_entry, star_mul]
  have h := piAntiSymSU_phase i k hik
  linear_combination (U.val i j * star (U.val k l)) * h

/-- Schur off-diagonal entry orthogonality (L2.6 step 1b-ii):
    `∫ U_{ij} · star(U_{kl}) dHaar = 0` whenever `i ≠ k`. -/
theorem sunHaarProb_entry_offdiag (i k : Fin N) (hik : i ≠ k) (j l : Fin N) :
    (∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N)) = 0 := by
  set I₀ := ∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) with hI₀
  have hflip := piAntiSymSU_entry_prod_flip i k hik j l
  -- Functional equation `I₀ = -I₀` from left-invariance + phase
  have hinv : I₀ = -I₀ := by
    calc I₀
        = ∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) := hI₀
      _ = ∫ U, (piAntiSymSU i k * U).val i j * star ((piAntiSymSU i k * U).val k l)
            ∂(sunHaarProb N) :=
          (MeasureTheory.integral_mul_left_eq_self
            (μ := sunHaarProb N)
            (fun U => U.val i j * star (U.val k l))
            (piAntiSymSU i k)).symm
      _ = ∫ U, -(U.val i j * star (U.val k l)) ∂(sunHaarProb N) :=
          MeasureTheory.integral_congr_ae
            (Filter.EventuallyEq.of_forall hflip)
      _ = -∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) := integral_neg _
      _ = -I₀ := by rw [← hI₀]
  -- Conclude `I₀ = 0` from `I₀ = -I₀`
  have h2I : (2 : ℂ) * I₀ = 0 := by
    have hdouble : (2 : ℂ) * I₀ = I₀ + I₀ := by ring
    rw [hdouble]
    nth_rw 2 [hinv]
    ring
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h2I).resolve_left h2ne

end YangMills.ClayCore