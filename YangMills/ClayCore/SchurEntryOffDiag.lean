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

## Bit-rot repair (2026-06-18)

This module was previously excluded from `YangMillsCore` because three
Mathlib v4.29 elaboration seams bit-rotted:
* `rw [star_mul]` was ambiguous (both the `StarMul` reverse-order law
  `star_mul` and its commutative variant `star_mul'` apply on `ℂ`);
* `Filter.EventuallyEq.of_forall` was removed as a public name;
* `NeZero` instance synthesis was left implicit.

The repair follows the robust idiom already used by `SchurZeroMean` and
`SchurDiagPhase`: rewrite the conjugation step via the explicit
`(starRingEnd ℂ)` / `Complex.conj_*` lemmas (no bare `star_mul`), and
carry the invariance through `integral_mul_left_eq_self` + `funext`
instead of `integral_congr_ae` + `EventuallyEq.of_forall`. The
mathematics is unchanged; only the proof scripts were hardened.
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

/-- Conjugation reverses the order on ℂ, computed through the explicit
    ring endomorphism (avoids the ambiguous bare `star_mul` lemma).
    `starRingEnd` is declared as a `RingHom`, so `map_mul` yields the
    direct order `star a * star b`; commutativity of `ℂ` reorders it to
    the `star b * star a` form the integrand flip needs. -/
private lemma star_mul_complex (a b : ℂ) :
    star (a * b) = star b * star a := by
  rw [show star (a * b) = (starRingEnd ℂ) (a * b) from rfl,
      (starRingEnd ℂ).map_mul, mul_comm,
      show (starRingEnd ℂ) a = star a from rfl,
      show (starRingEnd ℂ) b = star b from rfl]

/-- The `(i,j) · star (k,l)` integrand flips sign pointwise under left
    multiplication by `piAntiSymSU i k` when `i ≠ k`. -/
lemma piAntiSymSU_entry_prod_flip (i k : Fin N) (hik : i ≠ k) (j l : Fin N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (piAntiSymSU i k * U).val i j * star ((piAntiSymSU i k * U).val k l) =
      -(U.val i j * star (U.val k l)) := by
  rw [piAntiSymSU_apply_entry, piAntiSymSU_apply_entry, star_mul_complex]
  -- Now the LHS is  e_i · U_ij · star(e_k · U_kl)  =  e_i · U_ij · star(U_kl) · star(e_k)
  -- i.e. it factors as  (e_i · star(e_k)) · (U_ij · star(U_kl)).
  have hphase : Complex.exp (Complex.I * (piAntiSymAngle i k i : ℂ)) *
                  star (Complex.exp (Complex.I * (piAntiSymAngle i k k : ℂ))) = -1 :=
    piAntiSymSU_phase i k hik
  linear_combination (U.val i j * star (U.val k l)) * hphase

/-- Schur off-diagonal entry orthogonality (L2.6 step 1b-ii):
    `∫ U_{ij} · star(U_{kl}) dHaar = 0` whenever `i ≠ k`. -/
theorem sunHaarProb_entry_offdiag [NeZero N] (i k : Fin N) (hik : i ≠ k) (j l : Fin N) :
    (∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N)) = 0 := by
  set I₀ := ∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) with hI₀
  have hflip := piAntiSymSU_entry_prod_flip i k hik j l
  -- Functional equation `I₀ = -I₀` from left-invariance + phase,
  -- following the robust `funext`-and-`rw` idiom of `SchurZeroMean`.
  have heq_fun : (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ =>
                    (piAntiSymSU i k * U).val i j * star ((piAntiSymSU i k * U).val k l)) =
                 (fun U => -(U.val i j * star (U.val k l))) := by
    funext U
    exact hflip U
  have hinv : I₀ = -I₀ := by
    -- Left-invariance: ∫ f(U) dμ = ∫ f(g·U) dμ.  So I₀ = ∫ f = ∫ (f ∘ (g·)).
    have hleft : (∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N)) =
                 ∫ U,
                   (piAntiSymSU i k * U).val i j * star ((piAntiSymSU i k * U).val k l)
                     ∂(sunHaarProb N) :=
      (MeasureTheory.integral_mul_left_eq_self
        (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ =>
           U.val i j * star (U.val k l))
        (piAntiSymSU i k)).symm
    calc I₀
        = ∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) := hI₀
      _ = ∫ U,
          (piAntiSymSU i k * U).val i j * star ((piAntiSymSU i k * U).val k l)
            ∂(sunHaarProb N) := hleft
      _ = ∫ U, -(U.val i j * star (U.val k l)) ∂(sunHaarProb N) := by rw [heq_fun]
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
