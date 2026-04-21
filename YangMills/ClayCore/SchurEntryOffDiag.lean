import YangMills.ClayCore.SchurEntryOrthogonality
noncomputable section
open Matrix Complex MeasureTheory
open scoped BigOperators
namespace YangMills.ClayCore
variable {N : ℕ} [NeZero N]

lemma piAntiSymSU_apply_entry (i k : Fin N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (m j : Fin N) :
    ((piAntiSymSU i k * U).val) m j =
      Complex.exp (Complex.I * (piAntiSymAngle i k m : ℂ)) * U.val m j := by
  show ((diagPhaseSU (piAntiSymAngle i k) (piAntiSymAngle_sum_zero i k) * U).val) m j = _
  rw [diagPhaseSU_apply_entry]
  rfl

lemma piAntiSymSU_entry_prod_flip (i k : Fin N) (hik : i ≠ k) (j l : Fin N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (piAntiSymSU i k * U).val i j * star ((piAntiSymSU i k * U).val k l) =
      -(U.val i j * star (U.val k l)) := by
  rw [piAntiSymSU_apply_entry, piAntiSymSU_apply_entry]
  have hstar :
      star (Complex.exp (Complex.I * (piAntiSymAngle i k k : ℂ)) * U.val k l) =
        star (U.val k l) *
          star (Complex.exp (Complex.I * (piAntiSymAngle i k k : ℂ))) :=
    StarMul.star_mul _ _
  rw [hstar]
  have h := piAntiSymSU_phase i k hik
  linear_combination (U.val i j * star (U.val k l)) * h

theorem sunHaarProb_entry_offdiag (i k : Fin N) (hik : i ≠ k) (j l : Fin N) :
    (∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N)) = 0 := by
  set I₀ := ∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) with hI₀
  have hflip := piAntiSymSU_entry_prod_flip i k hik j l
  have hinv : I₀ = -I₀ := by
    calc I₀
        = ∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) := hI₀
      _ = ∫ U, (piAntiSymSU i k * U).val i j *
            star ((piAntiSymSU i k * U).val k l) ∂(sunHaarProb N) :=
          (MeasureTheory.integral_mul_left_eq_self
            (μ := sunHaarProb N)
            (fun U => U.val i j * star (U.val k l))
            (piAntiSymSU i k)).symm
      _ = ∫ U, -(U.val i j * star (U.val k l)) ∂(sunHaarProb N) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hflip)
      _ = -∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) := integral_neg _
      _ = -I₀ := by rw [← hI₀]
  have h2I : (2 : ℂ) * I₀ = 0 := by
    have hdouble : (2 : ℂ) * I₀ = I₀ + I₀ := by ring
    rw [hdouble]
    nth_rw 2 [hinv]
    ring
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h2I).resolve_left h2ne
end YangMills.ClayCore