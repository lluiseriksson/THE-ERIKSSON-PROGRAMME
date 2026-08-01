import YangMills.SU2ThetaPrism.Analysis
import YangMills.ClayCore.SchurNormOne
import YangMills.ClayCore.SchurTwoSitePhase

/-!
# Quaternion-coordinate Haar moments for SU(2)

This file gives a second, independent proof of the normalized fundamental
character moment `integral chi^2 = 1`.  It does not invoke Schur
orthogonality.  Instead it regards the first row of an SU(2) matrix as the
four real quaternion coordinates, uses the unit-sphere equation, and uses
explicit Haar-preserving group multiplications to permute the coordinates.

The existing theorem `chi_re_sq_integral_one`, proved through the fundamental
Schur calculation, is retained as an independent consistency check.
-/

noncomputable section

open Complex MeasureTheory
open scoped BigOperators

namespace YangMills.SU2ThetaPrism

private abbrev finTwoZero : Fin 2 := 0
private abbrev finTwoOne : Fin 2 := 1

/-- Left multiplication by this element multiplies the first row by `I` and
the second row by `-I`. -/
private def quaternionI : SU2 :=
  YangMills.ClayCore.twoSiteSU finTwoZero finTwoOne (by decide)

/-- Right multiplication by this element swaps the two columns, with the
sign convention needed to keep determinant one. -/
private def quaternionJ : SU2 :=
  YangMills.ClayCore.signedSwapSU finTwoZero finTwoOne (by decide)

/-- The four real coordinates of the first SU(2) row.  For the standard
quaternion matrix `[[a+bi, c+di],[-c+di,a-bi]]`, these are `a,b,c,d`. -/
def quaternionCoordinate : Fin 4 → SU2 → ℝ :=
  ![fun g => (g.val finTwoZero finTwoZero).re,
    fun g => (g.val finTwoZero finTwoZero).im,
    fun g => (g.val finTwoZero finTwoOne).re,
    fun g => (g.val finTwoZero finTwoOne).im]

@[simp] theorem quaternionCoordinate_zero (g : SU2) :
    quaternionCoordinate 0 g = (g.val finTwoZero finTwoZero).re := rfl

@[simp] theorem quaternionCoordinate_one (g : SU2) :
    quaternionCoordinate 1 g = (g.val finTwoZero finTwoZero).im := rfl

@[simp] theorem quaternionCoordinate_two (g : SU2) :
    quaternionCoordinate 2 g = (g.val finTwoZero finTwoOne).re := rfl

@[simp] theorem quaternionCoordinate_three (g : SU2) :
    quaternionCoordinate 3 g = (g.val finTwoZero finTwoOne).im := rfl

private theorem su2_star_val_eq_adjugate (g : SU2) :
    (star g.val : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.adjugate g.val := by
  have hgRight := congrArg Subtype.val (mul_inv_cancel g)
  change g.val * (g⁻¹).val = (1 : Matrix (Fin 2) (Fin 2) ℂ) at hgRight
  have hgDet : Matrix.det g.val = 1 := g.property.2
  have hadjLeft : Matrix.adjugate g.val * g.val = 1 := by
    rw [Matrix.adjugate_mul, hgDet, one_smul]
  have hinv : (g⁻¹).val = Matrix.adjugate g.val := by
    calc
      (g⁻¹).val = 1 * (g⁻¹).val := by simp
      _ = (Matrix.adjugate g.val * g.val) * (g⁻¹).val := by rw [hadjLeft]
      _ = Matrix.adjugate g.val * (g.val * (g⁻¹).val) :=
        Matrix.mul_assoc _ _ _
      _ = Matrix.adjugate g.val := by rw [hgRight, Matrix.mul_one]
  change (g⁻¹).val = Matrix.adjugate g.val
  exact hinv

private theorem su2_entry_one_one (g : SU2) :
    g.val finTwoOne finTwoOne = star (g.val finTwoZero finTwoZero) := by
  have h := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => M finTwoZero finTwoZero)
    (su2_star_val_eq_adjugate g)
  rw [Matrix.adjugate_fin_two] at h
  simpa [Matrix.star_apply] using h.symm

private theorem quaternionI_first_row (g : SU2) (c : Fin 2) :
    ((quaternionI * g).val) finTwoZero c =
      Complex.I * g.val finTwoZero c := by
  change
    (YangMills.ClayCore.twoSitePhase finTwoZero finTwoOne * g.val)
        finTwoZero c = Complex.I * g.val finTwoZero c
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp [YangMills.ClayCore.twoSitePhase,
    YangMills.ClayCore.twoSiteVec]

private theorem quaternionJ_column_zero (g : SU2) (r : Fin 2) :
    ((g * quaternionJ).val) r finTwoZero = g.val r finTwoOne := by
  exact YangMills.ClayCore.signedSwapSU_apply_right
    finTwoZero finTwoOne (by decide) g r

private theorem chi_re_eq_two_mul_coordinate_zero (g : SU2) :
    (chi g).re = 2 * quaternionCoordinate 0 g := by
  rw [chi, Matrix.trace_fin_two, su2_entry_one_one]
  simp [Complex.star_def]
  ring

private theorem quaternionCoordinate_continuous (k : Fin 4) :
    Continuous (quaternionCoordinate k) := by
  fin_cases k
  · exact Complex.continuous_re.comp
      (YangMills.ClayCore.continuous_val_entry finTwoZero finTwoZero)
  · exact Complex.continuous_im.comp
      (YangMills.ClayCore.continuous_val_entry finTwoZero finTwoZero)
  · exact Complex.continuous_re.comp
      (YangMills.ClayCore.continuous_val_entry finTwoZero finTwoOne)
  · exact Complex.continuous_im.comp
      (YangMills.ClayCore.continuous_val_entry finTwoZero finTwoOne)

private theorem quaternionCoordinate_sq_integrable (k : Fin 4) :
    Integrable (fun g : SU2 => quaternionCoordinate k g ^ 2) haarSU2 :=
  ((quaternionCoordinate_continuous k).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The four quaternion coordinates lie pointwise on the unit sphere. -/
theorem quaternionCoordinate_sq_sum (g : SU2) :
    ∑ k : Fin 4, quaternionCoordinate k g ^ 2 = 1 := by
  have hrow := YangMills.ClayCore.unitary_row_normSq_sum g finTwoZero
  rw [Fin.sum_univ_two] at hrow
  simp only [Complex.normSq_apply] at hrow
  rw [Fin.sum_univ_four]
  simp only [quaternionCoordinate_zero, quaternionCoordinate_one,
    quaternionCoordinate_two, quaternionCoordinate_three]
  nlinarith

private theorem coordinate_zero_integral_eq_one :
    (∫ g : SU2, quaternionCoordinate 0 g ^ 2 ∂haarSU2) =
      ∫ g : SU2, quaternionCoordinate 1 g ^ 2 ∂haarSU2 := by
  let f : SU2 → ℝ := fun g => quaternionCoordinate 0 g ^ 2
  calc
    (∫ g : SU2, quaternionCoordinate 0 g ^ 2 ∂haarSU2) =
        ∫ g : SU2, f (quaternionI * g) ∂haarSU2 :=
      (integral_mul_left_eq_self (μ := haarSU2) f quaternionI).symm
    _ = ∫ g : SU2, quaternionCoordinate 1 g ^ 2 ∂haarSU2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun g => by
        simp only [f]
        rw [show quaternionCoordinate 0 (quaternionI * g) =
            -quaternionCoordinate 1 g by
          simp only [quaternionCoordinate_zero, quaternionCoordinate_one]
          rw [quaternionI_first_row]
          simp]
        ring

private theorem coordinate_zero_integral_eq_two :
    (∫ g : SU2, quaternionCoordinate 0 g ^ 2 ∂haarSU2) =
      ∫ g : SU2, quaternionCoordinate 2 g ^ 2 ∂haarSU2 := by
  let f : SU2 → ℝ := fun g => quaternionCoordinate 0 g ^ 2
  calc
    (∫ g : SU2, quaternionCoordinate 0 g ^ 2 ∂haarSU2) =
        ∫ g : SU2, f (g * quaternionJ) ∂haarSU2 :=
      (integral_mul_right_eq_self (μ := haarSU2) f quaternionJ).symm
    _ = ∫ g : SU2, quaternionCoordinate 2 g ^ 2 ∂haarSU2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun g => by
        simp only [f, quaternionCoordinate_zero, quaternionCoordinate_two]
        rw [quaternionJ_column_zero]

private theorem coordinate_one_integral_eq_three :
    (∫ g : SU2, quaternionCoordinate 1 g ^ 2 ∂haarSU2) =
      ∫ g : SU2, quaternionCoordinate 3 g ^ 2 ∂haarSU2 := by
  let f : SU2 → ℝ := fun g => quaternionCoordinate 1 g ^ 2
  calc
    (∫ g : SU2, quaternionCoordinate 1 g ^ 2 ∂haarSU2) =
        ∫ g : SU2, f (g * quaternionJ) ∂haarSU2 :=
      (integral_mul_right_eq_self (μ := haarSU2) f quaternionJ).symm
    _ = ∫ g : SU2, quaternionCoordinate 3 g ^ 2 ∂haarSU2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun g => by
        simp only [f, quaternionCoordinate_one, quaternionCoordinate_three]
        rw [quaternionJ_column_zero]

/-- Quaternion-coordinate proof of `integral chi^2 = 1`.  The only analytic
input is normalized Haar invariance; no Schur moment theorem occurs in this
derivation. -/
theorem chi_re_sq_integral_one_quaternion :
    (∫ g : SU2, (chi g).re ^ 2 ∂haarSU2) = 1 := by
  let I0 : ℝ := ∫ g : SU2, quaternionCoordinate 0 g ^ 2 ∂haarSU2
  have hIntegralSum :
      (∫ g : SU2, ∑ k : Fin 4, quaternionCoordinate k g ^ 2 ∂haarSU2) =
        ∑ k : Fin 4, ∫ g : SU2, quaternionCoordinate k g ^ 2 ∂haarSU2 := by
    exact integral_finset_sum Finset.univ fun k _ =>
      quaternionCoordinate_sq_integrable k
  have hSumOne :
      (∑ k : Fin 4, ∫ g : SU2, quaternionCoordinate k g ^ 2 ∂haarSU2) = 1 := by
    calc
      (∑ k : Fin 4, ∫ g : SU2, quaternionCoordinate k g ^ 2 ∂haarSU2) =
          ∫ g : SU2, ∑ k : Fin 4, quaternionCoordinate k g ^ 2 ∂haarSU2 :=
        hIntegralSum.symm
      _ = ∫ _g : SU2, (1 : ℝ) ∂haarSU2 := by
        apply integral_congr_ae
        exact ae_of_all _ quaternionCoordinate_sq_sum
      _ = 1 := by simp
  have hAllEqual :
      (∑ k : Fin 4, ∫ g : SU2, quaternionCoordinate k g ^ 2 ∂haarSU2) =
        4 * I0 := by
    rw [Fin.sum_univ_four]
    dsimp only [I0]
    rw [← coordinate_zero_integral_eq_one,
      ← coordinate_zero_integral_eq_two,
      ← coordinate_one_integral_eq_three,
      ← coordinate_zero_integral_eq_one]
    ring
  have hI0 : I0 = 1 / 4 := by
    linarith [hSumOne, hAllEqual]
  have hfun : (fun g : SU2 => (chi g).re ^ 2) =
      fun g : SU2 => 4 * quaternionCoordinate 0 g ^ 2 := by
    funext g
    rw [chi_re_eq_two_mul_coordinate_zero]
    ring
  rw [hfun, integral_const_mul]
  change 4 * I0 = 1
  rw [hI0]
  norm_num

/-- The quaternion calculation and the pre-existing Schur calculation both
produce the same normalized value.  Keeping both conjuncts prevents the
consistency gate from silently replacing either derivation. -/
theorem chi_re_sq_quaternion_schur_consistency :
    ((∫ g : SU2, (chi g).re ^ 2 ∂haarSU2) = 1) ∧
      ((∫ g : SU2, (chi g).re ^ 2 ∂haarSU2) = 1) :=
  ⟨chi_re_sq_integral_one_quaternion, chi_re_sq_integral_one⟩

end YangMills.SU2ThetaPrism

end
