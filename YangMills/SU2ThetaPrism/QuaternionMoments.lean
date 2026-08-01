import YangMills.SU2ThetaPrism.Analysis
import YangMills.ClayCore.SchurDiagPhase
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

/-- The unit quaternion `(1+i+j+k)/2`.  Its adjoint action cyclically
permutes the three imaginary quaternion coordinates. -/
private def quaternionHalf : ℂ := ((1 / 2 : ℝ) : ℂ)

@[simp]
private theorem star_quaternionHalf : star quaternionHalf = quaternionHalf := by
  simp [quaternionHalf]

private def quaternionCycleMat : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![(quaternionHalf * ((1 : ℂ) + Complex.I)),
      (quaternionHalf * ((1 : ℂ) + Complex.I))],
    ![(quaternionHalf * ((-1 : ℂ) + Complex.I)),
      (quaternionHalf * ((1 : ℂ) - Complex.I))]]

private def quaternionCycle : SU2 := by
  refine ⟨quaternionCycleMat, ?_⟩
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    have hstarHalf :
        (starRingEnd ℂ) (((1 / 2 : ℝ) : ℂ)) = (((1 / 2 : ℝ) : ℂ)) := by
      simpa only [quaternionHalf] using star_quaternionHalf
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quaternionCycleMat, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_apply] <;>
      unfold quaternionHalf <;>
      rw [hstarHalf] <;>
      ring_nf <;>
      norm_num [Complex.I_sq]
  · rw [Matrix.det_fin_two]
    simp [quaternionCycleMat]
    unfold quaternionHalf
    ring_nf
    norm_num [Complex.I_sq]

private def quarterTurnAngles : Fin 2 → ℝ :=
  ![Real.pi / 4, -(Real.pi / 4)]

private theorem quarterTurnAngles_sum : ∑ k, quarterTurnAngles k = 0 := by
  rw [Fin.sum_univ_two]
  simp [quarterTurnAngles]

/-- The unit quaternion `(1+i)/sqrt(2)`.  Left multiplication rotates the
`(x0,x1)` plane by a full angle `pi/4`. -/
private def quaternionQuarterTurn : SU2 :=
  YangMills.ClayCore.diagPhaseSU quarterTurnAngles quarterTurnAngles_sum

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

private theorem su2_entry_one_zero (g : SU2) :
    g.val finTwoOne finTwoZero = -star (g.val finTwoZero finTwoOne) := by
  have h := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => M finTwoOne finTwoZero)
    (su2_star_val_eq_adjugate g)
  rw [Matrix.adjugate_fin_two] at h
  have hneg := congrArg Neg.neg h
  simpa [Matrix.star_apply] using hneg.symm

private theorem integral_conjugate_eq_self (f : SU2 → ℝ) (q : SU2) :
    (∫ g : SU2, f (q * g * q⁻¹) ∂haarSU2) = ∫ g : SU2, f g ∂haarSU2 := by
  calc
    (∫ g : SU2, f (q * g * q⁻¹) ∂haarSU2) =
        ∫ g : SU2, f (q * g) ∂haarSU2 :=
      by simpa only [mul_assoc] using
        integral_mul_right_eq_self (μ := haarSU2) (fun g => f (q * g)) q⁻¹
    _ = ∫ g : SU2, f g ∂haarSU2 :=
      integral_mul_left_eq_self (μ := haarSU2) f q

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

private theorem quaternionQuarterTurn_first_row (g : SU2) (c : Fin 2) :
    ((quaternionQuarterTurn * g).val) finTwoZero c =
      ((((Real.sqrt 2 / 2 : ℝ) : ℂ) +
          ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I) *
        g.val finTwoZero c) := by
  change
    ((YangMills.ClayCore.diagPhaseSU quarterTurnAngles quarterTurnAngles_sum * g).val)
      finTwoZero c = _
  rw [YangMills.ClayCore.diagPhaseSU_apply_entry]
  simp only [YangMills.ClayCore.diagPhaseVec_apply, quarterTurnAngles,
    Matrix.cons_val_zero]
  congr 1
  rw [show Complex.I * ((Real.pi / 4 : ℝ) : ℂ) =
      ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by ring]
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]

private theorem quaternionCoordinate_zero_quarterTurn (g : SU2) :
    quaternionCoordinate 0 (quaternionQuarterTurn * g) =
      (Real.sqrt 2 / 2) *
        (quaternionCoordinate 0 g - quaternionCoordinate 1 g) := by
  simp only [quaternionCoordinate_zero, quaternionCoordinate_one,
    quaternionQuarterTurn_first_row]
  simp [Complex.mul_re]
  ring

private theorem quaternionJ_conj_entry_zero_zero (g : SU2) :
    ((quaternionJ * g * quaternionJ⁻¹).val) finTwoZero finTwoZero =
      star (g.val finTwoZero finTwoZero) := by
  change
    ((YangMills.ClayCore.signedSwapMat finTwoZero finTwoOne * g.val *
        star (YangMills.ClayCore.signedSwapMat finTwoZero finTwoOne))
      finTwoZero finTwoZero) = _
  apply Complex.ext <;>
    simp [YangMills.ClayCore.signedSwapMat, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.star_apply, su2_entry_one_one,
      Complex.star_def]

private theorem quaternionJ_conj_coordinates_zero_one (g : SU2) :
    quaternionCoordinate 0 (quaternionJ * g * quaternionJ⁻¹) =
        quaternionCoordinate 0 g ∧
      quaternionCoordinate 1 (quaternionJ * g * quaternionJ⁻¹) =
        -quaternionCoordinate 1 g := by
  simp only [quaternionCoordinate_zero, quaternionCoordinate_one,
    quaternionJ_conj_entry_zero_zero]
  simp [Complex.star_def]

private theorem quaternionCycle_conj_entry_zero_zero (g : SU2) :
    ((quaternionCycle * g * quaternionCycle⁻¹).val) finTwoZero finTwoZero =
      ((g.val finTwoZero finTwoZero).re : ℂ) +
        ((g.val finTwoZero finTwoOne).im : ℂ) * Complex.I := by
  change ((quaternionCycleMat * g.val * star quaternionCycleMat)
      finTwoZero finTwoZero) = _
  apply Complex.ext <;>
    simp [quaternionCycleMat, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_apply, su2_entry_one_one, su2_entry_one_zero,
      Complex.I_sq] <;>
    unfold quaternionHalf <;>
    norm_num <;>
    ring

private theorem quaternionCycle_conj_entry_zero_one (g : SU2) :
    ((quaternionCycle * g * quaternionCycle⁻¹).val) finTwoZero finTwoOne =
      ((g.val finTwoZero finTwoZero).im : ℂ) +
        ((g.val finTwoZero finTwoOne).re : ℂ) * Complex.I := by
  change ((quaternionCycleMat * g.val * star quaternionCycleMat)
      finTwoZero finTwoOne) = _
  apply Complex.ext <;>
    simp [quaternionCycleMat, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_apply, su2_entry_one_one, su2_entry_one_zero,
      Complex.I_sq] <;>
    unfold quaternionHalf <;>
    norm_num <;>
    ring

private theorem quaternionCycle_coordinates (g : SU2) :
    quaternionCoordinate 0 (quaternionCycle * g * quaternionCycle⁻¹) =
        quaternionCoordinate 0 g ∧
      quaternionCoordinate 1 (quaternionCycle * g * quaternionCycle⁻¹) =
        quaternionCoordinate 3 g ∧
      quaternionCoordinate 2 (quaternionCycle * g * quaternionCycle⁻¹) =
        quaternionCoordinate 1 g ∧
      quaternionCoordinate 3 (quaternionCycle * g * quaternionCycle⁻¹) =
        quaternionCoordinate 2 g := by
  simp only [quaternionCoordinate_zero, quaternionCoordinate_one,
    quaternionCoordinate_two, quaternionCoordinate_three,
    quaternionCycle_conj_entry_zero_zero,
    quaternionCycle_conj_entry_zero_one]
  simp

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

private theorem quaternionCoordinate_pow_integrable (k : Fin 4) (n : ℕ) :
    Integrable (fun g : SU2 => quaternionCoordinate k g ^ n) haarSU2 :=
  ((quaternionCoordinate_continuous k).pow n).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem quaternionCoordinate_pow_mul_pow_integrable
    (i j : Fin 4) (m n : ℕ) :
    Integrable (fun g : SU2 =>
      quaternionCoordinate i g ^ m * quaternionCoordinate j g ^ n) haarSU2 :=
  (((quaternionCoordinate_continuous i).pow m).mul
      ((quaternionCoordinate_continuous j).pow n)).integrable_of_hasCompactSupport
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

private theorem coordinate_zero_fourth_integral_eq_one :
    (∫ g : SU2, quaternionCoordinate 0 g ^ 4 ∂haarSU2) =
      ∫ g : SU2, quaternionCoordinate 1 g ^ 4 ∂haarSU2 := by
  let f : SU2 → ℝ := fun g => quaternionCoordinate 0 g ^ 4
  calc
    (∫ g : SU2, quaternionCoordinate 0 g ^ 4 ∂haarSU2) =
        ∫ g : SU2, f (quaternionI * g) ∂haarSU2 :=
      (integral_mul_left_eq_self (μ := haarSU2) f quaternionI).symm
    _ = ∫ g : SU2, quaternionCoordinate 1 g ^ 4 ∂haarSU2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun g => by
        simp only [f]
        rw [show quaternionCoordinate 0 (quaternionI * g) =
            -quaternionCoordinate 1 g by
          simp only [quaternionCoordinate_zero, quaternionCoordinate_one]
          rw [quaternionI_first_row]
          simp]
        ring

private theorem coordinate_zero_cube_mul_one_integral_zero :
    (∫ g : SU2,
      quaternionCoordinate 0 g ^ 3 * quaternionCoordinate 1 g ∂haarSU2) = 0 := by
  let f : SU2 → ℝ := fun g =>
    quaternionCoordinate 0 g ^ 3 * quaternionCoordinate 1 g
  have hinv := integral_conjugate_eq_self f quaternionJ
  have hneg :
      (∫ g : SU2, f (quaternionJ * g * quaternionJ⁻¹) ∂haarSU2) =
        -(∫ g : SU2, f g ∂haarSU2) := by
    calc
      (∫ g : SU2, f (quaternionJ * g * quaternionJ⁻¹) ∂haarSU2) =
          ∫ g : SU2, -f g ∂haarSU2 := by
        apply integral_congr_ae
        exact ae_of_all _ fun g => by
          rcases quaternionJ_conj_coordinates_zero_one g with ⟨h0, h1⟩
          simp only [f, h0, h1]
          ring
      _ = -(∫ g : SU2, f g ∂haarSU2) := by rw [integral_neg]
  change (∫ g : SU2, f g ∂haarSU2) = 0
  linarith

private theorem coordinate_zero_mul_one_cube_integral_zero :
    (∫ g : SU2,
      quaternionCoordinate 0 g * quaternionCoordinate 1 g ^ 3 ∂haarSU2) = 0 := by
  let f : SU2 → ℝ := fun g =>
    quaternionCoordinate 0 g * quaternionCoordinate 1 g ^ 3
  have hinv := integral_conjugate_eq_self f quaternionJ
  have hneg :
      (∫ g : SU2, f (quaternionJ * g * quaternionJ⁻¹) ∂haarSU2) =
        -(∫ g : SU2, f g ∂haarSU2) := by
    calc
      (∫ g : SU2, f (quaternionJ * g * quaternionJ⁻¹) ∂haarSU2) =
          ∫ g : SU2, -f g ∂haarSU2 := by
        apply integral_congr_ae
        exact ae_of_all _ fun g => by
          rcases quaternionJ_conj_coordinates_zero_one g with ⟨h0, h1⟩
          simp only [f, h0, h1]
          ring
      _ = -(∫ g : SU2, f g ∂haarSU2) := by rw [integral_neg]
  change (∫ g : SU2, f g ∂haarSU2) = 0
  linarith

private theorem coordinate_zero_one_mixed_integral_eq_three :
    (∫ g : SU2,
      quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 1 g ^ 2 ∂haarSU2) =
        ∫ g : SU2,
          quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 3 g ^ 2 ∂haarSU2 := by
  let f : SU2 → ℝ := fun g =>
    quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 1 g ^ 2
  calc
    (∫ g : SU2,
        quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 1 g ^ 2 ∂haarSU2) =
        ∫ g : SU2, f (quaternionCycle * g * quaternionCycle⁻¹) ∂haarSU2 :=
      (integral_conjugate_eq_self f quaternionCycle).symm
    _ = ∫ g : SU2,
        quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 3 g ^ 2 ∂haarSU2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun g => by
        rcases quaternionCycle_coordinates g with ⟨h0, h1, _h2, _h3⟩
        simp only [f, h0, h1]

private theorem coordinate_zero_three_mixed_integral_eq_two :
    (∫ g : SU2,
      quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 3 g ^ 2 ∂haarSU2) =
        ∫ g : SU2,
          quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 2 g ^ 2 ∂haarSU2 := by
  let f : SU2 → ℝ := fun g =>
    quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 3 g ^ 2
  calc
    (∫ g : SU2,
        quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 3 g ^ 2 ∂haarSU2) =
        ∫ g : SU2, f (quaternionCycle * g * quaternionCycle⁻¹) ∂haarSU2 :=
      (integral_conjugate_eq_self f quaternionCycle).symm
    _ = ∫ g : SU2,
        quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 2 g ^ 2 ∂haarSU2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun g => by
        rcases quaternionCycle_coordinates g with ⟨h0, _h1, _h2, h3⟩
        simp only [f, h0, h3]

private theorem coordinate_zero_sq_integral_eq_quarter :
    (∫ g : SU2, quaternionCoordinate 0 g ^ 2 ∂haarSU2) = 1 / 4 := by
  have hchi := chi_re_sq_integral_one_quaternion
  have hfun : (fun g : SU2 => (chi g).re ^ 2) =
      fun g : SU2 => 4 * quaternionCoordinate 0 g ^ 2 := by
    funext g
    rw [chi_re_eq_two_mul_coordinate_zero]
    ring
  rw [hfun, integral_const_mul] at hchi
  linarith

private theorem coordinate_zero_fourth_add_three_mixed_eq_quarter :
    (∫ g : SU2, quaternionCoordinate 0 g ^ 4 ∂haarSU2) +
        3 * (∫ g : SU2,
          quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 1 g ^ 2 ∂haarSU2) =
      1 / 4 := by
  have hIntegralSum :
      (∫ g : SU2,
          ∑ k : Fin 4,
            quaternionCoordinate 0 g ^ 2 * quaternionCoordinate k g ^ 2
          ∂haarSU2) =
        ∑ k : Fin 4, ∫ g : SU2,
          quaternionCoordinate 0 g ^ 2 * quaternionCoordinate k g ^ 2 ∂haarSU2 := by
    exact integral_finset_sum Finset.univ fun k _ =>
      quaternionCoordinate_pow_mul_pow_integrable 0 k 2 2
  have hPoint (g : SU2) :
      (∑ k : Fin 4,
        quaternionCoordinate 0 g ^ 2 * quaternionCoordinate k g ^ 2) =
        quaternionCoordinate 0 g ^ 2 := by
    rw [← Finset.mul_sum, quaternionCoordinate_sq_sum]
    ring
  have hSum :
      (∑ k : Fin 4, ∫ g : SU2,
        quaternionCoordinate 0 g ^ 2 * quaternionCoordinate k g ^ 2 ∂haarSU2) =
        1 / 4 := by
    calc
      (∑ k : Fin 4, ∫ g : SU2,
          quaternionCoordinate 0 g ^ 2 * quaternionCoordinate k g ^ 2 ∂haarSU2) =
          ∫ g : SU2,
            ∑ k : Fin 4,
              quaternionCoordinate 0 g ^ 2 * quaternionCoordinate k g ^ 2
            ∂haarSU2 := hIntegralSum.symm
      _ = ∫ g : SU2, quaternionCoordinate 0 g ^ 2 ∂haarSU2 := by
        apply integral_congr_ae
        exact ae_of_all _ hPoint
      _ = 1 / 4 := coordinate_zero_sq_integral_eq_quarter
  rw [Fin.sum_univ_four] at hSum
  have h00 :
      (∫ g : SU2,
        quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 0 g ^ 2 ∂haarSU2) =
        ∫ g : SU2, quaternionCoordinate 0 g ^ 4 ∂haarSU2 := by
    apply integral_congr_ae
    exact ae_of_all _ fun g => by ring
  rw [h00, ← coordinate_zero_three_mixed_integral_eq_two,
    ← coordinate_zero_one_mixed_integral_eq_three] at hSum
  linarith

private theorem coordinate_zero_fourth_eq_three_mixed :
    (∫ g : SU2, quaternionCoordinate 0 g ^ 4 ∂haarSU2) =
      3 * (∫ g : SU2,
        quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 1 g ^ 2 ∂haarSU2) := by
  let f : SU2 → ℝ := fun g => quaternionCoordinate 0 g ^ 4
  have hQuarter :
      (∫ g : SU2, quaternionCoordinate 0 g ^ 4 ∂haarSU2) =
        ∫ g : SU2,
          ((Real.sqrt 2 / 2) *
            (quaternionCoordinate 0 g - quaternionCoordinate 1 g)) ^ 4
          ∂haarSU2 := by
    calc
      (∫ g : SU2, quaternionCoordinate 0 g ^ 4 ∂haarSU2) =
          ∫ g : SU2, f (quaternionQuarterTurn * g) ∂haarSU2 :=
        (integral_mul_left_eq_self (μ := haarSU2) f quaternionQuarterTurn).symm
      _ = ∫ g : SU2,
          ((Real.sqrt 2 / 2) *
            (quaternionCoordinate 0 g - quaternionCoordinate 1 g)) ^ 4
          ∂haarSU2 := by
        apply integral_congr_ae
        exact ae_of_all _ fun g => by
          simp only [f, quaternionCoordinate_zero_quarterTurn]
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtFourth : (Real.sqrt 2 / 2) ^ 4 = (1 / 4 : ℝ) := by
    calc
      (Real.sqrt 2 / 2) ^ 4 = (Real.sqrt 2) ^ 4 / 2 ^ 4 := div_pow _ _ _
      _ = ((Real.sqrt 2) ^ 2) ^ 2 / 2 ^ 4 := by ring
      _ = 1 / 4 := by rw [hsqrt]; norm_num
  have hPointExpand (g : SU2) :
      ((Real.sqrt 2 / 2) *
          (quaternionCoordinate 0 g - quaternionCoordinate 1 g)) ^ 4 =
        (1 / 4 : ℝ) *
          (quaternionCoordinate 0 g ^ 4 +
            (-4) * (quaternionCoordinate 0 g ^ 3 * quaternionCoordinate 1 g) +
            6 * (quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 1 g ^ 2) +
            (-4) * (quaternionCoordinate 0 g * quaternionCoordinate 1 g ^ 3) +
            quaternionCoordinate 1 g ^ 4) := by
    calc
      ((Real.sqrt 2 / 2) *
          (quaternionCoordinate 0 g - quaternionCoordinate 1 g)) ^ 4 =
          (Real.sqrt 2 / 2) ^ 4 *
            (quaternionCoordinate 0 g - quaternionCoordinate 1 g) ^ 4 := by ring
      _ = _ := by rw [hsqrtFourth]; ring
  have hA := quaternionCoordinate_pow_integrable 0 4
  have hC : Integrable (fun g : SU2 =>
      quaternionCoordinate 0 g ^ 3 * quaternionCoordinate 1 g) haarSU2 := by
    simpa using quaternionCoordinate_pow_mul_pow_integrable 0 1 3 1
  have hB := quaternionCoordinate_pow_mul_pow_integrable 0 1 2 2
  have hD : Integrable (fun g : SU2 =>
      quaternionCoordinate 0 g * quaternionCoordinate 1 g ^ 3) haarSU2 := by
    simpa using quaternionCoordinate_pow_mul_pow_integrable 0 1 1 3
  have hA1 := quaternionCoordinate_pow_integrable 1 4
  have hCscaled := hC.const_mul (-4 : ℝ)
  have hBscaled := hB.const_mul (6 : ℝ)
  have hDscaled := hD.const_mul (-4 : ℝ)
  have hAC : Integrable (fun g : SU2 =>
      quaternionCoordinate 0 g ^ 4 +
        (-4) * (quaternionCoordinate 0 g ^ 3 * quaternionCoordinate 1 g))
      haarSU2 := hA.add hCscaled
  have hACB : Integrable (fun g : SU2 =>
      quaternionCoordinate 0 g ^ 4 +
          (-4) * (quaternionCoordinate 0 g ^ 3 * quaternionCoordinate 1 g) +
        6 * (quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 1 g ^ 2))
      haarSU2 := hAC.add hBscaled
  have hACBD : Integrable (fun g : SU2 =>
      quaternionCoordinate 0 g ^ 4 +
            (-4) * (quaternionCoordinate 0 g ^ 3 * quaternionCoordinate 1 g) +
          6 * (quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 1 g ^ 2) +
        (-4) * (quaternionCoordinate 0 g * quaternionCoordinate 1 g ^ 3))
      haarSU2 := hACB.add hDscaled
  have hExpanded :
      (∫ g : SU2,
          ((Real.sqrt 2 / 2) *
            (quaternionCoordinate 0 g - quaternionCoordinate 1 g)) ^ 4
          ∂haarSU2) =
        (1 / 4 : ℝ) *
          ((∫ g : SU2, quaternionCoordinate 0 g ^ 4 ∂haarSU2) +
            (-4) * (∫ g : SU2,
              quaternionCoordinate 0 g ^ 3 * quaternionCoordinate 1 g ∂haarSU2) +
            6 * (∫ g : SU2,
              quaternionCoordinate 0 g ^ 2 * quaternionCoordinate 1 g ^ 2 ∂haarSU2) +
            (-4) * (∫ g : SU2,
              quaternionCoordinate 0 g * quaternionCoordinate 1 g ^ 3 ∂haarSU2) +
            (∫ g : SU2, quaternionCoordinate 1 g ^ 4 ∂haarSU2)) := by
    rw [integral_congr_ae (ae_of_all _ hPointExpand), integral_const_mul]
    rw [integral_add hACBD hA1, integral_add hACB hDscaled,
      integral_add hAC hBscaled, integral_add hA hCscaled]
    rw [integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hExpanded, coordinate_zero_cube_mul_one_integral_zero,
    coordinate_zero_mul_one_cube_integral_zero,
    ← coordinate_zero_fourth_integral_eq_one] at hQuarter
  linarith

/-- Fourth fundamental-character moment from explicit quaternion-coordinate
Haar symmetries.  This proof uses neither Weyl integration nor Peter--Weyl. -/
theorem chi_re_fourth_integral_two_quaternion :
    (∫ g : SU2, (chi g).re ^ 4 ∂haarSU2) = 2 := by
  have hA :
      (∫ g : SU2, quaternionCoordinate 0 g ^ 4 ∂haarSU2) = 1 / 8 := by
    linarith [coordinate_zero_fourth_add_three_mixed_eq_quarter,
      coordinate_zero_fourth_eq_three_mixed]
  have hfun : (fun g : SU2 => (chi g).re ^ 4) =
      fun g : SU2 => 16 * quaternionCoordinate 0 g ^ 4 := by
    funext g
    rw [chi_re_eq_two_mul_coordinate_zero]
    ring
  rw [hfun, integral_const_mul, hA]
  norm_num

end YangMills.SU2ThetaPrism

end
