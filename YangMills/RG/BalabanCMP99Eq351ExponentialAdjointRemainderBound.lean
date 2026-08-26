import YangMills.RG.BalabanCMP99Eq351ExponentialAdjointRemainder
import YangMills.RG.NearLog

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# CMP99 (3.54): quadratic bound for the exponential-adjoint remainder

The nonlinear species is the remainder constructed in the preceding algebra
leaf, not an operator supplied by the caller.  Under the source-sized radius
`‖Y‖ ≤ 1/4`, this module proves the explicit bound

`‖R₂(Y) X‖ ≤ 8 ‖Y‖² ‖X‖`.

The constant eight is left visible because it is the coefficient printed in
the third contribution to (3.54).  The physical substitution
`Y = i eta A'(b)` and the Eq. (3.37) amplitude clause remain downstream.
-/

namespace YangMills.RG

noncomputable section

variable {A : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable [NormOneClass A]

/-- The scalar exponential-tail denominator costs at most `4/3` below the
source radius `1/4`. -/
theorem cmp99Eq351_expTailMajorant_le_four_thirds_sq
    {Y : A} (hY : ‖Y‖ ≤ (1 / 4 : ℝ)) :
    ‖Y‖ ^ 2 / (1 - ‖Y‖) ≤ (4 / 3 : ℝ) * ‖Y‖ ^ 2 := by
  have hden : 0 < 1 - ‖Y‖ := by
    have : ‖Y‖ < 1 := lt_of_le_of_lt hY (by norm_num)
    linarith
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg ‖Y‖]

/-- The inverse exponential factor remains bounded by `4/3` on the same
radius. -/
theorem cmp99Eq351_norm_exp_neg_le_four_thirds
    {Y : A} (hY : ‖Y‖ ≤ (1 / 4 : ℝ)) :
    ‖NormedSpace.exp (-Y)‖ ≤ (4 / 3 : ℝ) := by
  have hYlt : ‖Y‖ < 1 := lt_of_le_of_lt hY (by norm_num)
  have hneg : ‖-Y‖ < 1 := by simpa using hYlt
  have htail := norm_exp_sub_one_sub_self_le hneg
  have htail' :
      ‖NormedSpace.exp (-Y) - 1 - (-Y)‖ ≤
        (4 / 3 : ℝ) * ‖Y‖ ^ 2 := by
    calc
      ‖NormedSpace.exp (-Y) - 1 - (-Y)‖
          ≤ ‖-Y‖ ^ 2 / (1 - ‖-Y‖) := htail
      _ = ‖Y‖ ^ 2 / (1 - ‖Y‖) := by simp
      _ ≤ (4 / 3 : ℝ) * ‖Y‖ ^ 2 :=
        cmp99Eq351_expTailMajorant_le_four_thirds_sq hY
  have hexp :
      NormedSpace.exp (-Y) =
        (NormedSpace.exp (-Y) - 1 - (-Y)) + 1 + (-Y) := by
    abel
  rw [hexp]
  calc
    ‖(NormedSpace.exp (-Y) - 1 - (-Y)) + 1 + (-Y)‖
        ≤ ‖NormedSpace.exp (-Y) - 1 - (-Y)‖ + ‖(1 : A)‖ + ‖-Y‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add_right (norm_add_le _ _) _)
    _ ≤ (4 / 3 : ℝ) * ‖Y‖ ^ 2 + 1 + ‖Y‖ := by
      simpa using add_le_add_right (add_le_add_right htail' 1) ‖Y‖
    _ ≤ (4 / 3 : ℝ) := by
      nlinarith [sq_nonneg ‖Y‖, norm_nonneg Y]

/-- Quantitative form of the third species in CMP99 (3.51)--(3.54).  The
remainder is internally constructed, and the numerical constant is the
literal source coefficient. -/
theorem norm_cmp99Eq351ExponentialAdjointRemainderCLM_apply_le
    (Y X : A) (hY : ‖Y‖ ≤ (1 / 4 : ℝ)) :
    ‖cmp99Eq351ExponentialAdjointRemainderCLM Y X‖ ≤
      8 * ‖Y‖ ^ 2 * ‖X‖ := by
  have hYlt : ‖Y‖ < 1 := lt_of_le_of_lt hY (by norm_num)
  have hneg : ‖-Y‖ < 1 := by simpa using hYlt
  have htailY :
      ‖NormedSpace.exp Y - 1 - Y‖ ≤
        (4 / 3 : ℝ) * ‖Y‖ ^ 2 :=
    (norm_exp_sub_one_sub_self_le hYlt).trans
      (cmp99Eq351_expTailMajorant_le_four_thirds_sq hY)
  have htailNeg :
      ‖NormedSpace.exp (-Y) - 1 + Y‖ ≤
        (4 / 3 : ℝ) * ‖Y‖ ^ 2 := by
    have htail := norm_exp_sub_one_sub_self_le hneg
    calc
      ‖NormedSpace.exp (-Y) - 1 + Y‖ =
          ‖NormedSpace.exp (-Y) - 1 - (-Y)‖ := by congr 1 <;> abel
      _ ≤ ‖-Y‖ ^ 2 / (1 - ‖-Y‖) := htail
      _ = ‖Y‖ ^ 2 / (1 - ‖Y‖) := by simp
      _ ≤ (4 / 3 : ℝ) * ‖Y‖ ^ 2 :=
        cmp99Eq351_expTailMajorant_le_four_thirds_sq hY
  have honeY : ‖(1 : A) + Y‖ ≤ (5 / 4 : ℝ) := by
    calc
      ‖(1 : A) + Y‖ ≤ ‖(1 : A)‖ + ‖Y‖ := norm_add_le _ _
      _ ≤ (5 / 4 : ℝ) := by simpa using add_le_add_left hY 1
  have hexpNeg : ‖NormedSpace.exp (-Y)‖ ≤ (4 / 3 : ℝ) :=
    cmp99Eq351_norm_exp_neg_le_four_thirds hY
  have hdecomp :
      NormedSpace.exp Y * X * NormedSpace.exp (-Y) - X -
          (Y * X - X * Y) =
        (NormedSpace.exp Y - 1 - Y) * X * NormedSpace.exp (-Y) +
          (1 + Y) * X * (NormedSpace.exp (-Y) - 1 + Y) -
            Y * X * Y := by
    noncomm_ring
  rw [cmp99Eq351ExponentialAdjointRemainderCLM_apply, hdecomp]
  calc
    ‖(NormedSpace.exp Y - 1 - Y) * X * NormedSpace.exp (-Y) +
          (1 + Y) * X * (NormedSpace.exp (-Y) - 1 + Y) -
            Y * X * Y‖
        ≤ ‖(NormedSpace.exp Y - 1 - Y) * X * NormedSpace.exp (-Y)‖ +
            ‖(1 + Y) * X * (NormedSpace.exp (-Y) - 1 + Y)‖ +
              ‖Y * X * Y‖ := by
          exact (norm_sub_le _ _).trans
            (add_le_add_right (norm_add_le _ _) _)
    _ ≤ (((4 / 3 : ℝ) * ‖Y‖ ^ 2) * ‖X‖) * (4 / 3 : ℝ) +
          (((5 / 4 : ℝ) * ‖X‖) * ((4 / 3 : ℝ) * ‖Y‖ ^ 2)) +
            ((‖Y‖ * ‖X‖) * ‖Y‖) := by
      gcongr
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right
            ((norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right htailY (norm_nonneg X)))
            (norm_nonneg _)) |>.trans
          (mul_le_mul
            (mul_le_mul_of_nonneg_right htailY (norm_nonneg X))
            hexpNeg (norm_nonneg _) (by positivity))
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right
            ((norm_mul_le _ _).trans
              (mul_le_mul honeY (le_refl ‖X‖) (norm_nonneg X) (by positivity)))
            (norm_nonneg _)) |>.trans
          (mul_le_mul
            (mul_le_mul honeY (le_refl ‖X‖) (norm_nonneg X) (by positivity))
            htailNeg (norm_nonneg _) (by positivity))
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg Y))
    _ = (40 / 9 : ℝ) * ‖Y‖ ^ 2 * ‖X‖ := by ring
    _ ≤ 8 * ‖Y‖ ^ 2 * ‖X‖ := by
      gcongr
      norm_num

end

end YangMills.RG
