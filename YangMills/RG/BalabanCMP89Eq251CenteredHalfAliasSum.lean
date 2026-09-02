import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import YangMills.RG.BalabanCMP89Eq251ExpandedAliasGeometry
import YangMills.RG.BalabanCMP89Eq251HalfAliasTailIntegral
import YangMills.RG.BalabanCMP89Eq251MultidimensionalAliasProduct
import YangMills.RG.BalabanCMP89Eq251OneDimensionalAliasSeries

/-!
# PRE-VALIDATION: the centered finite alias sum at exponent one half

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.

This scratch leaf combines the half-tail integral estimate with the literal
centered alias window.  Its target retains the sharp square-root scale in the
number of aliases; no cardinality bound is allowed in this bridge.
-/

namespace YangMills.RG

noncomputable section

/-- At exponent `1/2`, the literal reciprocal-lattice weight is bounded by
the shifted integer half-power. -/
theorem cmp89Eq251OneDimensionalAliasWeight_half_le_shiftedAbs
    (m : ℤ) :
    cmp89Eq251OneDimensionalAliasWeight (1 / 2 : ℝ) m ≤
      (1 + |(m : ℝ)|) ^ (-(1 / 2 : ℝ)) := by
  have hscale : |(m : ℝ)| ≤ |2 * Real.pi * (m : ℝ)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
      abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_gt_three, abs_nonneg (m : ℝ)]
  have hbase : 1 + |(m : ℝ)| ≤ 1 + |2 * Real.pi * (m : ℝ)| :=
    add_le_add_right hscale 1
  rw [cmp89Eq251OneDimensionalAliasWeight, one_div,
    ← Real.rpow_neg (by positivity : 0 ≤ 1 + |2 * Real.pi * (m : ℝ)|) (1 / 2 : ℝ)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)

/-- Every printed centered alias window is contained in the symmetric
integer interval of radius `N`. -/
theorem cmp89Eq245CenteredAliasIntegers_subset_Icc_radius (N : ℕ) :
    cmp89Eq245CenteredAliasIntegers N ⊆
      Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  intro m hm
  rw [Finset.mem_Icc]
  have hwidth :=
    two_mul_abs_int_le_of_mem_cmp89Eq245CenteredAliasIntegers hm
  have hlower : -|m| ≤ m := neg_abs_le m
  have hupper : m ≤ |m| := le_abs_self m
  constructor <;> omega

/-- The literal centered one-dimensional alias sum at exponent `1/2` grows
at most like the square root of the window cardinality. -/
theorem cmp89Eq251CenteredOneDimensionalAliasSum_half_le
    (N : ℕ) :
    cmp89Eq251CenteredOneDimensionalAliasSum N (1 / 2 : ℝ) ≤
      4 * Real.sqrt (N + 1) := by
  let weight : ℤ → ℝ :=
    fun m => cmp89Eq251OneDimensionalAliasWeight (1 / 2 : ℝ) m
  let tail : ℝ := ∑ i ∈ Finset.range N,
    (1 + ((i + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))
  have heven : Function.Even weight := by
    intro m
    simp [weight, cmp89Eq251OneDimensionalAliasWeight]
  have hwindow :
      cmp89Eq251CenteredOneDimensionalAliasSum N (1 / 2 : ℝ) ≤
        ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), weight m := by
    rw [cmp89Eq251CenteredOneDimensionalAliasSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (cmp89Eq245CenteredAliasIntegers_subset_Icc_radius N)
      (fun m _ _ => cmp89Eq251OneDimensionalAliasWeight_nonneg _ m)
  have hrange :
      (∑ m ∈ Finset.range (N + 1), weight m) ≤ 1 + tail := by
    rw [Finset.sum_range_succ']
    have htail :
        (∑ i ∈ Finset.range N, weight (i + 1)) ≤ tail := by
      exact Finset.sum_le_sum fun i _ => by
        have hi : 0 ≤ (i : ℝ) + 1 := by positivity
        simpa [weight, abs_of_nonneg hi]
          using cmp89Eq251OneDimensionalAliasWeight_half_le_shiftedAbs
            ((i + 1 : ℕ) : ℤ)
    have h0 : weight 0 = 1 := by
      simp [weight, cmp89Eq251OneDimensionalAliasWeight]
    have h0Nat : weight ((0 : ℕ) : ℤ) = 1 := by simpa using h0
    have htailNat :
        (∑ i ∈ Finset.range N, weight ((i + 1 : ℕ) : ℤ)) ≤ tail := by
      simpa using htail
    rw [h0Nat]
    linarith
  have htailIntegral :
      tail ≤ ∫ x in (0 : ℝ)..N, (1 + x) ^ (-(1 / 2 : ℝ)) := by
    simpa [tail] using cmp89Eq251HalfAliasPositiveTail_le_integral N
  have htailBound : tail ≤ 2 * (Real.sqrt (N + 1) - 1) := by
    rw [← cmp89Eq251HalfAliasIntegral_eq N]
    exact htailIntegral
  have hfull :
      (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), weight m) ≤
        1 + 2 * tail := by
    rw [Finset.sum_Icc_of_even_eq_range heven]
    have h0 : weight 0 = 1 := by
      simp [weight, cmp89Eq251OneDimensionalAliasWeight]
    rw [h0, nsmul_eq_mul]
    have hdouble := mul_le_mul_of_nonneg_left hrange (by norm_num : (0 : ℝ) ≤ 2)
    calc
      (2 : ℝ) * (∑ m ∈ Finset.range (N + 1), weight m) - 1
          ≤ 2 * (1 + tail) - 1 := sub_le_sub_right hdouble 1
      _ = 1 + 2 * tail := by ring
  have hsqrt : 1 ≤ Real.sqrt (N + 1) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  calc
    cmp89Eq251CenteredOneDimensionalAliasSum N (1 / 2 : ℝ)
        ≤ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), weight m := hwindow
    _ ≤ 1 + 2 * tail := hfull
    _ ≤ 1 + 4 * (Real.sqrt (N + 1) - 1) := by nlinarith
    _ ≤ 4 * Real.sqrt (N + 1) := by nlinarith

/-- Exact four-dimensional factorization turns the one-dimensional
square-root estimate into a quadratic bound, with the visible constant
`4^4 = 256`. -/
theorem cmp89Eq251CenteredFourDimensionalAliasSum_half_le
    (N : ℕ) :
    cmp89Eq251CenteredMultidimensionalAliasSum 4 N (1 / 2 : ℝ) ≤
      256 * (N + 1 : ℝ) ^ 2 := by
  rw [cmp89Eq251CenteredMultidimensionalAliasSum_eq_pow]
  have hsumNonneg :
      0 ≤ cmp89Eq251CenteredOneDimensionalAliasSum N (1 / 2 : ℝ) := by
    exact Finset.sum_nonneg fun m _ =>
      cmp89Eq251OneDimensionalAliasWeight_nonneg _ m
  have hpow := pow_le_pow_left₀ hsumNonneg
    (cmp89Eq251CenteredOneDimensionalAliasSum_half_le N) 4
  have hsqrt : Real.sqrt (N + 1) ^ 2 = (N + 1 : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  calc
    cmp89Eq251CenteredOneDimensionalAliasSum N (1 / 2 : ℝ) ^ 4
        ≤ (4 * Real.sqrt (N + 1)) ^ 4 := hpow
    _ = 256 * (Real.sqrt (N + 1) ^ 2) ^ 2 := by ring
    _ = 256 * (N + 1 : ℝ) ^ 2 := by rw [hsqrt]

end

end YangMills.RG
