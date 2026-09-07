import YangMills.RG.ShiftedCoerciveResolvent

/-!
# The inverse-square-root resolvent difference kernel

For positive `t`, this module packages the exact operator-valued integrand

`t⁻¹ᐟ² ((K₁+tI)⁻¹ - (K₀+tI)⁻¹)`

and rewrites it using the second-resolvent identity.  The terminal estimate is
the pointwise majorant needed for the later Bochner integral:

`‖kernel(t)‖ ≤ t⁻¹ᐟ² (c₁+t)⁻¹ ‖K₀-K₁‖ (c₀+t)⁻¹`.

No claim identifying its integral with a square-root difference is made here.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace
open Set

noncomputable section

/-- Shifted resolvent with the shift clamped to the nonnegative half-line. -/
noncomputable def nonnegativeShiftedResolvent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hK : IsCoerciveCLM K c) (t : ℝ) :
    E →L[ℝ] E :=
  shiftedResolventOfIsCoerciveCLM K hc hK (max t 0)
    (le_max_right t 0)

theorem nonnegativeShiftedResolvent_eq_of_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hK : IsCoerciveCLM K c) (t : ℝ) (ht : 0 ≤ t) :
    nonnegativeShiftedResolvent K hc hK t =
      shiftedResolventOfIsCoerciveCLM K hc hK t ht := by
  simp only [nonnegativeShiftedResolvent, max_eq_left ht]

/-- The clamped shifted resolvent is continuous on the positive half-line. -/
theorem continuousOn_nonnegativeShiftedResolvent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hK : IsCoerciveCLM K c) :
    ContinuousOn
      (nonnegativeShiftedResolvent K hc hK)
      (Ioi 0) := by
  have hring :=
    (continuousOn_ringInverse_shiftedPrecisionCLM K hc hK).mono
      Ioi_subset_Ici_self
  apply hring.congr
  intro t ht
  rw [nonnegativeShiftedResolvent_eq_of_nonneg K hc hK t ht.le,
    shiftedResolventOfIsCoerciveCLM_eq_ringInverse]

/-- Unnormalised inverse-square-root difference kernel. -/
noncomputable def inverseSqrtResolventDifferenceKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K₀ K₁ : E →L[ℝ] E)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hK₀ : IsCoerciveCLM K₀ c₀)
    (hK₁ : IsCoerciveCLM K₁ c₁)
    (t : ℝ) :
    E →L[ℝ] E :=
  (Real.sqrt t)⁻¹ •
    (nonnegativeShiftedResolvent K₁ hc₁ hK₁ t -
      nonnegativeShiftedResolvent K₀ hc₀ hK₀ t)

/-- Exact pointwise factorization of the kernel in the `C₁ (K₀-K₁) C₀`
ordering. -/
theorem inverseSqrtResolventDifferenceKernel_eq_factorized
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K₀ K₁ : E →L[ℝ] E)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hK₀ : IsCoerciveCLM K₀ c₀)
    (hK₁ : IsCoerciveCLM K₁ c₁)
    (t : ℝ) (ht : 0 ≤ t) :
    inverseSqrtResolventDifferenceKernel
        K₀ K₁ hc₀ hc₁ hK₀ hK₁ t =
      (Real.sqrt t)⁻¹ •
        (shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht).comp
          ((K₀ - K₁).comp
            (shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht)) := by
  rw [inverseSqrtResolventDifferenceKernel,
    nonnegativeShiftedResolvent_eq_of_nonneg K₁ hc₁ hK₁ t ht,
    nonnegativeShiftedResolvent_eq_of_nonneg K₀ hc₀ hK₀ t ht,
    shiftedResolvent_sub_eq_comp_precision_sub_comp
      K₀ K₁ hc₀ hc₁ hK₀ hK₁ t ht]

/-- Pointwise two-margin norm majorant for the inverse-square-root kernel. -/
theorem norm_inverseSqrtResolventDifferenceKernel_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K₀ K₁ : E →L[ℝ] E)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hK₀ : IsCoerciveCLM K₀ c₀)
    (hK₁ : IsCoerciveCLM K₁ c₁)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖inverseSqrtResolventDifferenceKernel
        K₀ K₁ hc₀ hc₁ hK₀ hK₁ t‖ ≤
      (Real.sqrt t)⁻¹ *
        ((c₁ + t)⁻¹ * ‖K₀ - K₁‖ * (c₀ + t)⁻¹) := by
  unfold inverseSqrtResolventDifferenceKernel
  rw [nonnegativeShiftedResolvent_eq_of_nonneg K₁ hc₁ hK₁ t ht,
    nonnegativeShiftedResolvent_eq_of_nonneg K₀ hc₀ hK₀ t ht,
    norm_smul]
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg t))]
  exact mul_le_mul_of_nonneg_left
    (norm_shiftedResolvent_sub_le
      K₀ K₁ hc₀ hc₁ hK₀ hK₁ t ht)
    (inv_nonneg.mpr (Real.sqrt_nonneg t))

/-- The inverse-square-root difference kernel is continuous away from the
integrable singularity at `t = 0`. -/
theorem continuousOn_inverseSqrtResolventDifferenceKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K₀ K₁ : E →L[ℝ] E)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hK₀ : IsCoerciveCLM K₀ c₀)
    (hK₁ : IsCoerciveCLM K₁ c₁) :
    ContinuousOn
      (inverseSqrtResolventDifferenceKernel
        K₀ K₁ hc₀ hc₁ hK₀ hK₁)
      (Ioi 0) := by
  unfold inverseSqrtResolventDifferenceKernel
  apply ContinuousOn.smul
  · apply ContinuousOn.inv₀
    · exact Real.continuous_sqrt.continuousOn
    · intro t ht
      exact (Real.sqrt_pos.2 ht).ne'
  · exact
      (continuousOn_nonnegativeShiftedResolvent K₁ hc₁ hK₁).sub
        (continuousOn_nonnegativeShiftedResolvent K₀ hc₀ hK₀)

end

end YangMills.RG
