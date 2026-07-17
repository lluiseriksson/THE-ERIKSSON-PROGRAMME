import YangMills.RG.PhysicalExponentialKernelSchur

/-!
# CMP99 patched parametrix: localized-defect Neumann correction

The exact patched identity has the orientation

`K Ppatch = 1 + D`.

Once the exponentially localized defect satisfies `norm D < 1`, the correct
right inverse is therefore

`Ppatch * sum_n (-D)^n`.

This is a Neumann series in the localized patching defect, not in the global
precision or global resolvent.  The source-facing construction of the chart
geometry remains separate.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Neumann inverse of `1 + D`, written as the geometric series in `-D`. -/
noncomputable def cmp99PatchedDefectNeumannInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E) : E →L[ℝ] E :=
  ∑' n : ℕ, (-D) ^ n

theorem summable_cmp99PatchedDefectNeumannInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {D : E →L[ℝ] E} (hD : ‖D‖ < 1) :
    Summable (fun n : ℕ => (-D) ^ n) := by
  apply summable_geometric_of_norm_lt_one
  simpa using hD

/-- `(1 + D)` times its defect-Neumann inverse is the identity. -/
theorem one_add_comp_cmp99PatchedDefectNeumannInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (D : E →L[ℝ] E) (hD : ‖D‖ < 1) :
    (ContinuousLinearMap.id ℝ E + D).comp
        (cmp99PatchedDefectNeumannInverse D) =
      ContinuousLinearMap.id ℝ E := by
  change (1 + D) * (∑' n : ℕ, (-D) ^ n) = 1
  simpa [sub_neg_eq_add] using
    (mul_neg_geom_series (-D) (by simpa using hD))

/-- The defect-Neumann inverse is also a left inverse. -/
theorem cmp99PatchedDefectNeumannInverse_comp_one_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (D : E →L[ℝ] E) (hD : ‖D‖ < 1) :
    (cmp99PatchedDefectNeumannInverse D).comp
        (ContinuousLinearMap.id ℝ E + D) =
      ContinuousLinearMap.id ℝ E := by
  change (∑' n : ℕ, (-D) ^ n) * (1 + D) = 1
  simpa [sub_neg_eq_add] using
    (geom_series_mul_neg (-D) (by simpa using hD))

/-- Correct an arbitrary right parametrix by its localized defect series. -/
noncomputable def cmp99CorrectedParametrix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P D : E →L[ℝ] E) : E →L[ℝ] E :=
  P.comp (cmp99PatchedDefectNeumannInverse D)

/-- Exact right inverse produced from `K P = 1 + D` and `norm D < 1`. -/
theorem comp_cmp99CorrectedParametrix_eq_id
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (K P D : E →L[ℝ] E)
    (hKP : K.comp P = ContinuousLinearMap.id ℝ E + D)
    (hD : ‖D‖ < 1) :
    K.comp (cmp99CorrectedParametrix P D) =
      ContinuousLinearMap.id ℝ E := by
  rw [cmp99CorrectedParametrix, ← ContinuousLinearMap.comp_assoc, hKP]
  exact one_add_comp_cmp99PatchedDefectNeumannInverse D hD

/-- Exponential kernel decay plus a uniform exponential row sum turns the
patched defect into a contraction under the visible scalar condition
`A * Ssum < 1`. -/
theorem cmp99PatchedPhysicalParametrixDefect_norm_lt_one_of_exponential
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    {A rate Ssum : ℝ} (hSsum : 0 ≤ Ssum)
    (hD : PhysicalCovarianceExponentialKernelBound
      (cmp99PatchedPhysicalParametrixDefect
        charts K enlarged core hc hmass hK)
      dist A rate)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(rate * (dist x z : ℝ))) ≤ Ssum)
    (hsmall : A * Ssum < 1) :
    ‖cmp99PatchedPhysicalParametrixDefect
      charts K enlarged core hc hmass hK‖ < 1 :=
  (physicalOpNorm_le_of_exponentialKernelBound
    dist hsymm hSsum hD hsum).trans_lt hsmall

/-- Physical corrected patched covariance. -/
noncomputable def cmp99CorrectedPatchedPhysicalCovariance
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) : PhysicalEndomorphism d N Nc :=
  cmp99CorrectedParametrix
    (cmp99PatchedPhysicalParametrix charts K enlarged core hc hmass hK)
    (cmp99PatchedPhysicalParametrixDefect
      charts K enlarged core hc hmass hK)

/-- The corrected physical patched covariance is an exact right inverse once
the core partition and defect contraction are available. -/
theorem comp_cmp99CorrectedPatchedPhysicalCovariance_eq_id
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hpartition : CMP99PhysicalCorePartition charts core)
    (hD : ‖cmp99PatchedPhysicalParametrixDefect
      charts K enlarged core hc hmass hK‖ < 1) :
    K.comp
        (cmp99CorrectedPatchedPhysicalCovariance
          charts K enlarged core hc hmass hK) =
      ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc) := by
  apply comp_cmp99CorrectedParametrix_eq_id
  · exact comp_cmp99PatchedPhysicalParametrix_of_corePartition
      charts K enlarged core hc hmass hK hpartition
  · exact hD

end

end YangMills.RG
