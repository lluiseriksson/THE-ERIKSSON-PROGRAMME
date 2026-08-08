import YangMills.RG.BalabanCMP99LocalizedParametrix

/-!
# CMP99 localized parametrix: finite range and Combes--Thomas decay

This file proves that the compressed precision constructed in
`BalabanCMP99LocalizedParametrix` inherits finite range and an explicit kernel
budget.  The generic coercive Combes--Thomas ladder therefore supplies
exponential decay of its exact local covariance.

This remains the local-inverse brick of a source-faithful parametrix.  It does
not yet form a partition of unity, compare overlapping local inverses, or
prove exponential smallness of the patched boundary defect.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

theorem physicalBondProjection_single_mem
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N))
    (source : PhysicalBond d N) (v : SUNLieCoord Nc)
    (hs : source ∈ S) :
    physicalBondProjection S
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) source v) =
      singlePhysicalBondCochain source v := by
  apply PiLp.ext
  intro target
  by_cases hts : target = source
  · subst target
    exact physicalBondProjection_apply_mem S hs _
  · rw [singlePhysicalBondCochain_of_ne (v := v) hts]
    by_cases ht : target ∈ S
    · rw [physicalBondProjection_apply_mem S ht]
      exact singlePhysicalBondCochain_of_ne v hts
    · rw [physicalBondProjection_apply_not_mem S ht]

theorem physicalBondProjection_single_not_mem
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N))
    (source : PhysicalBond d N) (v : SUNLieCoord Nc)
    (hs : source ∉ S) :
    physicalBondProjection S
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) source v) =
      0 := by
  apply PiLp.ext
  intro target
  by_cases ht : target ∈ S
  · rw [physicalBondProjection_apply_mem S ht]
    exact singlePhysicalBondCochain_of_ne v (fun h => hs (h ▸ ht))
  · rw [physicalBondProjection_apply_not_mem S ht, PiLp.zero_apply]

/-- Compression by the same coordinate projection on both sides preserves
finite range. -/
theorem physicalCovarianceFiniteRange_projection_comp_projection
    {d N Nc : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (S : Finset (PhysicalBond d N))
    (K : PhysicalEndomorphism d N Nc) {R : ℕ}
    (hK : PhysicalCovarianceFiniteRange K dist R) :
    PhysicalCovarianceFiniteRange
      ((physicalBondProjection S).comp (K.comp (physicalBondProjection S)))
      dist R := by
  intro source target v hfar
  by_cases hs : source ∈ S
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      physicalBondProjection_single_mem S source v hs]
    by_cases ht : target ∈ S
    · rw [physicalBondProjection_apply_mem (b := target) S ht]
      exact hK source target v hfar
    · exact physicalBondProjection_apply_not_mem (b := target) S ht _
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      physicalBondProjection_single_not_mem S source v hs, map_zero,
      map_zero, PiLp.zero_apply]

/-- Compression by coordinate projections does not enlarge a constant
pointwise kernel budget. -/
theorem physicalCovarianceKernelBound_projection_comp_projection
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N))
    (K : PhysicalEndomorphism d N Nc) {M : ℝ}
    (hK : PhysicalCovarianceKernelBound K (fun _ _ => M)) :
    PhysicalCovarianceKernelBound
      ((physicalBondProjection S).comp (K.comp (physicalBondProjection S)))
      (fun _ _ => M) := by
  intro source target v
  by_cases hs : source ∈ S
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      physicalBondProjection_single_mem S source v hs]
    by_cases ht : target ∈ S
    · rw [physicalBondProjection_apply_mem (b := target) S ht]
      exact hK source target v
    · rw [physicalBondProjection_apply_not_mem (b := target) S ht, norm_zero]
      exact le_trans (norm_nonneg _) (hK source target v)
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      physicalBondProjection_single_not_mem S source v hs, map_zero,
      map_zero, PiLp.zero_apply, norm_zero]
    exact le_trans (norm_nonneg _) (hK source target v)

/-- The complementary coordinate projection is ultralocal. -/
theorem physicalBondComplementProjection_finiteRange
    {d N Nc : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hself : ∀ p, dist p p = 0)
    (S : Finset (PhysicalBond d N)) :
    PhysicalCovarianceFiniteRange
      (physicalBondComplementProjection S : PhysicalEndomorphism d N Nc)
      dist 0 := by
  intro source target v hfar
  have hne : target ≠ source := by
    intro h
    subst target
    simpa [hself source] using hfar
  by_cases hs : source ∈ S
  · rw [physicalBondComplementProjection, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply,
      physicalBondProjection_single_mem S source v hs, sub_self,
      PiLp.zero_apply]
  · rw [physicalBondComplementProjection, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply,
      physicalBondProjection_single_not_mem S source v hs, sub_zero]
    exact singlePhysicalBondCochain_of_ne v hne

/-- The complementary coordinate projection has unit pointwise kernel
budget. -/
theorem physicalBondComplementProjection_kernelBound
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N)) :
    PhysicalCovarianceKernelBound
      (physicalBondComplementProjection S : PhysicalEndomorphism d N Nc)
      (fun _ _ => 1) := by
  intro source target v
  by_cases hs : source ∈ S
  · rw [physicalBondComplementProjection, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply,
      physicalBondProjection_single_mem S source v hs, sub_self,
      PiLp.zero_apply, norm_zero]
    positivity
  · rw [physicalBondComplementProjection, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply,
      physicalBondProjection_single_not_mem S source v hs, sub_zero]
    by_cases hts : target = source
    · subst target
      rw [singlePhysicalBondCochain_self]
      simp
    · rw [singlePhysicalBondCochain_of_ne (v := v) hts, norm_zero]
      positivity

/-- The localized precision has the same range as `K`: the exterior mass is
ultralocal. -/
theorem cmp99LocalizedPhysicalPrecision_finiteRange
    {d N Nc : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hself : ∀ p, dist p p = 0)
    (K : PhysicalEndomorphism d N Nc)
    (S : Finset (PhysicalBond d N)) (mass : ℝ) {R : ℕ}
    (hK : PhysicalCovarianceFiniteRange K dist R) :
    PhysicalCovarianceFiniteRange
      (cmp99LocalizedPhysicalPrecision K S mass) dist R := by
  apply physicalCovarianceFiniteRange_add dist
  · exact physicalCovarianceFiniteRange_projection_comp_projection
      dist S K hK
  · exact physicalCovarianceFiniteRange_smul dist mass
      (physicalCovarianceFiniteRange_mono dist (Nat.zero_le R)
        (physicalBondComplementProjection_finiteRange dist hself S))

/-- Explicit constant kernel budget for the localized precision. -/
theorem cmp99LocalizedPhysicalPrecision_kernelBound
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S : Finset (PhysicalBond d N)) (mass : ℝ) {M : ℝ}
    (hK : PhysicalCovarianceKernelBound K (fun _ _ => M)) :
    PhysicalCovarianceKernelBound
      (cmp99LocalizedPhysicalPrecision K S mass)
      (fun _ _ => M + |mass|) := by
  have hproj := physicalCovarianceKernelBound_projection_comp_projection S K hK
  have hcomp := physicalBondComplementProjection_kernelBound
    (Nc := Nc) S
  have hmass := physicalCovarianceKernelBound_smul mass hcomp
  have hadd := physicalCovarianceKernelBound_add hproj hmass
  simpa [cmp99LocalizedPhysicalPrecision] using hadd

/-- Combes--Thomas decay of the exact local covariance from the explicit
localized kernel and range budgets. -/
theorem cmp99LocalizedPhysicalCovariance_exponentialKernelBound
    {d N Nc : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    (hself : ∀ p, dist p p = 0)
    (K : PhysicalEndomorphism d N Nc)
    (S : Finset (PhysicalBond d N))
    {c mass M θ : ℝ} {R NR : ℕ}
    (hc : 0 < c) (hmass : 0 < mass) (hM : 0 ≤ M)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hcoer : IsCoerciveCLM K c)
    (hθ : 0 < θ)
    (hbudget : (M + |mass|) *
      (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ min c mass / 2) :
    PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K S hc hmass hcoer)
      dist (2 / min c mass) θ := by
  exact physicalCovariance_exponentialKernelBound_of_coercive
    dist hsymm htri hself hθ
    (add_nonneg hM (abs_nonneg mass)) (lt_min hc hmass) hNR
    (cmp99LocalizedPhysicalPrecision_finiteRange
      dist hself K S mass hrange)
    (cmp99LocalizedPhysicalPrecision_kernelBound K S mass hbound)
    (isCoerciveCLM_cmp99LocalizedPhysicalPrecision K S hcoer)
    (cmp99LocalizedPhysicalPrecision_comp_covariance K S hc hmass hcoer)
    hbudget

end

end YangMills.RG
