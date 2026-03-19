import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanFieldSpace
import YangMills.ClayCore.BalabanRG.SmallFieldLargeFieldSplit

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# BalabanFieldDecomposition — Layer 15C (v0.9.4)

Pointwise decomposition of a field configuration φ into small-field and
large-field parts, using `fieldThreshold β = exp(-β/2)`.

This layer is independent of ActivityFamily.
It works directly with φ : BalabanLatticeSite d k → ℝ.
-/

noncomputable section

/-- Small-field projection: keep φ(x) on small sites, zero elsewhere. -/
def smallFieldProjection {d k : ℕ} (β : ℝ) (φ : BalabanLatticeSite d k → ℝ) :
    BalabanLatticeSite d k → ℝ :=
  fun x => if |φ x| < fieldThreshold β then φ x else 0

/-- Large-field projection: keep φ(x) on large sites, zero elsewhere. -/
def largeFieldProjection {d k : ℕ} (β : ℝ) (φ : BalabanLatticeSite d k → ℝ) :
    BalabanLatticeSite d k → ℝ :=
  fun x => if fieldThreshold β ≤ |φ x| then φ x else 0

/-- The field splits as small + large. 0 sorrys. -/
theorem small_add_large_eq {d k : ℕ} (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ) :
    φ = fun x => smallFieldProjection β φ x + largeFieldProjection β φ x := by
  funext x
  unfold smallFieldProjection largeFieldProjection
  by_cases hsmall : |φ x| < fieldThreshold β
  · have hlarge : ¬ fieldThreshold β ≤ |φ x| := by linarith
    simp [hsmall, hlarge]
  · have hlarge : fieldThreshold β ≤ |φ x| := le_of_not_gt hsmall
    simp [hsmall, hlarge]

/-- Small projection is supported in the small-field region. 0 sorrys. -/
theorem smallFieldProjection_supportedIn {d k : ℕ} (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ) :
    balabanSupportedIn (smallFieldProjection β φ)
      (balabanSmallFieldRegion φ (fieldThreshold β)) := by
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxU, hxnz⟩
  have hsmall : |φ x| < fieldThreshold β := by
    by_contra h
    have hge : fieldThreshold β ≤ |φ x| := le_of_not_gt h
    simp [smallFieldProjection, hge] at hxnz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hsmall⟩

/-- Large projection is supported in the large-field region. 0 sorrys. -/
theorem largeFieldProjection_supportedIn {d k : ℕ} (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ) :
    balabanSupportedIn (largeFieldProjection β φ)
      (balabanLargeFieldRegion φ (fieldThreshold β)) := by
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxU, hxnz⟩
  have hlarge : fieldThreshold β ≤ |φ x| := by
    by_contra h
    have hlt : |φ x| < fieldThreshold β := lt_of_not_ge h
    simp [largeFieldProjection, hlt] at hxnz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hlarge⟩

/-- Pointwise disjointness: one projection vanishes at every site. 0 sorrys. -/
theorem small_large_pointwise_mul_zero {d k : ℕ} (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ) (x : BalabanLatticeSite d k) :
    smallFieldProjection β φ x * largeFieldProjection β φ x = 0 := by
  unfold smallFieldProjection largeFieldProjection
  by_cases hsmall : |φ x| < fieldThreshold β
  · simp [hsmall, not_le.mpr hsmall]
  · simp [hsmall, le_of_not_gt hsmall]

/-- Support disjointness. 0 sorrys. -/
theorem small_support_disjoint_large {d k : ℕ} (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ) :
    Disjoint (balabanFieldSupport (smallFieldProjection β φ))
      (balabanFieldSupport (largeFieldProjection β φ)) := by
  apply Finset.disjoint_left.mpr
  intro x hxS hxL
  rcases Finset.mem_filter.mp hxS with ⟨_, hxSne⟩
  rcases Finset.mem_filter.mp hxL with ⟨_, hxLne⟩
  have hzero : smallFieldProjection β φ x * largeFieldProjection β φ x = 0 :=
    small_large_pointwise_mul_zero β φ x
  have hs : smallFieldProjection β φ x ≠ 0 := hxSne
  have hl : largeFieldProjection β φ x ≠ 0 := hxLne
  exact mul_ne_zero hs hl hzero

/-- On a small field, the small projection equals φ. 0 sorrys. -/
theorem smallFieldProjection_eq_self_of_small {d N_c : ℕ} [NeZero N_c] {k : ℕ} {β : ℝ}
    (φ : BalabanLatticeSite d k → ℝ)
    (hS : SmallFieldPredicateField d N_c k β φ) :
    smallFieldProjection β φ = φ := by
  funext x
  unfold smallFieldProjection
  simp [((smallField_iff φ).mp hS) x]

/-- On a small field, the large projection is zero. 0 sorrys. -/
theorem largeFieldProjection_eq_zero_of_small {d N_c : ℕ} [NeZero N_c] {k : ℕ} {β : ℝ}
    (φ : BalabanLatticeSite d k → ℝ)
    (hS : SmallFieldPredicateField d N_c k β φ) :
    largeFieldProjection β φ = fun _ => 0 := by
  funext x
  unfold largeFieldProjection
  have hlt : |φ x| < fieldThreshold β := ((smallField_iff φ).mp hS) x
  simp [not_le.mpr hlt]

end

end YangMills.ClayCore
