/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixWalkExpansion

/-!
# Exact support and local transitions for the CMP99 patched walk

The ordered chart expansion initially sums all chart words.  This file begins
the source-facing sparsification.  A chart defect is exterior flux generated
by applying the finite-range global precision to a vector supported in the
chart's enlarged domain.  Hence it vanishes at a target farther than the
precision range from every bond of that domain.

Consequently two consecutive chart defects compose to zero whenever the core
read by the left defect is range-separated from the enlarged domain of the
right defect.  This is an exact support theorem, not an exponentially small
replacement and not an assumed successor relation.

Honest scope: bounding the number of non-separated charts uniformly requires
the concrete source chart geometry and remains open.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- A target set is beyond the finite interaction range of a source set. -/
def CMP99PhysicalRangeSeparated
    {d N : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (targetSet sourceSet : Finset (PhysicalBond d N)) : Prop :=
  ∀ target, target ∈ targetSet → ∀ source, source ∈ sourceSet →
    R < dist target source

/-- Projection support gives pointwise vanishing off the supporting set. -/
theorem physicalCochain_apply_eq_zero_of_projection_eq_self
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N))
    (y : PhysicalGaugeOneCochain d N Nc)
    (hy : physicalBondProjection S y = y)
    {target : PhysicalBond d N} (htarget : target ∉ S) :
    y target = 0 := by
  calc
    y target = physicalBondProjection S y target :=
      congrArg (fun z : PhysicalGaugeOneCochain d N Nc => z target) hy.symm
    _ = 0 := physicalBondProjection_apply_not_mem S htarget y

/-- A finite-range operator applied to a vector supported in `S` vanishes at
any target farther than the range from every source bond in `S`. -/
theorem physicalFiniteRange_apply_eq_zero_of_supported
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (R : ℕ)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (S : Finset (PhysicalBond d N))
    (y : PhysicalGaugeOneCochain d N Nc)
    (hy : physicalBondProjection S y = y)
    (target : PhysicalBond d N)
    (hfar : ∀ source, source ∈ S → R < dist target source) :
    K y target = 0 := by
  have hdecomp :
      y = ∑ source, singlePhysicalBondCochain
        (d := d) (N := N) (Nc := Nc) source (y source) := by
    exact (sum_singlePhysicalBondCochain_eq y).symm
  rw [hdecomp, map_sum, physicalCochain_sum_apply]
  apply Finset.sum_eq_zero
  intro source _hsource
  by_cases hs : source ∈ S
  · exact hrange source target (y source) (hfar source hs)
  · have hzero : y source = 0 :=
      physicalCochain_apply_eq_zero_of_projection_eq_self S y hy hs
    have hsingle :
        singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) source (y source) = 0 := by
      apply PiLp.ext
      intro q
      simp [hzero, singlePhysicalBondCochain]
    rw [hsingle, map_zero, PiLp.zero_apply]

/-- The local covariance fed from a core contained in the enlarged chart is
supported exactly in that enlarged chart. -/
theorem cmp99LocalizedCovariance_core_supported
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    {core enlarged : Finset (PhysicalBond d N)}
    (hsub : core ⊆ enlarged)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (x : PhysicalGaugeOneCochain d N Nc) :
    physicalBondProjection enlarged
        (cmp99LocalizedPhysicalCovariance K enlarged hc hmass hK
          (physicalBondProjection core x)) =
      cmp99LocalizedPhysicalCovariance K enlarged hc hmass hK
        (physicalBondProjection core x) := by
  let C := cmp99LocalizedPhysicalCovariance K enlarged hc hmass hK
  let P : PhysicalEndomorphism d N Nc := physicalBondProjection enlarged
  let Pcore : PhysicalEndomorphism d N Nc := physicalBondProjection core
  have hPPcore : P.comp Pcore = Pcore :=
    physicalBondProjection_comp_of_subset hsub
  have hCP : C.comp P = P.comp C :=
    cmp99LocalizedPhysicalCovariance_comm_projection K enlarged hc hmass hK
  have hPcore : P (Pcore x) = Pcore x := by
    exact DFunLike.congr_fun hPPcore x
  have hcomm := DFunLike.congr_fun hCP (Pcore x)
  simp only [ContinuousLinearMap.comp_apply] at hcomm
  rw [← hcomm, hPcore]

/-- A single chart defect vanishes at targets beyond the finite range of the
whole enlarged chart. -/
theorem cmp99SinglePhysicalParametrixDefect_apply_eq_zero_of_far
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    {core enlarged : Finset (PhysicalBond d N)}
    (hsub : core ⊆ enlarged)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) {R : ℕ}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (x : PhysicalGaugeOneCochain d N Nc)
    (target : PhysicalBond d N)
    (hfar : ∀ source, source ∈ enlarged → R < dist target source) :
    ((K - cmp99LocalizedPhysicalPrecision K enlarged mass).comp
        ((cmp99LocalizedPhysicalCovariance K enlarged hc hmass hK).comp
          (physicalBondProjection core))) x target = 0 := by
  rw [cmp99SinglePhysicalParametrixDefect_eq_exterior_flux
    K hsub hc hmass hK]
  simp only [ContinuousLinearMap.comp_apply]
  let y := cmp99LocalizedPhysicalCovariance K enlarged hc hmass hK
    (physicalBondProjection core x)
  have hy : physicalBondProjection enlarged y = y :=
    cmp99LocalizedCovariance_core_supported K hsub hc hmass hK x
  have hKy : K y target = 0 :=
    physicalFiniteRange_apply_eq_zero_of_supported
      K dist R hrange enlarged y hy target hfar
  change K y target - physicalBondProjection enlarged (K y) target = 0
  by_cases ht : target ∈ enlarged
  · rw [physicalBondProjection_apply_mem enlarged ht, sub_self]
  · rw [physicalBondProjection_apply_not_mem enlarged ht, sub_zero, hKy]

/-- If `leftCore` is range-separated from `rightEnlarged`, the right defect
has zero projection onto the core read by the next (left) defect. -/
theorem physicalBondProjection_comp_singleDefect_eq_zero_of_rangeSeparated
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (leftCore rightCore rightEnlarged : Finset (PhysicalBond d N))
    (hrightSub : rightCore ⊆ rightEnlarged)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) {R : ℕ}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hsep : CMP99PhysicalRangeSeparated dist R leftCore rightEnlarged)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    (physicalBondProjection leftCore : PhysicalEndomorphism d N Nc).comp
        ((K - cmp99LocalizedPhysicalPrecision K rightEnlarged mass).comp
          ((cmp99LocalizedPhysicalCovariance K rightEnlarged hc hmass hK).comp
            (physicalBondProjection rightCore))) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro target
  change
    physicalBondProjection leftCore
        (((K - cmp99LocalizedPhysicalPrecision K rightEnlarged mass).comp
          ((cmp99LocalizedPhysicalCovariance K rightEnlarged hc hmass hK).comp
            (physicalBondProjection rightCore))) x) target = 0
  by_cases ht : target ∈ leftCore
  · rw [ContinuousLinearMap.comp_apply,
      physicalBondProjection_apply_mem leftCore ht]
    exact cmp99SinglePhysicalParametrixDefect_apply_eq_zero_of_far
      K hrightSub dist hrange hc hmass hK x target (hsep target ht)
  · rw [ContinuousLinearMap.comp_apply,
      physicalBondProjection_apply_not_mem leftCore ht]

/-- Exact sparsity of the ordered patched walk: separated consecutive charts
give a zero continuation product. -/
theorem cmp99PhysicalPatchContinuation_mul_eq_zero_of_rangeSeparated
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (hsub : ∀ i, i ∈ charts → core i ⊆ enlarged i)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) {R : ℕ}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (left right : ↥charts)
    (hsep : CMP99PhysicalRangeSeparated dist R (core left) (enlarged right)) :
    cmp99PhysicalPatchContinuation
        charts K enlarged core hc hmass hK left *
      cmp99PhysicalPatchContinuation
        charts K enlarged core hc hmass hK right = 0 := by
  let Dleft : PhysicalEndomorphism d N Nc :=
    (K - cmp99LocalizedPhysicalPrecision K (enlarged left) mass).comp
      ((cmp99LocalizedPhysicalCovariance K (enlarged left) hc hmass hK).comp
        (physicalBondProjection (core left)))
  let Dright : PhysicalEndomorphism d N Nc :=
    (K - cmp99LocalizedPhysicalPrecision K (enlarged right) mass).comp
      ((cmp99LocalizedPhysicalCovariance K (enlarged right) hc hmass hK).comp
        (physicalBondProjection (core right)))
  have hproj :
      (physicalBondProjection (core left) : PhysicalEndomorphism d N Nc).comp
          Dright = 0 :=
    physicalBondProjection_comp_singleDefect_eq_zero_of_rangeSeparated
      K (core left) (core right) (enlarged right)
      (hsub right right.property) dist hrange hsep hc hmass hK
  have hcomp : Dleft.comp Dright = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change (K - cmp99LocalizedPhysicalPrecision K (enlarged left) mass)
      (cmp99LocalizedPhysicalCovariance K (enlarged left) hc hmass hK
        (physicalBondProjection (core left) (Dright x))) = 0
    have hx := DFunLike.congr_fun hproj x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at hx
    rw [hx, map_zero, map_zero]
  apply ContinuousLinearMap.ext
  intro x
  change (-Dleft) (-Dright x) = 0
  have hx := DFunLike.congr_fun hcomp x
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    map_neg, neg_neg, ContinuousLinearMap.zero_apply] using hx

end

end YangMills.RG
