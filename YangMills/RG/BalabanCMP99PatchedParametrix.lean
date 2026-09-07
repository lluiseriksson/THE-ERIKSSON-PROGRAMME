import YangMills.RG.BalabanCMP99LocalizedParametrixDecay

/-!
# CMP99 finite patched parametrix: exact operator identity

This file performs the algebraic patching step after construction of the
localized covariances.  For core projections `P_i`, enlarged local domains
`S_i`, and local covariances `C_i = K[S_i,m]⁻¹`, define

`Ppatch = sum_i C_i P_i`.

If the core projections resolve the identity, then the global precision obeys
the exact identity

`K Ppatch = 1 + D`,

where

`D = sum_i (K - K[S_i,m]) C_i P_i`.

No norm estimate on `D` is asserted here.  Its collar support and exponential
smallness are the next physical obligations; in particular this module does
not replace the local construction by a global Neumann series.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- A single exact local inverse contributes its core projection plus the
global-to-local precision defect. -/
theorem comp_localInverse_comp_core_eq_core_add_defect
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K Klocal C P : E →L[ℝ] E)
    (hinv : Klocal.comp C = ContinuousLinearMap.id ℝ E) :
    K.comp (C.comp P) =
      P + (K - Klocal).comp (C.comp P) := by
  ext x
  have hx := DFunLike.congr_fun hinv (P x)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hx ⊢
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply]
  change K (C (P x)) = P x + (K (C (P x)) - Klocal (C (P x)))
  rw [hx]
  abel

/-- Finite patched physical parametrix built from local covariances on the
enlarged domains `enlarged i`, fed by the core coordinate projections
`core i`. -/
noncomputable def cmp99PatchedPhysicalParametrix
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) : PhysicalEndomorphism d N Nc :=
  ∑ i ∈ charts,
    (cmp99LocalizedPhysicalCovariance K (enlarged i) hc hmass hK).comp
      (physicalBondProjection (core i))

/-- Exact defect of the finite patched physical parametrix. -/
noncomputable def cmp99PatchedPhysicalParametrixDefect
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) : PhysicalEndomorphism d N Nc :=
  ∑ i ∈ charts,
    (K - cmp99LocalizedPhysicalPrecision K (enlarged i) mass).comp
      ((cmp99LocalizedPhysicalCovariance K (enlarged i) hc hmass hK).comp
        (physicalBondProjection (core i)))

/-- Exact patched-parametrix identity.  The only geometric input is that the
core coordinate projections form a finite resolution of the identity. -/
theorem comp_cmp99PatchedPhysicalParametrix
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hpartition :
      (∑ i ∈ charts, physicalBondProjection (core i)) =
        ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc)) :
    K.comp
        (cmp99PatchedPhysicalParametrix charts K enlarged core hc hmass hK) =
      ContinuousLinearMap.id ℝ _ +
        cmp99PatchedPhysicalParametrixDefect
          charts K enlarged core hc hmass hK := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [cmp99PatchedPhysicalParametrix,
    cmp99PatchedPhysicalParametrixDefect, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, map_sum, ContinuousLinearMap.add_apply]
  rw [← DFunLike.congr_fun hpartition x]
  simp only [ContinuousLinearMap.sum_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact DFunLike.congr_fun
    (comp_localInverse_comp_core_eq_core_add_defect
      K (cmp99LocalizedPhysicalPrecision K (enlarged i) mass)
        (cmp99LocalizedPhysicalCovariance K (enlarged i) hc hmass hK)
        (physicalBondProjection (core i))
      (cmp99LocalizedPhysicalPrecision_comp_covariance
        K (enlarged i) hc hmass hK)) x

end

end YangMills.RG
