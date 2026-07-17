import YangMills.RG.BalabanCMP99PatchedParametrix

/-!
# CMP99 patched parametrix: exact exterior-defect factorization

The local precision is block diagonal for the decomposition into a finite
enlarged bond domain and its complement.  Consequently its exact covariance
commutes with the domain projection.  If a core lies inside the enlarged
domain, the corresponding patched-parametrix defect is therefore exactly

`(1 - P_S) K C_S P_core`.

This identifies the defect as flux leaving the enlarged domain.  It is an
exact support statement, not yet an exponentially small collar estimate.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

theorem physicalBondProjection_comp_self
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N)) :
    (physicalBondProjection S : PhysicalEndomorphism d N Nc).comp
        (physicalBondProjection S) =
      physicalBondProjection S := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro b
  by_cases hb : b ∈ S
  · simp [hb]
  · simp [hb]

theorem physicalBondProjection_comp_of_subset
    {d N Nc : ℕ} [NeZero N]
    {core enlarged : Finset (PhysicalBond d N)}
    (hsub : core ⊆ enlarged) :
    (physicalBondProjection enlarged : PhysicalEndomorphism d N Nc).comp
        (physicalBondProjection core) =
      physicalBondProjection core := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro b
  simp only [ContinuousLinearMap.comp_apply]
  by_cases hb : b ∈ core
  · have hb' := hsub hb
    simp [hb, hb']
  · by_cases hb' : b ∈ enlarged
    · rw [physicalBondProjection_apply_mem enlarged hb',
        physicalBondProjection_apply_not_mem core hb]
    · rw [physicalBondProjection_apply_not_mem enlarged hb',
        physicalBondProjection_apply_not_mem core hb]

theorem cmp99LocalizedPhysicalPrecision_comm_projection
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S : Finset (PhysicalBond d N)) (mass : ℝ) :
    (cmp99LocalizedPhysicalPrecision K S mass).comp
        (physicalBondProjection S) =
      (physicalBondProjection S).comp
        (cmp99LocalizedPhysicalPrecision K S mass) := by
  apply ContinuousLinearMap.ext
  intro x
  have hPx :
      physicalBondProjection S (physicalBondProjection S x) =
        physicalBondProjection S x := by
    exact DFunLike.congr_fun (physicalBondProjection_comp_self S) x
  have hQPx :
      physicalBondComplementProjection S (physicalBondProjection S x) = 0 := by
    rw [physicalBondComplementProjection, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, hPx, sub_self]
  have hPQx :
      physicalBondProjection S (physicalBondComplementProjection S x) = 0 := by
    apply PiLp.ext
    intro b
    by_cases hb : b ∈ S
    · rw [physicalBondProjection_apply_mem S hb]
      change x b - physicalBondProjection S x b = 0
      rw [physicalBondProjection_apply_mem S hb, sub_self]
    · rw [physicalBondProjection_apply_not_mem S hb, PiLp.zero_apply]
  simp only [ContinuousLinearMap.comp_apply, cmp99LocalizedPhysicalPrecision,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [hPx, hQPx, smul_zero, add_zero, map_add, map_smul, hPQx,
    smul_zero, add_zero]
  exact (DFunLike.congr_fun (physicalBondProjection_comp_self S)
    (K (physicalBondProjection S x))).symm

theorem cmp99LocalizedPhysicalCovariance_comm_projection
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S : Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    (cmp99LocalizedPhysicalCovariance K S hc hmass hK).comp
        (physicalBondProjection S) =
      (physicalBondProjection S).comp
        (cmp99LocalizedPhysicalCovariance K S hc hmass hK) := by
  let L := cmp99LocalizedPhysicalPrecision K S mass
  let C := cmp99LocalizedPhysicalCovariance K S hc hmass hK
  let P : PhysicalEndomorphism d N Nc := physicalBondProjection S
  have hLC : L.comp C = ContinuousLinearMap.id ℝ _ :=
    cmp99LocalizedPhysicalPrecision_comp_covariance K S hc hmass hK
  have hCL : C.comp L = ContinuousLinearMap.id ℝ _ :=
    cmp99LocalizedPhysicalCovariance_comp_precision K S hc hmass hK
  have hLP : L.comp P = P.comp L :=
    cmp99LocalizedPhysicalPrecision_comm_projection K S mass
  apply ContinuousLinearMap.ext
  intro x
  have hLCx : L (C x) = x := by
    exact DFunLike.congr_fun hLC x
  have hLPx : L (P (C x)) = P (L (C x)) := by
    exact DFunLike.congr_fun hLP (C x)
  have hCLx : C (L (P (C x))) = P (C x) := by
    exact DFunLike.congr_fun hCL (P (C x))
  simp only [ContinuousLinearMap.comp_apply]
  calc
    C (P x) = C (P (L (C x))) := by rw [hLCx]
    _ = C (L (P (C x))) := by rw [hLPx]
    _ = P (C x) := hCLx

/-- Exact single-chart collar factorization.  Once `core ⊆ enlarged`, the
global-to-local defect has an explicit exterior projection on its output. -/
theorem cmp99SinglePhysicalParametrixDefect_eq_exterior_flux
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    {core enlarged : Finset (PhysicalBond d N)}
    (hsub : core ⊆ enlarged)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    (K - cmp99LocalizedPhysicalPrecision K enlarged mass).comp
        ((cmp99LocalizedPhysicalCovariance K enlarged hc hmass hK).comp
          (physicalBondProjection core)) =
      (physicalBondComplementProjection enlarged).comp
        (K.comp
          ((cmp99LocalizedPhysicalCovariance K enlarged hc hmass hK).comp
            (physicalBondProjection core))) := by
  let C := cmp99LocalizedPhysicalCovariance K enlarged hc hmass hK
  let P : PhysicalEndomorphism d N Nc := physicalBondProjection enlarged
  let Pcore : PhysicalEndomorphism d N Nc := physicalBondProjection core
  have hPPcore : P.comp Pcore = Pcore :=
    physicalBondProjection_comp_of_subset hsub
  have hCP : C.comp P = P.comp C :=
    cmp99LocalizedPhysicalCovariance_comm_projection
      K enlarged hc hmass hK
  apply ContinuousLinearMap.ext
  intro x
  have hPcore : P (Pcore x) = Pcore x :=
    DFunLike.congr_fun hPPcore x
  have hPy : P (C (Pcore x)) = C (Pcore x) := by
    have hcomm := DFunLike.congr_fun hCP (Pcore x)
    simp only [ContinuousLinearMap.comp_apply] at hcomm
    rw [← hcomm, hPcore]
  have hQy :
      physicalBondComplementProjection enlarged (C (Pcore x)) = 0 := by
    change C (Pcore x) - P (C (Pcore x)) = 0
    rw [hPy, sub_self]
  have hLy :
      cmp99LocalizedPhysicalPrecision K enlarged mass (C (Pcore x)) =
        P (K (C (Pcore x))) := by
    rw [cmp99LocalizedPhysicalPrecision, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, hPy, hQy, smul_zero, add_zero]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
  rw [hLy]
  rw [physicalBondComplementProjection, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply]

end

end YangMills.RG
