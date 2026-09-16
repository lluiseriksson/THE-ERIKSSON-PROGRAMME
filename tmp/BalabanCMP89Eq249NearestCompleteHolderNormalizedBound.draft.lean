/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

H4c: apply the mass-uniform complete Holder contour once, in the internally
selected nearest signed-l1 endpoint direction.  The original endpoint order is
recovered by the exact orientation scalar, whose norm is one.  The source/owner
two-point metric dictionary, regional B0, window 15 and terminal fields remain
open.
-/

import YangMills.RG.BalabanCMP89Eq249CompleteHolderEndpointSwap
import YangMills.RG.BalabanCMP89Eq249CompleteHolderMassUniformNormalizedIntegralBound

namespace YangMills.RG

noncomputable section

/-- The original ordered normalized Holder integral is bounded by the one
selected physical signed-l1 contour, without summing two endpoint bounds. -/
theorem
    norm_cmp89Eq249NormalizedCompleteHolderIntegral_le_nearestSignedL1_draft
    {L j : ℕ} [NeZero L] {mass a rho alpha : ℝ}
    (ha : 0 ≤ a) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (halphaStrict : alpha < 1) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) {holder transport : Fin 4 → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holder) :
    let xi := cmp89Eq249FineLatticeSpacing L j
    let physical := cmp89Eq249PhysicalFineLatticeDisplacement xi
    ‖cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x => cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
          (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
          mu (physical holder) (physical transport))‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1
        (physical
          (cmp89Eq249NearestEndpointTransport_draft holder transport)))) *
        cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft
          a rho alpha := by
  dsimp only
  let xi := cmp89Eq249FineLatticeSpacing L j
  let physical := cmp89Eq249PhysicalFineLatticeDisplacement xi
  let selectedHolder :=
    cmp89Eq249NearestEndpointHolder_draft holder transport
  let selectedTransport :=
    cmp89Eq249NearestEndpointTransport_draft holder transport
  let orientation :=
    cmp89Eq249NearestEndpointOrientation_draft holder transport
  let original : (Fin 4 → ℝ) → ℂ := fun x =>
    cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
      (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      mu (physical holder) (physical transport)
  let selected : (Fin 4 → ℝ) → ℂ := fun x =>
    cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
      (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      mu (physical selectedHolder) (physical selectedTransport)
  have hpoint : ∀ x, original x = orientation * selected x := by
    intro x
    simpa [original, selected, orientation, selectedHolder,
      selectedTransport, physical, xi] using
      (cmp89Eq251ComplexStabilizedIntegrand_physicalFine_eq_orientation_mul_nearest_draft
        (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        mu holder transport)
  have hintegral :
      (∫ x, original x ∂cmp89Eq249FourDimensionalBrillouinMeasure) =
        orientation *
          ∫ x, selected x ∂cmp89Eq249FourDimensionalBrillouinMeasure := by
    calc
      _ = ∫ x, orientation * selected x
          ∂cmp89Eq249FourDimensionalBrillouinMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
      _ = orientation *
          ∫ x, selected x ∂cmp89Eq249FourDimensionalBrillouinMeasure :=
            integral_const_mul orientation selected
  have hnormalized :
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral original =
        orientation *
          cmp89Eq249NormalizedFourDimensionalBrillouinIntegral selected := by
    unfold cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
    rw [hintegral]
    ring
  have horientation : ‖orientation‖ = 1 := by
    by_cases hnear :
        cmp89Eq249NearestEndpointUsesTransport_draft holder transport
    · simp [orientation, cmp89Eq249NearestEndpointOrientation_draft, hnear]
    · simp [orientation, cmp89Eq249NearestEndpointOrientation_draft, hnear]
  have hselectedUnit :
      CMP89Eq251UnitLatticeBondDisplacement selectedHolder := by
    exact cmp89Eq249NearestEndpointHolder_unit_draft hunit
  have hselected :=
    norm_cmp89Eq249NormalizedCompleteHolderIntegral_physicalFine_le_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      (alpha := alpha) ha halpha0 halpha1 halphaStrict hrho hradius hmass
      hwindow hamplitude mu hselectedUnit selectedTransport
  rw [hnormalized, norm_mul, horientation, one_mul]
  simpa [selected, selectedHolder, selectedTransport, physical, xi] using
    hselected

end

end YangMills.RG
