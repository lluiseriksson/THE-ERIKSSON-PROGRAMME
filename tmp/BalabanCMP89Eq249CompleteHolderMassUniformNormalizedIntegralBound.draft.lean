/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

H3d: normalized complete physical fine-lattice Holder integral bound.  The
real product integral is moved to the single signed transport contour by H3c,
then the literal H2d pointwise majorant is integrated with exact Brillouin
volume cancellation.  No owner dictionary, regional B0, window-15 claim or
terminal field is asserted here.
-/

import YangMills.RG.BalabanCMP89Eq249CompleteHolderMassUniformProductContourTelescope
import YangMills.RG.BalabanCMP89Eq249PhysicalFineComplexHolderStabilizedBound
import YangMills.RG.BalabanCMP89Eq249NormalizedStabilizedEndpointIntegralBound

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The literal source-normalized complete Holder integral loses no volume
factor and retains exactly the physical signed-l1 decay and H2d constant. -/
theorem
    norm_cmp89Eq249NormalizedCompleteHolderIntegral_physicalFine_le_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho alpha : ℝ}
    (ha : 0 ≤ a) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (halphaStrict : alpha < 1) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) {holderU : Fin 4 → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holderU)
    (transportU : Fin 4 → ℤ) :
    let xi := cmp89Eq249FineLatticeSpacing L j
    let holder := cmp89Eq249PhysicalFineLatticeDisplacement xi holderU
    let transport := cmp89Eq249PhysicalFineLatticeDisplacement xi transportU
    ‖cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x => cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
          (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
          mu holder transport)‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 transport)) *
        cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft
          a rho alpha := by
  dsimp only
  let xi := cmp89Eq249FineLatticeSpacing L j
  let holder : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement xi holderU
  let transport : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement xi transportU
  let realIntegrand : (Fin 4 → ℝ) → ℂ := fun x =>
    cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
      (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      mu holder transport
  let signedIntegrand : (Fin 4 → ℝ) → ℂ := fun x =>
    cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
      (cmp89Eq251SignedContourMomentum rho
        (cmp89Eq251PhysicalBrillouinParameter x) transport)
      mu holder transport
  let C : ℝ :=
    Real.exp (-(rho * cmp89Eq251DisplacementL1 transport)) *
      cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft a rho alpha
  have hcontour :
      (∫ x, realIntegrand x ∂cmp89Eq249FourDimensionalBrillouinMeasure) =
        ∫ x, signedIntegrand x
          ∂cmp89Eq249FourDimensionalBrillouinMeasure := by
    simpa [realIntegrand, signedIntegrand, holder, transport, xi,
      cmp89Eq249FourDimensionalBrillouinMeasure] using
      (integral_cmp89Eq251ComplexStabilizedIntegrand_physicalFineHolder_eq_signed_massUniform_draft
        (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
        (rho := rho) ha hrho hamplitude hradius hwindow hmass
        mu holderU transportU)
  have hnormalized :
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral realIntegrand =
        cmp89Eq249NormalizedFourDimensionalBrillouinIntegral signedIntegrand := by
    unfold cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
    rw [hcontour]
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  let cube : Set (Fin 4 → ℝ) :=
    Set.univ.pi fun _ : Fin 4 => Set.Ioc 0 (2 * Real.pi)
  have hmeasure :
      cmp89Eq249FourDimensionalBrillouinMeasure =
        (volume : Measure (Fin 4 → ℝ)).restrict cube := by
    dsimp [cmp89Eq249FourDimensionalBrillouinMeasure, cube]
    rw [volume_pi, Measure.restrict_pi_pi]
    simp [Set.uIoc_of_le htwoPi]
  have hcube : MeasurableSet cube := by
    exact MeasurableSet.pi (Set.to_countable Set.univ) fun _ _ =>
      measurableSet_Ioc
  have hmem : ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure, x ∈ cube := by
    rw [hmeasure]
    exact ae_restrict_mem hcube
  have hpoint : ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure,
      ‖signedIntegrand x‖ ≤ C := by
    filter_upwards [hmem] with x hx
    have hp : ∀ nu, |cmp89Eq251PhysicalBrillouinParameter x nu| ≤
        Real.pi := by
      intro nu
      have hxnu : x nu ∈ Set.Ioc 0 (2 * Real.pi) := hx nu (by simp)
      rw [abs_le]
      simp only [cmp89Eq251PhysicalBrillouinParameter]
      constructor <;> linarith [hxnu.1, hxnu.2, Real.pi_pos]
    simpa [signedIntegrand, C, holder, transport, xi] using
      (norm_cmp89Eq251ComplexStabilizedIntegrand_physicalFineHolder_signedContour_le_draft
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        (alpha := alpha) ha halpha0 halpha1 halphaStrict hrho hradius hmass
        hwindow hp hunit transport hamplitude mu)
  rw [hnormalized]
  exact norm_cmp89Eq249NormalizedFourDimensionalBrillouinIntegral_le hpoint

end

end YangMills.RG
