/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Mass-uniform pointwise and normalized bounds for the literal CMP89
fine-lattice left derivative.  The numerator cancellation is the already
sealed `alpha = 0` endpoint bound; only the stabilized reciprocal is replaced
by its mass-uniform producer. -/

import YangMills.RG.BalabanCMP89Eq251FineLatticeStabilizedEndpointBound
import YangMills.RG.BalabanCMP89Eq249CentralStabilizedComplexFloorMassUniform
import YangMills.RG.BalabanCMP89Eq249NormalizedStabilizedEndpointIntegralBound
import YangMills.RG.BalabanCMP89Eq248GreenProductContourTelescope
import YangMills.RG.BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescope

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The normalized fine-lattice Green forward difference remains exact under
the mass-uniform window, including at `mass = 0`.  The two endpoint
integrability witnesses are constructed from the mass-uniform Green contour
telescope rather than from the older strictly-positive-mass theorem. -/
theorem cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen_forwardDifference_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (u : Fin 4 → ℤ) :
    (cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen L j mass a
          (cmp89Eq248FineLatticeForwardCoordinateShift mu u) -
        cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen
          L j mass a u) /
        (cmp89Eq249FineLatticeSpacing L j : ℂ) =
      cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
        L j mass a mu u := by
  let xi := cmp89Eq249FineLatticeSpacing L j
  let measure := cmp89Eq249FourDimensionalBrillouinMeasure
  let shifted : (Fin 4 → ℝ) → ℂ := fun x ⇒
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
      (fun nu ⇒ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      (cmp89Eq249PhysicalFineLatticeDisplacement xi
        (cmp89Eq248FineLatticeForwardCoordinateShift mu u))
  let base : (Fin 4 → ℝ) → ℂ := fun x ⇒
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
      (fun nu ⇒ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      (cmp89Eq249PhysicalFineLatticeDisplacement xi u)
  let deriv : (Fin 4 → ℝ) → ℂ := fun x ⇒
    cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
      L j mass a
      (fun nu ⇒ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu u
  have hshifted : Integrable shifted measure := by
    simpa [shifted, measure, xi,
      cmp89Eq248FineLatticeGreenPartialProductIntegrand_draft,
      cmp89Eq251EndpointPartialSignedContourMomentum_zero] using
      (integrable_cmp89Eq248FineLatticeGreenPartialProductIntegrand_draft
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hwindow hmass 0
        (cmp89Eq248FineLatticeForwardCoordinateShift mu u))
  have hbase : Integrable base measure := by
    simpa [base, measure, xi,
      cmp89Eq248FineLatticeGreenPartialProductIntegrand_draft,
      cmp89Eq251EndpointPartialSignedContourMomentum_zero] using
      (integrable_cmp89Eq248FineLatticeGreenPartialProductIntegrand_draft
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hwindow hmass 0 u)
  have hpoint : ∀ x, (shifted x - base x) / (xi : ℂ) = deriv x := by
    intro x
    simpa [shifted, base, deriv, xi] using
      (cmp89Eq248ComplexStabilizedGreenEndpoint_forwardDifference
        (L := L) (j := j) (mass := mass) (a := a)
        (fun nu ⇒ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu u)
  let normalization : ℂ := ((((2 * Real.pi) ^ 4)⁻¹ : ℝ) : ℂ)
  unfold cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen
    cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
  change
    (normalization * ∫ x, shifted x ∂measure -
        normalization * ∫ x, base x ∂measure) / (xi : ℂ) =
      normalization * ∫ x, deriv x ∂measure
  calc
    _ = normalization *
        (((∫ x, shifted x ∂measure) - ∫ x, base x ∂measure) /
          (xi : ℂ)) := by ring
    _ = normalization *
        ((∫ x, shifted x - base x ∂measure) / (xi : ℂ)) := by
      rw [MeasureTheory.integral_sub hshifted hbase]
    _ = normalization *
        (∫ x, (shifted x - base x) / (xi : ℂ) ∂measure) := by
      apply congrArg (fun value : ℂ ⇒ normalization * value)
      exact
        (MeasureTheory.integral_div (xi : ℂ)
          (fun x ⇒ shifted x - base x) (μ := measure)).symm
    _ = normalization * ∫ x, deriv x ∂measure := by
      congr 1
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall hpoint)

/-- The sealed `alpha = 0` numerator bound combined with the mass-uniform
stabilized reciprocal.  No strictly-positive-mass premise remains. -/
theorem norm_cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_signedContour_le_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (mu : Fin 4)
    (holderDisplacement endpointDisplacement : Fin 4 → ℝ) :
    ‖cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
        (cmp89Eq251SignedContourMomentum rho p endpointDisplacement) mu
        holderDisplacement endpointDisplacement‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement)) *
        cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho := by
  let z : Fin 4 → ℂ :=
    cmp89Eq251SignedContourMomentum rho p endpointDisplacement
  let decay : ℝ :=
    Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement))
  have hreal : ∀ nu, (z nu).re = p nu := by
    intro nu
    simp [z]
  have himag : ∀ nu, |(z nu).im| ≤ rho := by
    intro nu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p endpointDisplacement nu
  have hnum :=
    norm_cmp89Eq251ComplexStabilizedEndpointNumerator_zero_signedContour_le
      (L := L) (j := j) (mass := mass) hmass hrho hradius hp
      holderDisplacement endpointDisplacement hamplitude mu
  have hrecip :=
    norm_inv_cmp89Eq249CentralStabilizedAliasDenominator_le_massUniform
      (L := L) (j := j) (mass := mass) ha hrho hradius hmass hwindow
      hp hreal himag hamplitude
  have hdecay : 0 ≤ decay := (Real.exp_pos _).le
  have hampNonneg :
      0 ≤ cmp89Eq251ComplexEndpointAmplitudeBound rho := by
    have hcentral :
        0 ≤ cmp89Eq251ComplexCentralEndpointAmplitudeBound rho := by
      rw [cmp89Eq251ComplexCentralEndpointAmplitudeBound]
      positivity
    have hfine :
        0 ≤ cmp89Eq251CentralFineSymbolStripUpperBound rho := by
      rw [cmp89Eq251CentralFineSymbolStripUpperBound,
        cmp89Eq249CentralFineSymbolVerticalBound,
        cmp89Eq249CentralFineSymbolRealBound]
      positivity
    have hsum :
        0 ≤ cmp89Eq251ComplexNoncentralEndpointQuotientSumBound rho := by
      rw [cmp89Eq251ComplexNoncentralEndpointQuotientSumBound,
        cmp89Eq251ComplexNoncentralEndpointQuotientConstant,
        cmp89Eq251ComplexNoncentralEndpointRadialConstant,
        cmp89Eq245EntireAverageAliasStripConstant]
      positivity
    rw [cmp89Eq251ComplexEndpointAmplitudeBound]
    exact add_nonneg hcentral (mul_nonneg hfine hsum)
  have hnumBoundNonneg :
      0 ≤ decay * cmp89Eq251ComplexEndpointAmplitudeBound rho :=
    mul_nonneg hdecay hampNonneg
  rw [cmp89Eq251ComplexStabilizedEndpointIntegrand, div_eq_mul_inv, norm_mul,
    cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound]
  have hmul := mul_le_mul hnum hrecip (norm_nonneg _) hnumBoundNonneg
  simpa [z, decay, mul_assoc] using hmul

/-- Pointwise signed-contour bound for the literal fine-lattice derivative
integrand, retaining its generated physical displacement. -/
theorem norm_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_signedContour_le_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ nu, |p nu| ≤ Real.pi)
    (mu : Fin 4) (endpointU : Fin 4 → ℤ) :
    ‖cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a
        (cmp89Eq251SignedContourMomentum rho p
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) endpointU))
        mu endpointU‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) endpointU))) *
        cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho := by
  simpa [cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand]
    using
      (norm_cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_signedContour_le_massUniform_draft
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hradius hmass hwindow hamplitude hp mu (fun _ => 0)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) endpointU))

/-- The normalized real derivative coefficient equals its internally
constructed fully signed contour integral. -/
theorem cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel_eq_signed_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (endpointU : Fin 4 → ℤ) :
    cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
        L j mass a mu endpointU =
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x =>
          cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
            L j mass a
            (cmp89Eq251SignedContourMomentum rho
              (cmp89Eq251PhysicalBrillouinParameter x)
              (cmp89Eq249PhysicalFineLatticeDisplacement
                (cmp89Eq249FineLatticeSpacing L j) endpointU))
            mu endpointU) := by
  have h :=
    integral_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_eq_signed_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass mu endpointU
  unfold cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
    cmp89Eq249FourDimensionalBrillouinMeasure
  simpa [cmp89Eq249FineLatticeSpacing] using h

/-- Mass-uniform exponential bound for the literal normalized derivative
coefficient. -/
theorem norm_cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel_le_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (endpointU : Fin 4 → ℤ) :
    ‖cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
        L j mass a mu endpointU‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) endpointU))) *
        cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho := by
  rw [cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel_eq_signed_massUniform_draft
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hrho hamplitude hradius hwindow hmass]
  apply norm_cmp89Eq249NormalizedFourDimensionalBrillouinIntegral_le
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
  have hmem : ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure,
      x ∈ cube := by
    rw [hmeasure]
    exact ae_restrict_mem hcube
  filter_upwards [hmem] with x hx
  have hp : ∀ nu, |cmp89Eq251PhysicalBrillouinParameter x nu| ≤
      Real.pi := by
    intro nu
    have hxnu : x nu ∈ Set.Ioc 0 (2 * Real.pi) := hx nu (by simp)
    rw [abs_le]
    simp only [cmp89Eq251PhysicalBrillouinParameter]
    constructor <;> linarith [hxnu.1, hxnu.2, Real.pi_pos]
  exact
    norm_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_signedContour_le_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hradius hmass hwindow hamplitude hp mu endpointU

/-- Zero mass is an actual specialization of the mass-uniform derivative
bound, not a limiting argument or a positive-mass hypothesis. -/
theorem norm_cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel_massZero_le_draft
    {L j : ℕ} [NeZero L] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (mu : Fin 4) (endpointU : Fin 4 → ℤ) :
    ‖cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
        L j 0 a mu endpointU‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) endpointU))) *
        cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho := by
  exact
    norm_cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel_le_massUniform_draft
      (L := L) (j := j) (mass := 0) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow
      (by norm_num [CMP89Eq251UniformMassWindow]) mu endpointU

end

end YangMills.RG
