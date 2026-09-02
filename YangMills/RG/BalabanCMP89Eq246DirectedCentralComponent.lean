import YangMills.RG.BalabanCMP89Eq246DirectedSourceMoment
import YangMills.RG.BalabanCMP89Eq246FinePointSourceCentralComponentBound

/-!
# PRE-VALIDATION: directed central component below CMP89 (2.46)

Source is present, its promoted `.olean` has not yet been materialized in a
fresh checkout, and the result has not yet been cold-verified by the compiler.
The exact draft passed one retained-runtime focal/audit diagnostic only.

This draft keeps the two directed inputs to the central numerator separate:
the stabilized full-solution moment and the noncentral source moment.  It
does not identify the Fourier integral with the continuous Green kernel.
-/

namespace YangMills.RG

noncomputable section

/-- The target phase at the central alias and the noncentral source moment
recombine to relative endpoint decay. -/
theorem norm_cmp89Eq246CentralTargetPhase_mul_noncentralSourceMoment_signedContour_le
    {L j : ℕ} [NeZero L] {mass rho : ℝ}
    (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (targetEndpoint sourceEndpoint : Fin 4 → ℝ) :
    let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
    let z := cmp89Eq251SignedContourMomentum rho p displacement
    let central := cmp89Eq249CentralAliasIndex 4 L j
    ‖Complex.exp
          (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z central.1) targetEndpoint) *
        cmp89Eq246StabilizedAliasNoncentralSourceMoment 4 L j mass z
          (cmp89Eq246FinePointSourceAliasVector
            4 L j z sourceEndpoint)‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
  dsimp only
  let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
  let z := cmp89Eq251SignedContourMomentum rho p displacement
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let g := Real.exp
    (rho * cmp89Eq246SignedEndpointPairing displacement sourceEndpoint)
  let source := cmp89Eq246FinePointSourceAliasVector
    4 L j z sourceEndpoint
  let targetPhase := Complex.exp
    (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z central.1) targetEndpoint)
  have hreal : ∀ mu, (z mu).re = p mu := by
    intro mu
    simp [z]
  have himag : ∀ mu, |(z mu).im| ≤ rho := by
    intro mu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p displacement mu
  have hg : 0 ≤ g := (Real.exp_pos _).le
  have hsource : ∀ n, ‖source n‖ ≤ g := by
    intro n
    exact le_of_eq
      (norm_cmp89Eq246FinePointSourceAliasVector_signedContour
        rho p displacement sourceEndpoint n)
  have hmoment :
      ‖cmp89Eq246StabilizedAliasNoncentralSourceMoment
          4 L j mass z source‖ ≤
        g * cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
    exact norm_cmp89Eq246StabilizedAliasNoncentralSourceMoment_le_of_envelope
      (L := L) (j := j) (mass := mass) (rho := rho) (g := g)
      hrho hradius hp hreal himag hamplitude source hg hsource
  have htarget :
      ‖targetPhase‖ = Real.exp
        (-(rho * cmp89Eq246SignedEndpointPairing
          displacement targetEndpoint)) := by
    exact norm_cmp89Eq246TargetPhase_signedContour
      rho p displacement targetEndpoint central
  rw [norm_mul]
  calc
    ‖targetPhase‖ *
        ‖cmp89Eq246StabilizedAliasNoncentralSourceMoment
          4 L j mass z source‖ ≤
      ‖targetPhase‖ *
        (g * cmp89Eq248ComplexNoncentralGreenSumBound_draft rho) :=
          mul_le_mul_of_nonneg_left hmoment (norm_nonneg targetPhase)
    _ = (Real.exp
          (-(rho * cmp89Eq246SignedEndpointPairing
            displacement targetEndpoint)) *
        Real.exp
          (rho * cmp89Eq246SignedEndpointPairing
            displacement sourceEndpoint)) *
        cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
          rw [htarget]
          simpa only [g, mul_assoc]
    _ = Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
          rw [cmp89Eq246_targetDecay_mul_sourceGrowth]

/-- The complete central solution component, including its reciprocal-row
factor, has directed relative endpoint decay. -/
theorem norm_cmp89Eq246CentralTargetPhase_mul_centralComponent_signedContour_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hstabilized : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpair : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (targetEndpoint sourceEndpoint : Fin 4 → ℝ) :
    let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
    let z := cmp89Eq251SignedContourMomentum rho p displacement
    let central := cmp89Eq249CentralAliasIndex 4 L j
    ‖Complex.exp
          (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z central.1) targetEndpoint) *
        cmp89Eq246StabilizedFinePointSourceSolution
          4 L j mass a z sourceEndpoint central‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        cmp89Eq246FinePointSourceCentralComponentAmplitudeBound a rho := by
  dsimp only
  let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
  let z := cmp89Eq251SignedContourMomentum rho p displacement
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let source := cmp89Eq246FinePointSourceAliasVector
    4 L j z sourceEndpoint
  let moment := cmp89Eq246StabilizedFinePointSourceSolutionMoment
    4 L j mass a sourceEndpoint z
  let sourceMoment := cmp89Eq246StabilizedAliasNoncentralSourceMoment
    4 L j mass z source
  let aliasSum := cmp89Eq249ComplexNoncentralAliasSum 4 L j mass z
  let row := cmp89Eq246EntireAliasAverageRow 4 L j z central
  let targetPhase := Complex.exp
    (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z central.1) targetEndpoint)
  let decay := Real.exp
    (-(rho * cmp89Eq251DisplacementL1 displacement))
  let momentBound := cmp89Eq246FinePointSourceMomentAmplitudeBound a rho
  let sourceMomentBound := cmp89Eq248ComplexNoncentralGreenSumBound_draft rho
  let aliasBound := cmp89Eq249ComplexNoncentralAliasSumBound rho
  let numerator := moment - sourceMoment + (a : ℂ) * moment * aliasSum
  have hreal : ∀ mu, (z mu).re = p mu := by
    intro mu
    simp [z]
  have himag : ∀ mu, |(z mu).im| ≤ rho := by
    intro mu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p displacement mu
  have hdecay : 0 ≤ decay := by
    dsimp [decay]
    positivity
  have hmomentBound : 0 ≤ momentBound := by
    have hrecip :
        0 ≤ cmp89Eq249CentralStabilizedComplexReciprocalBound a rho := by
      rw [cmp89Eq249CentralStabilizedComplexReciprocalBound]
      have hgap :
          0 < cmp89Eq249CentralStabilizedLowerConstant 4 a -
            cmp89Eq249CentralStabilizedDenominatorVariationBound a rho := by
        simpa [CMP89Eq249CentralStabilizedComplexWindow] using hstabilized
      exact inv_nonneg.mpr hgap.le
    have hfine :
        0 ≤ cmp89Eq251CentralFineSymbolStripUpperBound rho := by
      rw [cmp89Eq251CentralFineSymbolStripUpperBound,
        cmp89Eq249CentralFineSymbolVerticalBound,
        cmp89Eq249CentralFineSymbolRealBound]
      positivity
    have hsum :
        0 ≤ cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
      rw [cmp89Eq248ComplexNoncentralGreenSumBound_draft,
        cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft,
        cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
        cmp89Eq245EntireAverageAliasStripConstant]
      positivity
    dsimp [momentBound, cmp89Eq246FinePointSourceMomentAmplitudeBound]
    exact mul_nonneg (add_nonneg (by positivity) (mul_nonneg hfine hsum)) hrecip
  have hsourceMomentBound : 0 ≤ sourceMomentBound := by
    dsimp [sourceMomentBound, cmp89Eq248ComplexNoncentralGreenSumBound_draft,
      cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft,
      cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have haliasBound : 0 ≤ aliasBound := by
    dsimp [aliasBound, cmp89Eq249ComplexNoncentralAliasSumBound,
      cmp89Eq249ComplexNoncentralAliasQuotientConstant,
      cmp89Eq249ComplexNoncentralAliasRadialConstant,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hmoment : ‖targetPhase * moment‖ ≤ decay * momentBound := by
    simpa [targetPhase, moment, decay, momentBound, central, source, z,
      displacement] using
      (norm_cmp89Eq246TargetPhase_mul_stabilizedSourceMoment_signedContour_le
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hradius hmass hstabilized hamplitude hp
        targetEndpoint sourceEndpoint central)
  have hsourceMoment :
      ‖targetPhase * sourceMoment‖ ≤ decay * sourceMomentBound := by
    simpa [targetPhase, sourceMoment, sourceMomentBound, decay, central,
      source, z, displacement] using
      (norm_cmp89Eq246CentralTargetPhase_mul_noncentralSourceMoment_signedContour_le
        (L := L) (j := j) (mass := mass) (rho := rho)
        hrho hradius hamplitude hp targetEndpoint sourceEndpoint)
  have halias : ‖aliasSum‖ ≤ aliasBound := by
    simpa [aliasSum, aliasBound] using
      norm_cmp89Eq249ComplexNoncentralAliasSum_le_bound
        (L := L) (j := j) (mass := mass) (rho := rho)
        hrho hradius hp hreal himag hamplitude
  have hcorrection :
      ‖targetPhase * ((a : ℂ) * moment * aliasSum)‖ ≤
        decay * (|a| * momentBound * aliasBound) := by
    rw [show targetPhase * ((a : ℂ) * moment * aliasSum) =
        (a : ℂ) * (targetPhase * moment) * aliasSum by ring,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hleft := mul_le_mul_of_nonneg_left hmoment (abs_nonneg a)
    have hleftNonneg : 0 ≤ |a| * (decay * momentBound) :=
      mul_nonneg (abs_nonneg a) (mul_nonneg hdecay hmomentBound)
    have hmul := mul_le_mul hleft halias (norm_nonneg aliasSum) hleftNonneg
    nlinarith
  have hnumerator :
      ‖targetPhase * numerator‖ ≤
        decay * (momentBound + sourceMomentBound +
          |a| * momentBound * aliasBound) := by
    rw [show targetPhase * numerator =
        (targetPhase * moment - targetPhase * sourceMoment) +
          targetPhase * ((a : ℂ) * moment * aliasSum) by
            dsimp [numerator]
            ring]
    calc
      _ ≤ ‖targetPhase * moment - targetPhase * sourceMoment‖ +
          ‖targetPhase * ((a : ℂ) * moment * aliasSum)‖ := norm_add_le _ _
      _ ≤ (‖targetPhase * moment‖ + ‖targetPhase * sourceMoment‖) +
          ‖targetPhase * ((a : ℂ) * moment * aliasSum)‖ := by
            gcongr
            exact norm_sub_le _ _
      _ ≤ (decay * momentBound + decay * sourceMomentBound) +
          decay * (|a| * momentBound * aliasBound) := by gcongr
      _ = _ := by ring
  have hrowInv : ‖row⁻¹‖ ≤
      cmp89Eq246CentralAverageRowReciprocalBound rho := by
    simpa [row, central] using
      norm_inv_cmp89Eq246CentralAverageRow_le
        (L := L) (j := j) hrho hpair hp hreal himag
  have hsolution :
      cmp89Eq246StabilizedFinePointSourceSolution
          4 L j mass a z sourceEndpoint central = numerator / row := by
    dsimp [numerator, row, moment, sourceMoment, aliasSum, source, central]
    rw [cmp89Eq246StabilizedFinePointSourceSolution,
      cmp89Eq246StabilizedAliasFullSolution]
    simp only [if_pos]
    rw [← cmp89Eq246StabilizedFinePointSourceSolutionMoment_eq]
    rw [cmp89Eq246FinePointSourceCentralNumerator_eq]
  rw [hsolution, div_eq_mul_inv,
    show targetPhase * (numerator * row⁻¹) =
      (targetPhase * numerator) * row⁻¹ by ring,
    norm_mul]
  have hbudgetNonneg :
      0 ≤ momentBound + sourceMomentBound +
        |a| * momentBound * aliasBound :=
    add_nonneg (add_nonneg hmomentBound hsourceMomentBound)
      (mul_nonneg (mul_nonneg (abs_nonneg a) hmomentBound) haliasBound)
  have hmul := mul_le_mul hnumerator hrowInv (norm_nonneg _)
    (mul_nonneg hdecay hbudgetNonneg)
  simpa [targetPhase, decay, momentBound, sourceMomentBound, aliasBound,
    cmp89Eq246FinePointSourceCentralComponentAmplitudeBound,
    mul_assoc, mul_left_comm, mul_comm] using hmul

end

end YangMills.RG
