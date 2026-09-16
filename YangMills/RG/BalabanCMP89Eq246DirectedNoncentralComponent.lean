import YangMills.RG.BalabanCMP89Eq246DirectedSourceMoment
import YangMills.RG.BalabanCMP89Eq246FinePointSourceBareDiagonalBound
import YangMills.RG.BalabanCMP89Eq246FinePointSourceNoncentralCorrectionBound

/-!
# Directed noncentral component below CMP89 (2.46)

The target phase is combined with the literal fine point source before norms
are taken.  The bare inverse-Laplacian and rank-one correction retain their
different alias weights.  No finite alias-cardinality factor is hidden.
-/

namespace YangMills.RG

noncomputable section

/-- The source-independent reciprocal fine symbol inherits the existing
half-weight bound by specializing the normalized source endpoint to zero. -/
theorem norm_inv_cmp89Eq246EntireAliasFineSymbol_le_halfWeight
    {L j : ℕ} [NeZero L] {mass rho : ℝ}
    (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (m : CMP89Eq246AliasIndex 4 L j)
    (hm : m ≠ cmp89Eq249CentralAliasIndex 4 L j) :
    ‖(cmp89Eq246EntireAliasFineSymbol 4 L j mass z m)⁻¹‖ ≤
      cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound *
        cmp89Eq251MultidimensionalAliasWeight (1 / 2 : ℝ) m.1 := by
  have hzero :=
    norm_cmp89Eq246FinePointSourceBareDiagonal_le
      (L := L) (j := j) (mass := mass) (rho := rho)
      hrho hradius hamplitude hp hreal himag (fun _ => 0) m hm
  simpa [cmp89Eq246FinePointSourceAliasVector,
    cmp89Eq251ContourPhaseGrowth, cmp89Eq251DisplacementL1,
    cmp89Eq251EntirePhase, div_eq_mul_inv] using hzero

/-- The directed target/source phase gives exact relative decay in the bare
noncentral diagonal branch. -/
theorem norm_cmp89Eq246TargetPhase_mul_bareDiagonal_signedContour_le
    {L j : ℕ} [NeZero L] {mass rho : ℝ}
    (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (targetEndpoint sourceEndpoint : Fin 4 → ℝ)
    (m : CMP89Eq246AliasIndex 4 L j)
    (hm : m ≠ cmp89Eq249CentralAliasIndex 4 L j) :
    let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
    let z := cmp89Eq251SignedContourMomentum rho p displacement
    ‖Complex.exp
          (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint) *
        (cmp89Eq246FinePointSourceAliasVector
            4 L j z sourceEndpoint m /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z m)‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        (cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound *
          cmp89Eq251MultidimensionalAliasWeight (1 / 2 : ℝ) m.1) := by
  dsimp only
  let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
  let z := cmp89Eq251SignedContourMomentum rho p displacement
  let targetPhase := Complex.exp
    (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint)
  let source := cmp89Eq246FinePointSourceAliasVector
    4 L j z sourceEndpoint
  let symbol := cmp89Eq246EntireAliasFineSymbol 4 L j mass z m
  let decay := Real.exp
    (-(rho * cmp89Eq251DisplacementL1 displacement))
  let bound := cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound *
    cmp89Eq251MultidimensionalAliasWeight (1 / 2 : ℝ) m.1
  have hreal : ∀ mu, (z mu).re = p mu := by
    intro mu
    simp [z]
  have himag : ∀ mu, |(z mu).im| ≤ rho := by
    intro mu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p displacement mu
  have hphase : ‖targetPhase * source m‖ = decay := by
    simpa [targetPhase, source, decay, z, displacement] using
      (norm_cmp89Eq246TargetPhase_mul_finePointSourceAliasVector_signedContour
        (d := 4) (L := L) (j := j) rho p m targetEndpoint sourceEndpoint)
  have hinverse : ‖symbol⁻¹‖ ≤ bound := by
    simpa [symbol, bound] using
      (norm_inv_cmp89Eq246EntireAliasFineSymbol_le_halfWeight
        (L := L) (j := j) (mass := mass) (rho := rho)
        hrho hradius hamplitude hp hreal himag m hm)
  have hdecay : 0 ≤ decay := by
    dsimp [decay]
    positivity
  rw [show targetPhase * (source m / symbol) =
      (targetPhase * source m) * symbol⁻¹ by
        simp [div_eq_mul_inv, mul_assoc],
    norm_mul, hphase]
  exact mul_le_mul_of_nonneg_left hinverse hdecay

/-- The target phase is attached to the stabilized moment before the
noncentral rank-one quotient is estimated. -/
theorem norm_cmp89Eq246TargetPhase_mul_noncentralCorrection_signedContour_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (targetEndpoint sourceEndpoint : Fin 4 → ℝ)
    (m : CMP89Eq246AliasIndex 4 L j)
    (hm : m ≠ cmp89Eq249CentralAliasIndex 4 L j) :
    let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
    let z := cmp89Eq251SignedContourMomentum rho p displacement
    let targetPhase := Complex.exp
      (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint)
    ‖targetPhase *
        ((a : ℂ) * cmp89Eq246EntireAliasAverageColumn 4 L j z m *
            cmp89Eq246StabilizedFinePointSourceSolutionMoment
              4 L j mass a sourceEndpoint z /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z m)‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        (cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound a rho *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) m.1) := by
  dsimp only
  let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
  let z := cmp89Eq251SignedContourMomentum rho p displacement
  let targetPhase := Complex.exp
    (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint)
  let moment := cmp89Eq246StabilizedFinePointSourceSolutionMoment
    4 L j mass a sourceEndpoint z
  let quotient := cmp89Eq246EntireAliasAverageColumn 4 L j z m /
    cmp89Eq246EntireAliasFineSymbol 4 L j mass z m
  let qbound := cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho
  let weight := cmp89Eq251MultidimensionalAliasWeight
    (cmp89Eq251AliasSeriesExponent 4 (-1)) m.1
  let mbound := cmp89Eq246FinePointSourceMomentAmplitudeBound a rho
  let decay := Real.exp
    (-(rho * cmp89Eq251DisplacementL1 displacement))
  have hreal : ∀ mu, (z mu).re = p mu := by
    intro mu
    simp [z]
  have himag : ∀ mu, |(z mu).im| ≤ rho := by
    intro mu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p displacement mu
  have hquot : ‖quotient‖ ≤ qbound * weight := by
    have hm0 : m.1 ≠ cmp89Eq249ZeroAlias 4 := by
      intro hz
      apply hm
      apply Subtype.ext
      exact hz
    simpa [quotient, qbound, weight,
      cmp89Eq246EntireAliasAverageColumn,
      cmp89Eq246EntireAliasFineSymbol] using
      (norm_cmp89Eq248ComplexNoncentralGreenQuotient_le_sourceWeight_draft
        (N := L ^ j) (mass := mass)
        (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)
        hrho hradius m.2 hm0 hp hreal himag hamplitude)
  have hmoment : ‖targetPhase * moment‖ ≤ decay * mbound := by
    simpa [targetPhase, moment, decay, z, displacement, mbound] using
      (norm_cmp89Eq246TargetPhase_mul_stabilizedSourceMoment_signedContour_le
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hradius hmass hwindow hamplitude hp
        targetEndpoint sourceEndpoint m)
  have hqbound : 0 ≤ qbound := by
    dsimp [qbound, cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft,
      cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hweight : 0 ≤ weight :=
    cmp89Eq251MultidimensionalAliasWeight_nonneg _ m.1
  have hleft := mul_le_mul_of_nonneg_left hquot (abs_nonneg a)
  have hleftNonneg : 0 ≤ |a| * (qbound * weight) :=
    mul_nonneg (abs_nonneg a) (mul_nonneg hqbound hweight)
  have hmul := mul_le_mul hleft hmoment (norm_nonneg _) hleftNonneg
  rw [show targetPhase * ((a : ℂ) *
      cmp89Eq246EntireAliasAverageColumn 4 L j z m * moment /
        cmp89Eq246EntireAliasFineSymbol 4 L j mass z m) =
      (a : ℂ) * quotient * (targetPhase * moment) by
        dsimp [quotient]
        simp [div_eq_mul_inv]
        ring,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simpa [qbound, weight, mbound, decay,
    cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound,
    mul_assoc, mul_left_comm, mul_comm] using hmul

/-- One complete noncentral solution component keeps the distinct bare and
rank-one alias weights while sharing the same directed endpoint decay. -/
theorem norm_cmp89Eq246TargetPhase_mul_noncentralSolution_signedContour_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (targetEndpoint sourceEndpoint : Fin 4 → ℝ)
    (m : CMP89Eq246AliasIndex 4 L j)
    (hm : m ≠ cmp89Eq249CentralAliasIndex 4 L j) :
    let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
    let z := cmp89Eq251SignedContourMomentum rho p displacement
    let targetPhase := Complex.exp
      (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint)
    ‖targetPhase * cmp89Eq246StabilizedFinePointSourceSolution
        4 L j mass a z sourceEndpoint m‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        ((cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound *
            cmp89Eq251MultidimensionalAliasWeight (1 / 2 : ℝ) m.1) +
          (cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound a rho *
            cmp89Eq251MultidimensionalAliasWeight
              (cmp89Eq251AliasSeriesExponent 4 (-1)) m.1)) := by
  dsimp only
  let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
  let z := cmp89Eq251SignedContourMomentum rho p displacement
  let targetPhase := Complex.exp
    (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint)
  let source := cmp89Eq246FinePointSourceAliasVector
    4 L j z sourceEndpoint
  let moment := cmp89Eq246StabilizedFinePointSourceSolutionMoment
    4 L j mass a sourceEndpoint z
  let bare := source m / cmp89Eq246EntireAliasFineSymbol 4 L j mass z m
  let correction :=
    (a : ℂ) * cmp89Eq246EntireAliasAverageColumn 4 L j z m * moment /
      cmp89Eq246EntireAliasFineSymbol 4 L j mass z m
  let decay := Real.exp
    (-(rho * cmp89Eq251DisplacementL1 displacement))
  let bareBound := cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound *
    cmp89Eq251MultidimensionalAliasWeight (1 / 2 : ℝ) m.1
  let correctionBound :=
    cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound a rho *
      cmp89Eq251MultidimensionalAliasWeight
        (cmp89Eq251AliasSeriesExponent 4 (-1)) m.1
  have hbranch :
      cmp89Eq246StabilizedFinePointSourceSolution
          4 L j mass a z sourceEndpoint m = bare - correction := by
    simp [cmp89Eq246StabilizedFinePointSourceSolution,
      cmp89Eq246StabilizedAliasFullSolution, source, moment, bare, correction,
      hm, cmp89Eq246StabilizedFinePointSourceSolutionMoment_eq]
  have hbare : ‖targetPhase * bare‖ ≤ decay * bareBound := by
    simpa [targetPhase, bare, source, decay, bareBound, z, displacement] using
      (norm_cmp89Eq246TargetPhase_mul_bareDiagonal_signedContour_le
        (L := L) (j := j) (mass := mass) (rho := rho)
        hrho hradius hamplitude hp targetEndpoint sourceEndpoint m hm)
  have hcorrection :
      ‖targetPhase * correction‖ ≤ decay * correctionBound := by
    simpa [targetPhase, correction, moment, decay, correctionBound, z,
      displacement] using
      (norm_cmp89Eq246TargetPhase_mul_noncentralCorrection_signedContour_le
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hradius hmass hwindow hamplitude hp
        targetEndpoint sourceEndpoint m hm)
  rw [hbranch, mul_sub]
  calc
    _ ≤ ‖targetPhase * bare‖ + ‖targetPhase * correction‖ := norm_sub_le _ _
    _ ≤ decay * bareBound + decay * correctionBound := add_le_add hbare hcorrection
    _ = decay * (bareBound + correctionBound) := by ring

end

end YangMills.RG
