import YangMills.RG.BalabanCMP89Eq246CentralAverageRowReciprocalBound
import YangMills.RG.BalabanCMP89Eq246FinePointSourceCentralNumeratorIdentity
import YangMills.RG.BalabanCMP89Eq249ComplexNoncentralAliasSumBound

/-!
# Cold-sealed: scale-uniform central component below CMP89 (2.46)

Cold compiler validation: exact source checkpoint
`c1cdd849d0117cdf18724ac076cd4a5bbfd67b35` passed the fresh Colab Pro+
CPU/high-RAM focal and exact axiom gate recorded in Verification Ledger
Addendum 1027.

The central branch is controlled without charging it the quadratic bare
diagonal alias budget.  Its noncentral terms retain the row factor and reduce
to the already sealed source moment and printed row-column alias sum.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit scale-uniform coefficient for the central component. -/
def cmp89Eq246FinePointSourceCentralComponentAmplitudeBound
    (a rho : ℝ) : ℝ :=
  cmp89Eq246CentralAverageRowReciprocalBound rho *
    (cmp89Eq246FinePointSourceMomentAmplitudeBound a rho +
      cmp89Eq248ComplexNoncentralGreenSumBound_draft rho +
      |a| * cmp89Eq246FinePointSourceMomentAmplitudeBound a rho *
        cmp89Eq249ComplexNoncentralAliasSumBound rho)

/-- The central fine-point-source solution component is uniform in the alias
window. -/
theorem norm_cmp89Eq246FinePointSourceCentralComponent_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hstabilized : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpair : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (sourceEndpoint : Fin 4 → ℝ) :
    ‖cmp89Eq246StabilizedFinePointSourceSolution
        4 L j mass a z sourceEndpoint
        (cmp89Eq249CentralAliasIndex 4 L j)‖ ≤
      cmp89Eq251ContourPhaseGrowth rho sourceEndpoint *
        cmp89Eq246FinePointSourceCentralComponentAmplitudeBound a rho := by
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let source :=
    cmp89Eq246FinePointSourceAliasVector 4 L j z sourceEndpoint
  let moment :=
    cmp89Eq246StabilizedFinePointSourceSolutionMoment
      4 L j mass a sourceEndpoint z
  let sourceMoment :=
    cmp89Eq246StabilizedAliasNoncentralSourceMoment
      4 L j mass z source
  let aliasSum := cmp89Eq249ComplexNoncentralAliasSum 4 L j mass z
  let row := cmp89Eq246EntireAliasAverageRow 4 L j z central
  let growth := cmp89Eq251ContourPhaseGrowth rho sourceEndpoint
  let momentBound := cmp89Eq246FinePointSourceMomentAmplitudeBound a rho
  let sourceMomentBound := cmp89Eq248ComplexNoncentralGreenSumBound_draft rho
  let aliasBound := cmp89Eq249ComplexNoncentralAliasSumBound rho
  let numerator := moment - sourceMoment + (a : ℂ) * moment * aliasSum
  have hgrowth : 0 ≤ growth := by
    dsimp [growth, cmp89Eq251ContourPhaseGrowth]
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
  have hmoment : ‖moment‖ ≤ growth * momentBound := by
    simpa [moment, growth, momentBound] using
      norm_cmp89Eq246StabilizedFinePointSourceSolutionMoment_le
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hradius hmass hstabilized hamplitude hp hreal himag
        sourceEndpoint
  have hsourceMoment : ‖sourceMoment‖ ≤ growth * sourceMomentBound := by
    simpa [sourceMoment, source, growth, sourceMomentBound] using
      norm_cmp89Eq246StabilizedAliasNoncentralFinePointSourceMoment_le
        (L := L) (j := j) (mass := mass) (rho := rho)
        hrho hradius hp hreal himag hamplitude sourceEndpoint
  have halias : ‖aliasSum‖ ≤ aliasBound := by
    simpa [aliasSum, aliasBound] using
      norm_cmp89Eq249ComplexNoncentralAliasSum_le_bound
        (L := L) (j := j) (mass := mass) (rho := rho)
        hrho hradius hp hreal himag hamplitude
  have hcorrection :
      ‖(a : ℂ) * moment * aliasSum‖ ≤
        growth * (|a| * momentBound * aliasBound) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hleft := mul_le_mul_of_nonneg_left hmoment (abs_nonneg a)
    have hleftNonneg : 0 ≤ |a| * (growth * momentBound) :=
      mul_nonneg (abs_nonneg a) (mul_nonneg hgrowth hmomentBound)
    have hmul := mul_le_mul hleft halias (norm_nonneg aliasSum) hleftNonneg
    nlinarith
  have hnumerator :
      ‖numerator‖ ≤ growth *
        (momentBound + sourceMomentBound + |a| * momentBound * aliasBound) := by
    calc
      ‖numerator‖ ≤ ‖moment - sourceMoment‖ +
          ‖(a : ℂ) * moment * aliasSum‖ := by
        exact norm_add_le _ _
      _ ≤ (‖moment‖ + ‖sourceMoment‖) +
          ‖(a : ℂ) * moment * aliasSum‖ := by
        gcongr
        exact norm_sub_le moment sourceMoment
      _ ≤ (growth * momentBound + growth * sourceMomentBound) +
          growth * (|a| * momentBound * aliasBound) := by
        gcongr
      _ = growth *
          (momentBound + sourceMomentBound + |a| * momentBound * aliasBound) := by
        ring
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
  rw [show cmp89Eq249CentralAliasIndex 4 L j = central by rfl, hsolution,
    norm_div, div_eq_mul_inv, ← norm_inv]
  have hmul := mul_le_mul hnumerator hrowInv (norm_nonneg _)
    (mul_nonneg hgrowth (by positivity))
  simpa [numerator, growth, momentBound, sourceMomentBound, aliasBound,
    cmp89Eq246FinePointSourceCentralComponentAmplitudeBound,
    mul_assoc, mul_left_comm, mul_comm] using hmul

end

end YangMills.RG
