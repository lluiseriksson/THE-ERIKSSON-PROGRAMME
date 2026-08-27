import YangMills.RG.BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation
import YangMills.RG.BalabanCMP99Eq359TowerRealSliceAgreement
import tmp.BalabanCMP99SourceWeightedGaugePrecisionDictionary.draft

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# Weighted/counting real slice for the CMP99 (3.60) precision

The analytic tower uses the printed source-weighted starred synthesis.  The
real source precision uses Lean's counting-space Hilbert adjoint.  Their
coefficients therefore differ by the exact terminal-volume ratio; omitting it
would preserve every operator type while changing the physical precision.
-/

namespace YangMills.RG

noncomputable section

variable {d N Nc : ℕ} [NeZero N] [NeZero Nc]
variable {Omega : ActiveGaugeRegion d N} {spacing : ℝ}

/-- A complex printed-star precision at the derived weighted coefficient is
exactly the compact real slice of the counting-Hilbert source precision.
The Laplacian real-slice equality and the tower agreement are the only
generic inputs; the coefficient conversion is derived internally. -/
theorem cmp99Eq360ComplexRegionalPrecision_realSlice_weighted
    (complexTower : CMP99ComplexRegionalTower (Nc := Nc) Omega spacing)
    (physicalTower : CMP99SourceWeightedRegionalTower
      (g := SUNLieCoord Nc) Omega spacing)
    (agreement : CMP99Eq359TowerRealSliceAgreement
      complexTower physicalTower)
    (complexDelta : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc))
    (physicalDelta : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hDelta : ∀ phi,
      complexDelta (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi) =
        cmp99ActiveGaugeZeroCochainComplexificationCLM Omega
          (physicalDelta phi))
    (a : ℝ) (hterminal : physicalTower.terminalSpacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99Eq360ComplexRegionalPrecision complexDelta complexTower.Qprime
        complexTower.starred
        (cmp99SourceWeightedAdjointCountingCoefficient physicalTower a : ℂ)
        (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi) =
      cmp99ActiveGaugeZeroCochainComplexificationCLM Omega
        (cmp99SourceGaugePrecision physicalDelta physicalTower.Qprime a phi) := by
  rw [cmp99Eq360ComplexRegionalPrecision,
    cmp99SourceGaugePrecision_eq_weightedAdjoint physicalTower physicalDelta
      a hterminal]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  rw [hDelta, agreement.Qprime_realSlice, agreement.starred_realSlice,
    map_add, map_smul, Complex.coe_smul]

end

end YangMills.RG
