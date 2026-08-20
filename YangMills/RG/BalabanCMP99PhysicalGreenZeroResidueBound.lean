/-
SEALED SOURCE-SPECIFIC BRICK -- COMPILER-VERIFIED.

This file combines the literal mass-uniform CMP89 Green coefficient bound
with the zero-residue selector of Step 8b.22 and the centered periodic lattice
estimate.  It produces a norm bound for the selected coefficient sum while
retaining decay in the canonical centered endpoint representative.

It does not yet identify that representative with the existing physical bond
transport displacement, transport the decay to CMP99 localization owners,
construct regional `B0`, or attain window 15.
-/

import YangMills.RG.BalabanCMP89CenteredGreenFourierSummability
import YangMills.RG.BalabanCMP99CenteredPeriodicEndpointDictionary


namespace YangMills.RG

noncomputable section

/-- The literal normalized zero-mass Green has the fine-lattice coefficient
majorant consumed by the centered periodic residue theorem. -/
theorem norm_cmp89Eq248PhysicalZeroMassGreen_le_signedLatticeWeight_draft
    {K : ℕ} [NeZero K] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (v : Fin 4 → ℤ) :
    ‖cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen K 1 0 a v‖ ≤
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ)) v := by
  have h :=
    norm_cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen_le_massUniform_draft
      (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow
        (by norm_num [CMP89Eq251UniformMassWindow]) v
  rw [cmp89Eq248PhysicalFineGreenDecay_eq_signedLatticeWeight_draft
    (L := K) (j := 1) rho v] at h
  simpa [pow_one, mul_comm] using h

/-- Absolute mass of the literal Green coefficients selected by residue zero.
The public right-hand side retains the centered fine-lattice decay and has no
`N^4` volume factor. -/
theorem tsum_norm_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_zeroResidue_le_draft
    {K N : ℕ} [NeZero K] [NeZero N] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (u : Fin 4 → ℤ) :
    (∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        ‖cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          K 1 0 a u n.1‖) ≤
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
            (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N) u)) := by
  let A := cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho
  let coefficient := fun v : Fin 4 → ℤ =>
    cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen K 1 0 a v
  have hA : 0 ≤ A := by
    dsimp [A]
    rw [cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft]
    apply mul_nonneg
    · rw [cmp89Eq248ComplexGreenNumeratorBound_draft]
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
      exact add_nonneg (by positivity) (mul_nonneg hfine hsum)
    · rw [cmp89Eq249CentralStabilizedComplexReciprocalBound]
      have hgap :
          0 < cmp89Eq249CentralStabilizedLowerConstant 4 a -
            cmp89Eq249CentralStabilizedDenominatorVariationBound a rho := by
        simpa [CMP89Eq249CentralStabilizedComplexWindow] using hwindow
      exact inv_nonneg.mpr hgap.le
  have hcoefficient : ∀ v,
      ‖coefficient v‖ ≤ A *
        cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ)) v := by
    intro v
    exact norm_cmp89Eq248PhysicalZeroMassGreen_le_signedLatticeWeight_draft
      ha hrho.le hamplitude hradius hwindow v
  have h :=
    tsum_norm_cmp99FlatIntegerZeroResidueClass_le_centeredPeriodic
      (d := 4) (K := K) (N := N) hrho hA coefficient hcoefficient u
  simpa [A, coefficient,
    cmp89Eq248CenteredGreenPhysicalFourierCoefficient,
    cmp89SignedLatticeResidueAffineMap] using h

/-- Norm of the actual complex coefficient sum selected by Step 8b.22. -/
theorem norm_tsum_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_zeroResidue_le_draft
    {K N : ℕ} [NeZero K] [NeZero N] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (u : Fin 4 → ℤ) :
    ‖∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          K 1 0 a u n.1‖ ≤
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
            (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N) u)) := by
  have hfull :=
    summable_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_draft
      (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow
        (by norm_num [CMP89Eq251UniformMassWindow]) u
  have hnorm : Summable (fun n : CMP99FlatIntegerResidueClass 4 N 0 =>
      ‖cmp89Eq248CenteredGreenPhysicalFourierCoefficient
        K 1 0 a u n.1‖) := hfull.norm.subtype _
  exact (norm_tsum_le_tsum_norm hnorm).trans
    (tsum_norm_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_zeroResidue_le_draft
      ha hrho hamplitude hradius hwindow u)

end

end YangMills.RG
