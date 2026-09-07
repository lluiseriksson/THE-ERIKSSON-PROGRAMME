/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexContourDefect

/-!
# Column estimate for the complete source contour defect

The source layer estimate is entrywise and its spatial profile uses the
symmetric physical bond distance.  Consequently the same summation controls
both rows and columns.  This module makes that fact explicit and supplies
the transpose `L∞` norm required by the bilateral `R1` budget, without a
dimension-dependent row-to-column conversion.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

set_option maxHeartbeats 5000000 in
/-- Entrywise estimate for the complete, length-summed covariance defect. -/
theorem norm_cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_apply_le
    {M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    ‖(cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma -
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1)) row col‖ ≤
      (cmp116SourcePi4ComplexContourPrefactor Ahead radius Rweak *
        (1 - cmp116SourcePi4ComplexContourRatio Delta rho Rweak)⁻¹ ^ 2) *
        Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ))) := by
  let sigmaLayer := fun n : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK sigma n
  let oneLayer := fun n : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK (fun _ => 1) n
  let sigmaEntry := fun n : ℕ => sigmaLayer n row col
  let oneEntry := fun n : ℕ => oneLayer n row col
  let diffEntry := fun n : ℕ => sigmaEntry n - oneEntry n
  have hdiffSum :
      Summable fun n : ℕ => sigmaLayer n - oneLayer n :=
    summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hDelta hDelta1 sigma hradius hRweak hdiff hcap hsmall
  have honeSum : Summable oneLayer :=
    summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_one
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hDelta hDelta1 hRweak hsmall
  have hsigmaSum : Summable sigmaLayer := by
    have hadd := hdiffSum.add honeSum
    exact hadd.congr fun n => by
      exact sub_add_cancel (sigmaLayer n) (oneLayer n)
  have hsigmaEntry : Summable sigmaEntry :=
    (Pi.summable.mp (Pi.summable.mp hsigmaSum row)) col
  have honeEntry : Summable oneEntry :=
    (Pi.summable.mp (Pi.summable.mp honeSum row)) col
  have hdiffEntry : Summable diffEntry := hsigmaEntry.sub honeEntry
  have hmajorHasSum :
      HasSum
        (fun n : ℕ =>
          cmp116SourcePi4ComplexDefectLayerAmplitude
            Delta Ahead rho radius Rweak n *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ))))
        ((cmp116SourcePi4ComplexContourPrefactor Ahead radius Rweak *
          (1 - cmp116SourcePi4ComplexContourRatio
            Delta rho Rweak)⁻¹ ^ 2) *
          Real.exp (-(rate *
            (physicalBondDist row.1 col.1 : ℝ)))) :=
    (hasSum_cmp116SourcePi4ComplexDefectLayerAmplitude
      Delta Ahead rho radius Rweak hsmall).mul_right
        (Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ))))
  change ‖(∑' n, sigmaEntry n) - ∑' n, oneEntry n‖ ≤ _
  rw [← hsigmaEntry.tsum_sub honeEntry]
  calc
    ‖∑' n : ℕ, diffEntry n‖ ≤ ∑' n : ℕ, ‖diffEntry n‖ :=
      norm_tsum_le_tsum_norm hdiffEntry.norm
    _ ≤ ∑' n : ℕ,
        cmp116SourcePi4ComplexDefectLayerAmplitude
          Delta Ahead rho radius Rweak n *
          Real.exp (-(rate *
            (physicalBondDist row.1 col.1 : ℝ))) := by
      exact Summable.tsum_le_tsum
        (fun n =>
          norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one_apply_le'
            anchor K hc hmass hK hAhead hrho hrate Cert htri hrange
            hDelta hDelta1 sigma hradius hRweak hdiff hcap n row col)
        hdiffEntry.norm hmajorHasSum.summable
    _ = _ := hmajorHasSum.tsum_eq

set_option maxHeartbeats 5000000 in
/-- Volume-uniform column norm of the complete contour defect.  Symmetry of
the metric, rather than symmetry of the complex covariance, supplies the
bound. -/
theorem linfty_opNorm_transpose_cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_le
    {M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1) :
    ‖(cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma -
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1)).transpose‖ ≤
      (cmp116SourcePi4ComplexContourPrefactor Ahead radius Rweak *
        (1 - cmp116SourcePi4ComplexContourRatio Delta rho Rweak)⁻¹ ^ 2) *
        (((Nc ^ 2 - 1 : ℕ) : ℝ) *
          cmp99PhysicalBondGeometricRowSum 4 rate) := by
  apply physicalWalkMatrix_linfty_opNorm_le_of_fixedRate
  · unfold cmp116SourcePi4ComplexContourPrefactor
    positivity
  · exact hgeom
  · intro row col
    rw [Matrix.transpose_apply]
    simpa only [physicalBondDist_comm] using
      (norm_cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_apply_le
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
        hDelta hDelta1 sigma hradius hRweak hdiff hcap hsmall col row)

end

end YangMills.RG
