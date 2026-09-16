/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceCoordinatePivotTsumBound

/-!
# Carrier-linear traces of the complete source covariance difference

The existing coordinate-pivot layer estimate is specialized here to an
arbitrary ambient left multiplier.  The complete covariance difference is
expanded only once, at the traced factor.  Its first active source coordinate
therefore costs linearly in the contour carrier, while the ambient multiplier
remains visible solely through its operator norm.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

set_option maxHeartbeats 4000000 in
/-- The trace of an arbitrary ambient multiplier against the literal source
covariance difference has a carrier-linear bound.  No trace-class norm,
finite support, or rank hypothesis is used. -/
theorem norm_trace_mul_cmp116SourcePi4FullComplexCovarianceDifference_le
    {q M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin q ≃ ↥carrier) (z : Fin q → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
      physicalBondDist Ahead rho rate)
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (radius Rweak : ℝ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1)
    (P : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ) :
    let geometricRow :=
      (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate)
    let walkRatio :=
      cmp116SourcePi4ComplexContourRatio Delta rho Rweak
    let traceUnit :=
      (q : ℝ) * 625 *
        (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
        (radius * Rweak ^ 10000) * geometricRow *
        (Ahead * geometricRow)
    ‖Matrix.trace
        (P *
          (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling carrier e z) -
            cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK (fun _ => 1)))‖ ≤
      (traceUnit * ‖P‖) * (1 - walkRatio)⁻¹ ^ 2 := by
  dsimp only
  let sigma := cmp116SourceRestrictedShiftedCoupling carrier e z
  let geometricRow : ℝ :=
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate)
  let walkRatio : ℝ :=
    cmp116SourcePi4ComplexContourRatio Delta rho Rweak
  let traceUnit : ℝ :=
    (q : ℝ) * 625 *
      (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
      (radius * Rweak ^ 10000) * geometricRow *
      (Ahead * geometricRow)
  have hsigmaDiff : ∀ d, ‖sigma d - 1‖ ≤ radius := by
    intro d
    by_cases hd : d ∈ carrier
    · simpa [sigma,
        norm_cmp116SourceRestrictedShiftedCoupling_sub_one_of_mem
          carrier e z hd] using hz (e.symm ⟨d, hd⟩)
    · rw [show sigma d = 1 by
        exact cmp116SourceRestrictedShiftedCoupling_eq_one_of_not_mem
          carrier e z hd]
      simpa using hradius
  have hsigmaCap : ∀ d, ‖sigma d‖ ≤ Rweak := by
    intro d
    by_cases hd : d ∈ carrier
    · simpa [sigma, cmp116SourceRestrictedShiftedCoupling, hd] using
        hcap (e.symm ⟨d, hd⟩)
    · rw [show sigma d = 1 by
        exact cmp116SourceRestrictedShiftedCoupling_eq_one_of_not_mem
          carrier e z hd, norm_one]
      exact hRweak
  have hdiffSum : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma layer -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) layer :=
    summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hDelta hDelta1 sigma hradius hRweak hsigmaDiff hsigmaCap hcontourSmall
  have honeSum : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) layer :=
    summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_one
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hDelta hDelta1 hRweak hcontourSmall
  have htraceEq :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_trace_mul_pow_eq_tsum_layers
      (R := R) anchor K hc hmass hK sigma hdiffSum honeSum P 1 0
  have hsum :=
    norm_tsum_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_restricted_trace_le
      (R := R) (Delta := Delta)
      anchor carrier e z K hc hmass hK hAhead hrho Cert hrate hgeom
      hrange hDelta hDelta1 radius Rweak hradius hRweak hz hcap
      hcontourSmall P 1 0
  rw [show sigma =
      cmp116SourceRestrictedShiftedCoupling carrier e z by rfl] at htraceEq
  simp only [pow_zero, Matrix.mul_one, norm_one] at htraceEq hsum
  rw [htraceEq]
  convert hsum using 1
  ring

end

end YangMills.RG
