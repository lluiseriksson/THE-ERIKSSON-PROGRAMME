/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceCoordinatePivotLayerBound
import YangMills.RG.BalabanCMP116SourceRestrictedCoordinatePivotTsumTrace

/-!
# Summing the physical coordinate-pivot trace layers

The fixed-length trace estimate is summed with the differentiated geometric
series.  The resulting constant is linear in the physical contour carrier and
contains no ambient chart or lattice cardinality.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

set_option maxHeartbeats 3000000 in
/-- The complete source-coordinate trace layer series is bounded by the exact
differentiated geometric denominator. -/
theorem norm_tsum_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_restricted_trace_le
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
    (hrange : R + 1 ≤ 4 * M)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (radius Rweak : ℝ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1)
    (P D : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (m : ℕ) :
    let geometricRow :=
      (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate)
    let walkRatio :=
      cmp116SourcePi4ComplexContourRatio Delta rho Rweak
    let layerPrefactor :=
      (q : ℝ) * 625 *
        (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
        (radius * Rweak ^ 10000) * geometricRow * ‖D ^ m‖ *
        (‖P‖ * (Ahead * geometricRow))
    ‖∑' layer : ℕ,
        Matrix.trace
          ((P *
            (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                (R := R) anchor K hc hmass hK
                (cmp116SourceRestrictedShiftedCoupling carrier e z) layer -
              cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                (R := R) anchor K hc hmass hK (fun _ => 1) layer)) *
            D ^ m)‖ ≤
      layerPrefactor * (1 - walkRatio)⁻¹ ^ 2 := by
  dsimp only
  let geometricRow : ℝ :=
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate)
  let walkRatio : ℝ :=
    cmp116SourcePi4ComplexContourRatio Delta rho Rweak
  let layerPrefactor : ℝ :=
    (q : ℝ) * 625 *
      (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
      (radius * Rweak ^ 10000) * geometricRow * ‖D ^ m‖ *
      (‖P‖ * (Ahead * geometricRow))
  let term := fun layer : ℕ =>
    Matrix.trace
      ((P *
        (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
            (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling carrier e z) layer -
          cmp116SourcePi4FullComplexWeakenedCovarianceLayer
            (R := R) anchor K hc hmass hK (fun _ => 1) layer)) *
        D ^ m)
  have hrow0 : 0 ≤ geometricRow := by
    dsimp [geometricRow]
    exact mul_nonneg (by positivity)
      (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)
  have hratio0 : 0 ≤ walkRatio := by
    dsimp [walkRatio]
    unfold cmp116SourcePi4ComplexContourRatio
    positivity
  have hratioNorm : ‖walkRatio‖ < 1 := by
    simpa [walkRatio] using hcontourSmall
  have hgeomSeries :
      HasSum
        (fun layer : ℕ =>
          (((layer + 1 : ℕ) : ℝ) * walkRatio ^ layer))
        ((1 - walkRatio)⁻¹ ^ 2) := by
    simpa using
      (hasSum_choose_mul_geometric_of_norm_lt_one'
        (R := ℝ) 1 hratioNorm)
  have hprefactor0 : 0 ≤ layerPrefactor := by
    dsimp [layerPrefactor]
    positivity
  have hmajor :
      Summable fun layer : ℕ =>
        layerPrefactor *
          (((layer + 1 : ℕ) : ℝ) * walkRatio ^ layer) :=
    hgeomSeries.summable.mul_left layerPrefactor
  have hterm : ∀ layer : ℕ,
      ‖term layer‖ ≤
        layerPrefactor *
          (((layer + 1 : ℕ) : ℝ) * walkRatio ^ layer) := by
    intro layer
    calc
      ‖term layer‖ ≤
          (q : ℝ) *
            ((((layer + 1) * 625 *
                cmp116SourcePi4TerminalBranching Delta ^ layer : ℕ) : ℝ) *
              ((((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
                ((radius * Rweak ^ (10000 * (layer + 1))) *
                  (((rho ^ layer * geometricRow) * ‖D ^ m‖) *
                    (‖P‖ * (Ahead * geometricRow)))))) := by
        simpa [term, geometricRow] using
          (norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_restricted_trace_le
            (R := R) (Delta := Delta) (layer := layer)
            anchor carrier e z K hc hmass hK Cert hrate hgeom
            hrange hDelta hDelta1 radius Rweak hradius hRweak hz hcap
            P D m)
      _ = layerPrefactor *
          (((layer + 1 : ℕ) : ℝ) * walkRatio ^ layer) := by
        dsimp [layerPrefactor, walkRatio]
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
        push_cast
        rw [show 10000 * (layer + 1) =
          10000 + 10000 * layer by omega]
        rw [pow_add, pow_mul]
        unfold cmp116SourcePi4ComplexContourRatio
        rw [mul_pow, mul_pow]
        ring
  have hnorm :
      Summable fun layer : ℕ => ‖term layer‖ :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  change ‖∑' layer : ℕ, term layer‖ ≤
    layerPrefactor * (1 - walkRatio)⁻¹ ^ 2
  calc
    ‖∑' layer : ℕ, term layer‖ ≤
        ∑' layer : ℕ, ‖term layer‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' layer : ℕ,
        layerPrefactor *
          (((layer + 1 : ℕ) : ℝ) * walkRatio ^ layer) :=
      hnorm.tsum_le_tsum hterm hmajor
    _ = layerPrefactor * (1 - walkRatio)⁻¹ ^ 2 :=
      (hgeomSeries.mul_left layerPrefactor).tsum_eq

set_option maxHeartbeats 3000000 in
/-- Positive trace powers of the literal relative covariance defect inherit
the carrier-linear layer bound.  Both matrix layer summability hypotheses are
constructed from the physical contour certificate. -/
theorem norm_trace_cmp116SourcePi4FullComplexRelativeCovarianceDefect_pow_succ_le
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
    (m : ℕ) :
    let geometricRow :=
      (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate)
    let walkRatio :=
      cmp116SourcePi4ComplexContourRatio Delta rho Rweak
    let D :=
      cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling carrier e z)
    let tracePrefactor :=
      (q : ℝ) * 625 *
        (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
        (radius * Rweak ^ 10000) * geometricRow *
        ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        (Ahead * geometricRow)
    ‖Matrix.trace (D ^ (m + 1))‖ ≤
      (tracePrefactor * (1 - walkRatio)⁻¹ ^ 2) * ‖D‖ ^ m := by
  dsimp only
  let sigma :=
    cmp116SourceRestrictedShiftedCoupling carrier e z
  let D :=
    cmp116SourcePi4FullComplexRelativeCovarianceDefect
      (R := R) anchor K hc hmass hK sigma
  let geometricRow : ℝ :=
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate)
  let walkRatio : ℝ :=
    cmp116SourcePi4ComplexContourRatio Delta rho Rweak
  let tracePrefactor : ℝ :=
    (q : ℝ) * 625 *
      (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
      (radius * Rweak ^ 10000) * geometricRow *
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
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
  have htraceEq :
      Matrix.trace (D ^ (m + 1)) =
        ∑' layer : ℕ,
          Matrix.trace
            ((cmp116PhysicalEndomorphismComplexMatrix K *
              (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                  (R := R) anchor K hc hmass hK sigma layer -
                cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                  (R := R) anchor K hc hmass hK (fun _ => 1) layer)) *
              D ^ m) := by
    dsimp [D]
    exact
      trace_cmp116SourcePi4FullComplexRelativeCovarianceDefect_pow_succ_eq_tsum_layers
        anchor K hc hmass hK sigma hdiffSum honeSum m
  have hsum :=
    norm_tsum_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_restricted_trace_le
      (R := R) (Delta := Delta)
      anchor carrier e z K hc hmass hK hAhead hrho Cert hrate hgeom
      hrange hDelta hDelta1 radius Rweak hradius hRweak hz hcap
      hcontourSmall
      (cmp116PhysicalEndomorphismComplexMatrix K) D m
  have hrow0 : 0 ≤ geometricRow := by
    dsimp [geometricRow]
    exact mul_nonneg (by positivity)
      (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)
  have hprefactor0 : 0 ≤ tracePrefactor := by
    dsimp [tracePrefactor]
    positivity
  rw [htraceEq]
  calc
    ‖∑' layer : ℕ,
        Matrix.trace
          ((cmp116PhysicalEndomorphismComplexMatrix K *
            (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                (R := R) anchor K hc hmass hK sigma layer -
              cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                (R := R) anchor K hc hmass hK (fun _ => 1) layer)) *
            D ^ m)‖ ≤
        (tracePrefactor * (1 - walkRatio)⁻¹ ^ 2) * ‖D ^ m‖ := by
      dsimp [tracePrefactor, geometricRow, walkRatio, sigma, D]
      convert hsum using 1 <;> ring
    _ ≤ (tracePrefactor * (1 - walkRatio)⁻¹ ^ 2) * ‖D‖ ^ m := by
      gcongr
      exact norm_pow_le D m

set_option maxHeartbeats 3000000 in
/-- The traced Mercator logarithm of the physical relative covariance defect
has a source-carrier-linear bound. -/
theorem norm_trace_nearLog_cmp116SourcePi4FullComplexRelativeCovarianceDefect_le
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
    (hdefectSmall :
      ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling carrier e z)‖ < 1) :
    let geometricRow :=
      (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate)
    let walkRatio :=
      cmp116SourcePi4ComplexContourRatio Delta rho Rweak
    let D :=
      cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling carrier e z)
    let tracePrefactor :=
      (q : ℝ) * 625 *
        (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
        (radius * Rweak ^ 10000) * geometricRow *
        ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        (Ahead * geometricRow)
    ‖Matrix.trace (nearLog D)‖ ≤
      (tracePrefactor * (1 - walkRatio)⁻¹ ^ 2) /
        (1 - ‖D‖) := by
  dsimp only
  let D :=
    cmp116SourcePi4FullComplexRelativeCovarianceDefect
      (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling carrier e z)
  let geometricRow : ℝ :=
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate)
  let walkRatio : ℝ :=
    cmp116SourcePi4ComplexContourRatio Delta rho Rweak
  let tracePrefactor : ℝ :=
    (q : ℝ) * 625 *
      (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
      (radius * Rweak ^ 10000) * geometricRow *
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
      (Ahead * geometricRow)
  have htrace : ∀ m : ℕ,
      ‖Matrix.trace (D ^ (m + 1))‖ ≤
        (tracePrefactor * (1 - walkRatio)⁻¹ ^ 2) * ‖D‖ ^ m := by
    intro m
    simpa [D, geometricRow, walkRatio, tracePrefactor] using
      (norm_trace_cmp116SourcePi4FullComplexRelativeCovarianceDefect_pow_succ_le
        (R := R) (Delta := Delta)
        anchor carrier e z K hc hmass hK hAhead hrho Cert hrate hgeom
        htri hrange hDelta hDelta1 radius Rweak hradius hRweak hz hcap
        hcontourSmall m)
  exact
    norm_trace_nearLog_le_of_trace_pow_geometric
      D hdefectSmall (norm_nonneg D) hdefectSmall htrace

end

end YangMills.RG
