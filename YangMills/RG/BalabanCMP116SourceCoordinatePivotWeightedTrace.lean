/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4WeightedSplitMatrix
import YangMills.RG.BalabanCMP116SourceCoordinatePivotCoreCardinality
import YangMills.RG.BalabanCMP116FiniteCarrierLinftyNorm

/-!
# Weighted first-hit trace bound for one physical contour coordinate

The localized rectangular trace estimate is combined with the literal source
weighted-row certificate.  Prefix and suffix are each converted to a matrix
bound only once, and the finite intermediate dimension is replaced by the
explicit singleton-pivot `Pi^4` bound.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

set_option maxHeartbeats 2000000 in

/-- A nonzero coordinate-pivot walk trace has a volume-uniform physical
first-hit bound.  The two displayed powers of `rho` are complementary parts
of the same walk length. -/
theorem norm_cmp116SourcePi4ForwardWalk_coordinatePivot_weight_mul_trace_le_weighted
    {n M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin n ≃ ↥carrier) (z : Fin n → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate : ℝ}
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
      physicalBondDist Ahead rho rate)
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (walk : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)))
    (i : Fin n)
    (hweight :
      cmp116RestrictedOrderedPivotWeight
          (cmp116SourcePi4ForwardWalkActive anchor walk)
          carrier e z i ≠ 0)
    (P D : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (m : ℕ) :
    let rawWalk :=
      (⟨walk.1, walk.2⟩ :
        CMP99GeneralizedWalk Unit
          ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)))
    let domainActive :=
      fun chart :
          ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)) =>
        cmp99SourceDomainLargeBlocks chart.1.domain ∩
          cmp116SourceSigmaZero anchor
    let cube : FinBox 4 (2 * Q) := e i
    let hactive : cube ∈ rawWalk.active domainActive :=
      mem_active_of_cmp116RestrictedOrderedPivotWeight_ne_zero
        (cmp116SourcePi4ForwardWalkActive anchor walk)
        carrier e z i hweight
    let index := rawWalk.firstActiveDomainIndex domainActive cube hactive
    let geometricRow :=
      (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate)
    ‖cmp116RestrictedOrderedPivotWeight
          (cmp116SourcePi4ForwardWalkActive anchor walk)
          carrier e z i *
        Matrix.trace
          ((P *
            cmp116PhysicalEndomorphismComplexMatrix
              (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)) *
            D ^ m)‖ ≤
      (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
        (‖cmp116RestrictedOrderedPivotWeight
              (cmp116SourcePi4ForwardWalkActive anchor walk)
              carrier e z i‖ *
          (((rho ^ (rawWalk.tail.length - index.val) * geometricRow) *
                ‖D ^ m‖) *
            (‖P‖ * ((Ahead * rho ^ index.val) * geometricRow)))) := by
  classical
  dsimp only
  let rawWalk :=
    (⟨walk.1, walk.2⟩ :
      CMP99GeneralizedWalk Unit
        ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)))
  let domainActive :=
    fun chart :
        ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)) =>
      cmp99SourceDomainLargeBlocks chart.1.domain ∩
        cmp116SourceSigmaZero anchor
  let cube : FinBox 4 (2 * Q) := e i
  have hactive : cube ∈ rawWalk.active domainActive := by
    exact
      mem_active_of_cmp116RestrictedOrderedPivotWeight_ne_zero
        (cmp116SourcePi4ForwardWalkActive anchor walk)
        carrier e z i hweight
  let index := rawWalk.firstActiveDomainIndex domainActive cube hactive
  let R0 :=
    cmp99PhysicalPatchHead
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
  let R := fun (_ : Unit) =>
    cmp99PhysicalPatchContinuation
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
  let leftPart := ((rawWalk.factors R0 R).take index).prod
  let pivot :=
    rawWalk.firstActiveFactor domainActive R0 R cube hactive
  let rightPart := ((rawWalk.factors R0 R).drop (index + 1)).prod
  let activeCore :=
    CMP99GeneralizedWalk.contourActiveCore
      (fun chart => cmp99SourcePi4ChartCore (M := M) chart.1)
      domainActive ({cube} : Finset (FinBox 4 (2 * Q)))
  let activeCoordinates :=
    cmp116PhysicalCoreCoordinates (Nc := Nc) activeCore
  let geometricRow :=
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate)
  let w :=
    cmp116RestrictedOrderedPivotWeight
      (cmp116SourcePi4ForwardWalkActive anchor walk) carrier e z i
  have hbase :=
    norm_cmp116SourcePi4ForwardWalk_coordinatePivot_weight_mul_trace_le
      anchor carrier e z K hc hmass hK walk i hweight P D m
  dsimp only at hbase
  have hprefix :
      ‖cmp116PhysicalEndomorphismComplexMatrix
          (leftPart.comp pivot)‖ ≤
        (Ahead * rho ^ index.val) * geometricRow := by
    simpa [rawWalk, R0, R, leftPart, pivot, index, geometricRow] using
      (cmp116SourcePi4ForwardWalk_prefixThroughFactor_matrix_linfty_le
        K hc hmass hK Cert hrate hgeom walk index)
  have hsuffix :
      ‖cmp116PhysicalEndomorphismComplexMatrix rightPart‖ ≤
        rho ^ (rawWalk.tail.length - index.val) * geometricRow := by
    simpa [rawWalk, R0, R, rightPart, index, geometricRow] using
      (cmp116SourcePi4ForwardWalk_suffixAfterFactor_matrix_linfty_le
        K hc hmass hK Cert hrate hgeom walk index)
  have hAhead : 0 ≤ Ahead := (Cert.head walk.1).1
  have hrho : 0 ≤ rho := (Cert.continuation walk.1).1
  have hgeometricRow : 0 ≤ geometricRow := by
    dsimp [geometricRow]
    exact mul_nonneg (Nat.cast_nonneg _)
      (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)
  have hrestriction :
      ‖cmp116FinsetCoordinateRestriction
          (ι := CMP116PhysicalWalkCoordinate
            4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates‖ ≤ 1 :=
    linfty_opNorm_cmp116FinsetCoordinateRestriction_le_one activeCoordinates
  have hinclusion :
      ‖cmp116FinsetColumnInclusion
          (ι := CMP116PhysicalWalkCoordinate
            4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates‖ ≤ 1 :=
    linfty_opNorm_cmp116FinsetColumnInclusion_le_one activeCoordinates
  have hright :
      ‖cmp116FinsetCoordinateRestriction
            (ι := CMP116PhysicalWalkCoordinate
              4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates *
          cmp116PhysicalEndomorphismComplexMatrix rightPart‖ ≤
        rho ^ (rawWalk.tail.length - index.val) * geometricRow := by
    calc
      _ ≤
          ‖cmp116FinsetCoordinateRestriction
              (ι := CMP116PhysicalWalkCoordinate
                4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates‖ *
            ‖cmp116PhysicalEndomorphismComplexMatrix rightPart‖ :=
        Matrix.linfty_opNorm_mul _ _
      _ ≤ 1 *
          (rho ^ (rawWalk.tail.length - index.val) * geometricRow) :=
        mul_le_mul hrestriction hsuffix (norm_nonneg _) (by positivity)
      _ = _ := one_mul _
  have hleft :
      ‖P *
          (cmp116PhysicalEndomorphismComplexMatrix
              (leftPart.comp pivot) *
            cmp116FinsetColumnInclusion
              (ι := CMP116PhysicalWalkCoordinate
                4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates)‖ ≤
        ‖P‖ * ((Ahead * rho ^ index.val) * geometricRow) := by
    calc
      _ ≤ ‖P‖ *
          ‖cmp116PhysicalEndomorphismComplexMatrix
              (leftPart.comp pivot) *
            cmp116FinsetColumnInclusion
              (ι := CMP116PhysicalWalkCoordinate
                4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates‖ :=
        Matrix.linfty_opNorm_mul _ _
      _ ≤ ‖P‖ *
          (‖cmp116PhysicalEndomorphismComplexMatrix
              (leftPart.comp pivot)‖ *
            ‖cmp116FinsetColumnInclusion
              (ι := CMP116PhysicalWalkCoordinate
                4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates‖) := by
        gcongr
        exact Matrix.linfty_opNorm_mul _ _
      _ ≤ ‖P‖ *
          (((Ahead * rho ^ index.val) * geometricRow) * 1) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hprefix hinclusion (norm_nonneg _)
            (mul_nonneg (mul_nonneg hAhead (pow_nonneg hrho _))
              hgeometricRow))
          (norm_nonneg P)
      _ = _ := by ring
  have hcard :
      (Fintype.card ↥activeCoordinates : ℝ) ≤
        (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) := by
    rw [Fintype.card_coe]
    exact_mod_cast
        card_cmp116SourcePi4_coordinatePivot_activeCoordinates_le
          (M := M) (Nc := Nc) anchor cube
  calc
    ‖w * Matrix.trace
        ((P *
          cmp116PhysicalEndomorphismComplexMatrix
            (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)) *
          D ^ m)‖ ≤
        (Fintype.card ↥activeCoordinates : ℝ) *
          (‖w‖ *
            ((‖cmp116FinsetCoordinateRestriction
                  (ι := CMP116PhysicalWalkCoordinate
                    4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates *
                cmp116PhysicalEndomorphismComplexMatrix rightPart‖ *
                ‖D ^ m‖) *
              ‖P *
                (cmp116PhysicalEndomorphismComplexMatrix
                    (leftPart.comp pivot) *
                  cmp116FinsetColumnInclusion
                    (ι := CMP116PhysicalWalkCoordinate
                      4 (M * (2 * Q)) Nc) (α := ℂ)
                    activeCoordinates)‖)) := hbase
    _ ≤ (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
        (‖w‖ *
          (((rho ^ (rawWalk.tail.length - index.val) * geometricRow) *
                ‖D ^ m‖) *
            (‖P‖ * ((Ahead * rho ^ index.val) * geometricRow)))) := by
      gcongr

end

end YangMills.RG
