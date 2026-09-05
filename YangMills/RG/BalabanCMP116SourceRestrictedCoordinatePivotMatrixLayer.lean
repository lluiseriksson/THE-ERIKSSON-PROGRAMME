/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedCoordinatePivotFirstHit

/-!
# Matrix coordinate-pivot decomposition of one restricted defect layer

The entrywise source decomposition is promoted to an equality of matrices.
Consequently a trace containing one finite terminal layer distributes exactly
over its physical coordinate pivots and forward walks.

This file performs no infinite rearrangement and makes no rank claim about a
sum of walks.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- One restricted terminal defect layer is exactly the finite sum of its
coordinate-pivot walk matrices. -/
theorem cmp116SourcePi4TerminalComplexDefectLayer_restricted_eq_sum_coordinatePivotMatrices
    {n M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin n ≃ ↥carrier) (z : Fin n → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (layer : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    cmp116SourcePi4TerminalComplexDefectLayer
        (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling carrier e z)
        layer terminal =
      ∑ i : Fin n,
        ∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R layer terminal,
          cmp116RestrictedOrderedPivotWeight
              (cmp116SourcePi4ForwardWalkActive anchor walk)
              carrier e z i •
            cmp116PhysicalEndomorphismComplexMatrix
              (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk) := by
  classical
  ext row col
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    cmp116PhysicalEndomorphismComplexMatrix_apply] using
    (cmp116SourcePi4TerminalComplexDefectLayer_restricted_eq_sum_coordinatePivots
      (R := R) anchor carrier e z K hc hmass hK layer terminal row col)

/-- After multiplying by an arbitrary ambient left factor and defect power,
the trace of one terminal layer is still the exact finite sum of its physical
pivot-walk traces. -/
theorem cmp116SourcePi4TerminalComplexDefectLayer_restricted_trace_mul_pow_eq_sum_coordinatePivots
    {n M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin n ≃ ↥carrier) (z : Fin n → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (layer : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (P D : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (m : ℕ) :
    Matrix.trace
        ((P *
          cmp116SourcePi4TerminalComplexDefectLayer
            (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling carrier e z)
            layer terminal) * D ^ m) =
      ∑ i : Fin n,
        ∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R layer terminal,
          cmp116RestrictedOrderedPivotWeight
              (cmp116SourcePi4ForwardWalkActive anchor walk)
              carrier e z i *
            Matrix.trace
              ((P *
                cmp116PhysicalEndomorphismComplexMatrix
                  (cmp116SourcePi4ForwardWalkOperator
                    K hc hmass hK walk)) * D ^ m) := by
  classical
  rw [
    cmp116SourcePi4TerminalComplexDefectLayer_restricted_eq_sum_coordinatePivotMatrices
      (R := R) anchor carrier e z K hc hmass hK layer terminal]
  simp_rw [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- The trace containing one complete length layer expands exactly over its
source terminal groups, physical coordinate pivots, and forward walks. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceLayer_restricted_trace_mul_pow_eq_sum_coordinatePivots
    {n M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin n ≃ ↥carrier) (z : Fin n → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (layer : ℕ)
    (P D : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (m : ℕ) :
    Matrix.trace
        ((P *
          (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
              (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling carrier e z) layer -
            cmp116SourcePi4FullComplexWeakenedCovarianceLayer
              (R := R) anchor K hc hmass hK (fun _ => 1) layer)) *
          D ^ m) =
      ∑ terminal : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        ∑ i : Fin n,
          ∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
              (cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q))
              (cmp99SourcePi4ChartCore (M := M))
              cmp99SourcePi4ChartEnlarged physicalBondDist R layer terminal,
            cmp116RestrictedOrderedPivotWeight
                (cmp116SourcePi4ForwardWalkActive anchor walk)
                carrier e z i *
              Matrix.trace
                ((P *
                  cmp116PhysicalEndomorphismComplexMatrix
                    (cmp116SourcePi4ForwardWalkOperator
                      K hc hmass hK walk)) * D ^ m) := by
  classical
  rw [←
    sum_cmp116SourcePi4TerminalComplexDefectLayer_restricted
      (R := R) anchor carrier e z K hc hmass hK layer]
  simp_rw [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum,
    cmp116SourcePi4TerminalComplexDefectLayer_restricted_trace_mul_pow_eq_sum_coordinatePivots
      (R := R) anchor carrier e z K hc hmass hK layer]

end

end YangMills.RG
