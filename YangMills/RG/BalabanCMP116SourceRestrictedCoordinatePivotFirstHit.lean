/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedWalkFiniteRankFactorization
import YangMills.RG.BalabanCMP116MatrixTraceLinftyOpNorm
import YangMills.RG.BalabanCMP116SourceRestrictedCoordinatePivotLayer

/-!
# First-hit factorization of one restricted coordinate-pivot walk

A nonzero ordered pivot weight forces its physical contour coordinate to
belong to the weakening carrier of the walk.  The existing physical
first-hit theorem can therefore insert the projection onto the common core
of precisely the walk domains which activate that coordinate.

This is a termwise factorization.  No low-rank statement is made about the
sum of all walks in one pivot group.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- A nonzero physical coordinate-pivot walk factors through the scalar
coordinates over the common core of the domains which activate that
coordinate. -/
theorem cmp116SourcePi4ForwardWalk_matrix_eq_coordinatePivot_finiteCarrierFactors
    {n M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin n ≃ ↥carrier) (z : Fin n → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (walk : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)))
    (i : Fin n)
    (hweight :
      cmp116RestrictedOrderedPivotWeight
          (cmp116SourcePi4ForwardWalkActive anchor walk)
          carrier e z i ≠ 0) :
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
    let singletonCarrier : Finset (FinBox 4 (2 * Q)) := {cube}
    let index :=
      rawWalk.firstActiveDomainIndex domainActive cube
        (mem_active_of_cmp116RestrictedOrderedPivotWeight_ne_zero
          (cmp116SourcePi4ForwardWalkActive anchor walk)
          carrier e z i hweight)
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
    let pivot := rawWalk.firstActiveFactor
      domainActive R0 R cube
        (mem_active_of_cmp116RestrictedOrderedPivotWeight_ne_zero
          (cmp116SourcePi4ForwardWalkActive anchor walk)
          carrier e z i hweight)
    let rightPart := ((rawWalk.factors R0 R).drop (index + 1)).prod
    let activeCore := CMP99GeneralizedWalk.contourActiveCore
      (fun chart => cmp99SourcePi4ChartCore (M := M) chart.1)
      domainActive singletonCarrier
    let activeCoordinates :=
      cmp116PhysicalCoreCoordinates (Nc := Nc) activeCore
    cmp116PhysicalEndomorphismComplexMatrix
        (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk) =
      (cmp116PhysicalEndomorphismComplexMatrix (leftPart.comp pivot) *
        cmp116FinsetColumnInclusion
          (ι := CMP116PhysicalWalkCoordinate
            4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates) *
      (cmp116FinsetCoordinateRestriction
          (ι := CMP116PhysicalWalkCoordinate
            4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates *
        cmp116PhysicalEndomorphismComplexMatrix rightPart) := by
  classical
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
  simpa only [rawWalk, domainActive, cube,
    cmp116SourcePi4ForwardWalkActive,
    cmp116SourcePi4ForwardWalkOperator] using
    (cmp116PhysicalPatchWalk_matrix_eq_firstHit_finiteCarrierFactors
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK domainActive ({cube} : Finset (FinBox 4 (2 * Q)))
      rawWalk cube hactive (by simp))

/-- The trace of a nonzero pivot walk is exactly a trace on its localized
intermediate coordinate space.  This cycles one rectangular product at a
time and does not infer a rank bound for a sum of walks. -/
theorem cmp116SourcePi4ForwardWalk_trace_eq_coordinatePivot_reducedTrace
    {n M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin n ≃ ↥carrier) (z : Fin n → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (walk : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)))
    (i : Fin n)
    (hweight :
      cmp116RestrictedOrderedPivotWeight
          (cmp116SourcePi4ForwardWalkActive anchor walk)
          carrier e z i ≠ 0) :
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
    let singletonCarrier : Finset (FinBox 4 (2 * Q)) := {cube}
    let hactive : cube ∈ rawWalk.active domainActive :=
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
    let pivot := rawWalk.firstActiveFactor
      domainActive R0 R cube hactive
    let rightPart := ((rawWalk.factors R0 R).drop (index + 1)).prod
    let activeCore := CMP99GeneralizedWalk.contourActiveCore
      (fun chart => cmp99SourcePi4ChartCore (M := M) chart.1)
      domainActive singletonCarrier
    let activeCoordinates :=
      cmp116PhysicalCoreCoordinates (Nc := Nc) activeCore
    Matrix.trace
        (cmp116PhysicalEndomorphismComplexMatrix
          (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)) =
      Matrix.trace
        ((cmp116FinsetCoordinateRestriction
            (ι := CMP116PhysicalWalkCoordinate
              4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates *
            cmp116PhysicalEndomorphismComplexMatrix rightPart) *
          (cmp116PhysicalEndomorphismComplexMatrix
              (leftPart.comp pivot) *
            cmp116FinsetColumnInclusion
              (ι := CMP116PhysicalWalkCoordinate
                4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates)) := by
  classical
  dsimp only
  rw [
    cmp116SourcePi4ForwardWalk_matrix_eq_coordinatePivot_finiteCarrierFactors
      anchor carrier e z K hc hmass hK walk i hweight]
  exact Matrix.trace_mul_comm _ _

/-- A nonzero weighted pivot-walk trace costs only the dimension of its
singleton-pivot common core.  The arbitrary ambient factors `P` and `D ^ m`
remain visible for later summation over walks and trace powers. -/
theorem norm_cmp116SourcePi4ForwardWalk_coordinatePivot_weight_mul_trace_le
    {n M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin n ≃ ↥carrier) (z : Fin n → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
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
    let singletonCarrier : Finset (FinBox 4 (2 * Q)) := {cube}
    let hactive : cube ∈ rawWalk.active domainActive :=
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
    let pivot := rawWalk.firstActiveFactor
      domainActive R0 R cube hactive
    let rightPart := ((rawWalk.factors R0 R).drop (index + 1)).prod
    let activeCore := CMP99GeneralizedWalk.contourActiveCore
      (fun chart => cmp99SourcePi4ChartCore (M := M) chart.1)
      domainActive singletonCarrier
    let activeCoordinates :=
      cmp116PhysicalCoreCoordinates (Nc := Nc) activeCore
    ‖cmp116RestrictedOrderedPivotWeight
          (cmp116SourcePi4ForwardWalkActive anchor walk)
          carrier e z i *
        Matrix.trace
          ((P *
            cmp116PhysicalEndomorphismComplexMatrix
              (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)) *
            D ^ m)‖ ≤
      (Fintype.card ↥activeCoordinates : ℝ) *
        (‖cmp116RestrictedOrderedPivotWeight
              (cmp116SourcePi4ForwardWalkActive anchor walk)
              carrier e z i‖ *
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
                    4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates)‖)) := by
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
  let pivot := rawWalk.firstActiveFactor
    domainActive R0 R cube hactive
  let rightPart := ((rawWalk.factors R0 R).drop (index + 1)).prod
  let activeCore := CMP99GeneralizedWalk.contourActiveCore
    (fun chart => cmp99SourcePi4ChartCore (M := M) chart.1)
    domainActive ({cube} : Finset (FinBox 4 (2 * Q)))
  let activeCoordinates :=
    cmp116PhysicalCoreCoordinates (Nc := Nc) activeCore
  let A :=
    cmp116PhysicalEndomorphismComplexMatrix (leftPart.comp pivot) *
      cmp116FinsetColumnInclusion
        (ι := CMP116PhysicalWalkCoordinate
          4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates
  let B :=
    cmp116FinsetCoordinateRestriction
        (ι := CMP116PhysicalWalkCoordinate
          4 (M * (2 * Q)) Nc) (α := ℂ) activeCoordinates *
      cmp116PhysicalEndomorphismComplexMatrix rightPart
  let w :=
    cmp116RestrictedOrderedPivotWeight
      (cmp116SourcePi4ForwardWalkActive anchor walk) carrier e z i
  have hfactor :=
    cmp116SourcePi4ForwardWalk_matrix_eq_coordinatePivot_finiteCarrierFactors
      anchor carrier e z K hc hmass hK walk i hweight
  dsimp only at hfactor
  change
    cmp116PhysicalEndomorphismComplexMatrix
        (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk) =
      A * B at hfactor
  change
    ‖w *
        Matrix.trace
          ((P *
            cmp116PhysicalEndomorphismComplexMatrix
              (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)) *
            D ^ m)‖ ≤
      (Fintype.card ↥activeCoordinates : ℝ) *
        (‖w‖ * ((‖B‖ * ‖D ^ m‖) * ‖P * A‖))
  rw [hfactor]
  simpa only [Matrix.mul_assoc] using
    (norm_scalar_mul_trace_rectangular_mul_pow_le_card_mul
      w (P * A) B D m)

end

end YangMills.RG
