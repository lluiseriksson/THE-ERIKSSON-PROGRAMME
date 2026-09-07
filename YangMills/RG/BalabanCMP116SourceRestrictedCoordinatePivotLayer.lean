/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedMonomialLinearTelescope
import YangMills.RG.BalabanCMP116SourceRestrictedTerminalComplexDefectLayer

/-!
# Coordinate-pivot decomposition of a restricted source defect layer

The exact restricted terminal layer is reorganized with the physical Cauchy
coordinate outside the finite walk sum.  This replaces the nonempty-powerset
expansion by exactly `n = carrier.card` pivot groups.

No operator factorization is claimed here.  The next stage must split every
walk in pivot group `i` at the first domain which activates the physical
coordinate `e i`.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- A restricted terminal covariance-defect layer is the finite sum of its
ordered physical coordinate-pivot groups. -/
theorem cmp116SourcePi4TerminalComplexDefectLayer_restricted_eq_sum_coordinatePivots
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
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    cmp116SourcePi4TerminalComplexDefectLayer
        (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling carrier e z)
        layer terminal row col =
      ∑ i : Fin n,
        ∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R layer terminal,
          cmp116RestrictedOrderedPivotWeight
              (cmp116SourcePi4ForwardWalkActive anchor walk)
              carrier e z i *
            cmp116ComplexPhysicalOperatorCoefficient
              (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
              col.1 row.1 col.2 row.2 := by
  classical
  unfold cmp116SourcePi4TerminalComplexDefectLayer
  simp_rw [
    cmp116ComplexWeakeningMonomial_restricted_sub_one_eq_sum_pivotWeight,
    Finset.sum_mul]
  rw [Finset.sum_comm]

end

end YangMills.RG
