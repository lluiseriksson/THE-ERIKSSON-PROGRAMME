/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4TerminalComplexDefectLayer
import YangMills.RG.BalabanCMP116SourceRestrictedShiftedComplexContour

/-!
# The complete contour defect only sees walks meeting the local carrier

For the localized Cauchy coupling, the coefficient of a forward walk depends
only on the intersection of its complete weakening carrier with `Z₀`.
Consequently a walk disjoint from `Z₀` contributes exactly zero.  This is an
exact sparsity statement at the walk level; it does not claim unsupported
bilateral matrix support or a determinant estimate.
-/

namespace YangMills.RG

noncomputable section

open scoped BigOperators

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The scalar defect coefficient of a forward walk vanishes exactly when
its complete active carrier misses the localized contour carrier. -/
theorem cmp116SourcePi4ForwardWalkRestrictedDefectCoefficient_eq_zero_of_disjoint
    {n Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin n ≃ ↥contourCarrier) (z : Fin n → ℂ)
    (walk : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)))
    (hdisjoint :
      Disjoint
        (cmp116SourcePi4ForwardWalkActive anchor walk) contourCarrier) :
    cmp116ComplexWeakeningMonomial
          (cmp116SourcePi4ForwardWalkActive anchor walk)
          (cmp116SourceRestrictedShiftedCoupling contourCarrier e z) - 1 = 0 := by
  exact
    cmp116ComplexWeakeningMonomial_restrictedShiftedCoupling_sub_one_eq_zero
      (cmp116SourcePi4ForwardWalkActive anchor walk)
      contourCarrier e z hdisjoint

/-- In a restricted terminal defect layer, every weakening monomial can be
rewritten on the literal intersection `walkActive ∩ Z₀`. -/
theorem cmp116SourcePi4TerminalComplexDefectLayer_restricted_eq
    {n M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin n ≃ ↥contourCarrier) (z : Fin n → ℂ)
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
        (cmp116SourceRestrictedShiftedCoupling contourCarrier e z)
        layer terminal row col =
      ∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R layer terminal,
        (cmp116ComplexWeakeningMonomial
            (cmp116SourcePi4ForwardWalkActive anchor walk ∩ contourCarrier)
            (cmp116SourceRestrictedShiftedCoupling
              contourCarrier e z) - 1) *
          cmp116ComplexPhysicalOperatorCoefficient
            (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
            col.1 row.1 col.2 row.2 := by
  classical
  unfold cmp116SourcePi4TerminalComplexDefectLayer
  apply Finset.sum_congr rfl
  intro walk hwalk
  rw [cmp116ComplexWeakeningMonomial_restrictedShiftedCoupling]

/-- The terminal decomposition of the complete covariance defect remains
exact for the restricted coupling. -/
theorem sum_cmp116SourcePi4TerminalComplexDefectLayer_restricted
    {n M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin n ≃ ↥contourCarrier) (z : Fin n → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (layer : ℕ) :
    (∑ terminal : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)),
      cmp116SourcePi4TerminalComplexDefectLayer
        (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling contourCarrier e z)
        layer terminal) =
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling contourCarrier e z) layer -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) layer := by
  exact sum_cmp116SourcePi4TerminalComplexDefectLayer
    (R := R) anchor K hc hmass hK
    (cmp116SourceRestrictedShiftedCoupling contourCarrier e z) layer

end

end YangMills.RG
