/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ConnectedLocalizationRegrouping
import YangMills.RG.BalabanCMP116SourcePi4FullComplexWeakenedCovarianceDerivative

/-!
# Connected localization of a physical derivative layer

For a fixed walk length and weakening coordinate, the derivative layer is a
finite family of literal physical patched walks.  This module packages that
dependent head/tail family as one finite source and regroups it by the
canonical face-connected component of its active carrier containing the
differentiated cube.

The resulting identity is the source-specific finite regrouping needed after
one FTC step.  It does not yet identify the grouped coefficient with the
complete CMP116 activity `V_k(Y, B)` or prove `(1.43)`.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The literal dependent finite index of all physical source walks in one
length layer. -/
abbrev CMP116SourcePi4LayerWalkIndex
    (M Q R n : ℕ) [NeZero M] [NeZero Q] :=
  Σ head : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)),
    ↥(cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R)
      head n)

/-- The anchored walk represented by one dependent layer index. -/
def CMP116SourcePi4LayerWalkIndex.walk
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n) :
    CMP99AnchoredWalk
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R)
      idx.1 :=
  ⟨n, idx.2⟩

/-- Literal source active carrier of a layer index. -/
noncomputable def cmp116SourcePi4LayerWalkActive
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp116SourcePi4QuotientWalkActive
    (M := M) anchor idx.1 idx.walk

/-- Literal scalar contribution of one physical walk to a coordinate
derivative layer. -/
noncomputable def cmp116SourcePi4DerivativeLayerWalkTerm
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n) : ℂ :=
  (if d ∈ cmp116SourcePi4LayerWalkActive anchor idx then
    cmp116ComplexWeakeningMonomial
      ((cmp116SourcePi4LayerWalkActive anchor idx).erase d) sigma
  else 0) *
    cmp116ComplexPhysicalOperatorCoefficient
      (idx.walk.term
        (cmp99PhysicalPatchHead
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK))
      col.1 row.1 col.2 row.2

/-- One physical derivative layer is exactly the sum of its coefficients
grouped by the canonical face-connected localization domain containing the
differentiated weakening cube. -/
theorem
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative_eq_sum_anchoredFiber
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative
        (R := R) anchor K hc hmass hK sigma d n row col =
      ∑ Y ∈ cmp116AnchoredLocalizationDomains
          (cmp116CoarseFaceAdj 4 (2 * Q))
          (Finset.univ :
            Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
          (fun _ => d)
          (cmp116SourcePi4LayerWalkActive anchor),
        cmp116AnchoredFiberCoefficient
          (cmp116CoarseFaceAdj 4 (2 * Q))
          (Finset.univ :
            Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
          (fun _ => d)
          (cmp116SourcePi4LayerWalkActive anchor)
          (cmp116SourcePi4DerivativeLayerWalkTerm
            anchor K hc hmass hK sigma d row col) Y := by
  classical
  have hregroup :=
    cmp116_sum_eq_sum_anchoredFiberCoefficient
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (Finset.univ :
        Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
      (fun _ => d)
      (cmp116SourcePi4LayerWalkActive anchor)
      (cmp116SourcePi4DerivativeLayerWalkTerm
        anchor K hc hmass hK sigma d row col)
  rw [Fintype.sum_sigma] at hregroup
  simpa [cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative,
    cmp116SourcePi4DerivativeLayerWalkTerm,
    cmp116SourcePi4LayerWalkActive,
    CMP116SourcePi4LayerWalkIndex.walk] using hregroup

end

end YangMills.RG
