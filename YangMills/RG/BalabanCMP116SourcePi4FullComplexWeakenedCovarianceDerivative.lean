/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexWeakenedCovariance

/-!
# Coordinate derivatives of the physical weakened covariance layers

Each finite length layer of the complete source `Pi^4` covariance is a finite
sum of literal weakening monomials times physical patched-walk coefficients.
This file differentiates that concrete layer with respect to one complex
weakening coordinate.  No abstract differentiability field and no
differentiation under an infinite sum are used.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The literal coordinate derivative of one finite complex covariance
layer.  A walk contributes precisely when its active carrier contains the
chosen weakening cube, and that cube is erased from its monomial. -/
noncomputable def
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q)) (n : ℕ) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  fun row col =>
    ∑ head : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)),
      ∑ tail : ↥(cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged
            physicalBondDist R)
          head n),
        let walk : CMP99AnchoredWalk
            (cmp99PhysicalPatchSuccessorSteps
              (cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q))
              (cmp99SourcePi4ChartCore (M := M))
              cmp99SourcePi4ChartEnlarged
              physicalBondDist R)
            head := ⟨n, tail⟩
        (if d ∈ cmp116SourcePi4QuotientWalkActive
              (M := M) anchor head walk then
          cmp116ComplexWeakeningMonomial
            ((cmp116SourcePi4QuotientWalkActive
              (M := M) anchor head walk).erase d) sigma
        else 0) *
          cmp116ComplexPhysicalOperatorCoefficient
            (walk.term
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

/-- One finite physical covariance layer is complex differentiable in every
weakening coordinate, with derivative given by the literal erased-monomial
sum. -/
theorem
    hasDerivAt_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_update
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q)) (n : ℕ)
    (row col : CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
    (t : ℂ) :
    HasDerivAt
      (fun z =>
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK
          (Function.update sigma d z) n row col)
      (cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative
        (R := R) anchor K hc hmass hK sigma d n row col)
      t := by
  classical
  unfold cmp116SourcePi4FullComplexWeakenedCovarianceLayer
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerDerivative
  let term :
      (head : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))) →
      ↥(cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        head n) → ℂ → ℂ :=
    fun head tail z =>
      let walk : CMP99AnchoredWalk
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R) head :=
        ⟨n, tail⟩
      cmp116ComplexWeakeningMonomial
          (cmp116SourcePi4QuotientWalkActive
            (M := M) anchor head walk)
          (Function.update sigma d z) *
        cmp116ComplexPhysicalOperatorCoefficient
          (walk.term
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
  let derivative :
      (head : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))) →
      ↥(cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        head n) → ℂ :=
    fun head tail =>
      let walk : CMP99AnchoredWalk
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R) head :=
        ⟨n, tail⟩
      (if d ∈ cmp116SourcePi4QuotientWalkActive
            (M := M) anchor head walk then
        cmp116ComplexWeakeningMonomial
          ((cmp116SourcePi4QuotientWalkActive
            (M := M) anchor head walk).erase d) sigma
      else 0) *
        cmp116ComplexPhysicalOperatorCoefficient
          (walk.term
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
  have hsum : HasDerivAt
      (fun z => ∑ head, ∑ tail, term head tail z)
      (∑ head, ∑ tail, derivative head tail) t := by
    apply HasDerivAt.fun_sum
    intro head _
    apply HasDerivAt.fun_sum
    intro tail _
    dsimp only [term, derivative]
    let walk : CMP99AnchoredWalk
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R) head :=
      ⟨n, tail⟩
    let active :=
      cmp116SourcePi4QuotientWalkActive (M := M) anchor head walk
    let coefficient : ℂ :=
      cmp116ComplexPhysicalOperatorCoefficient
        (walk.term
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
    change HasDerivAt
      (fun z =>
        cmp116ComplexWeakeningMonomial active
          (Function.update sigma d z) * coefficient)
      ((if d ∈ active then
        cmp116ComplexWeakeningMonomial (active.erase d) sigma else 0) *
          coefficient) t
    by_cases hd : d ∈ active
    · simp_rw [cmp116ComplexWeakeningMonomial_update_of_mem
        active sigma d hd]
      simp only [hd, if_true]
      simpa only [id, one_mul, mul_assoc] using
        (hasDerivAt_id t).mul_const
          (cmp116ComplexWeakeningMonomial
            (active.erase d) sigma * coefficient)
    · simp_rw [cmp116ComplexWeakeningMonomial_update_of_not_mem
        active sigma d hd]
      simp only [hd, if_false, zero_mul]
      exact hasDerivAt_const t
        (cmp116ComplexWeakeningMonomial active sigma * coefficient)
  simpa [term, derivative] using hsum

end

end YangMills.RG
