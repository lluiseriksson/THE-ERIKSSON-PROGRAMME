/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullWeakenedPrecision

/-!
# Complete complex source `Pi^4` weakened covariance

This module complexifies the literal weakening monomials in the complete
all-head, length-ordered source covariance.  The physical operator
coefficients themselves remain the real CMP99 patched-walk coefficients,
embedded canonically in `Complex`.

The outer series stays ordered by walk length.  In particular no exchange of
two infinite sums is hidden in the definition.  Each finite complex layer is
proved to restrict exactly to the canonical matrix of the corresponding real
layer.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- One canonical physical matrix coefficient as a real continuous linear
functional on the finite endomorphism space. -/
noncomputable def cmp116PhysicalOperatorCoefficientCLM
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (source target : PhysicalBond d N)
    (input output : Fin (Nc ^ 2 - 1)) :
    (PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc) →L[ℝ] ℝ := by
  let L :
      (PhysicalGaugeOneCochain d N Nc →L[ℝ]
          PhysicalGaugeOneCochain d N Nc) →ₗ[ℝ] ℝ := {
    toFun := fun T =>
      cmp116PhysicalOperatorCoefficient
        T source target input output
    map_add' := fun T S => by
      simp [cmp116PhysicalOperatorCoefficient]
    map_smul' := fun r T => by
      simp [cmp116PhysicalOperatorCoefficient]
  }
  exact ⟨L, L.continuous_of_finiteDimensional⟩

/-- One all-head length layer with complex source weakening monomials. -/
noncomputable def cmp116SourcePi4FullComplexWeakenedCovarianceLayer
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ) (n : ℕ) :
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
        cmp116ComplexWeakeningMonomial
            (cmp116SourcePi4QuotientWalkActive
              (M := M) anchor head walk) sigma *
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

/-- Complete length-ordered complex covariance matrix. -/
noncomputable def cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  fun row col =>
    ∑' n : ℕ,
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK sigma n row col

/-- A finite complex layer restricted to real weakening parameters is exactly
the canonical coordinate matrix of the real physical layer. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceLayer_ofReal
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ) (n : ℕ) :
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun x => (s x : ℂ)) n =
      cmp116PhysicalEndomorphismComplexMatrix
        (cmp116SourcePi4FullWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK s n) := by
  classical
  funext row col
  rw [cmp116PhysicalEndomorphismComplexMatrix_apply]
  simp [cmp116SourcePi4FullComplexWeakenedCovarianceLayer,
    cmp116SourcePi4FullWeakenedCovarianceLayer,
    cmp116ComplexWeakeningMonomial_ofReal,
    cmp116ComplexPhysicalOperatorCoefficient,
    cmp116PhysicalOperatorCoefficient]

/-- At full coupling each complex layer is the canonical matrix of the exact
generated-walk layer. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceLayer_one
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ) :
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) n =
      cmp116PhysicalEndomorphismComplexMatrix
        (cmp116SourcePi4QuotientGeneratedWalkLayer
          (R := R) K hc hmass hK n) := by
  calc
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) n =
      cmp116PhysicalEndomorphismComplexMatrix
        (cmp116SourcePi4FullWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => (1 : ℝ)) n) := by
            simpa using
              cmp116SourcePi4FullComplexWeakenedCovarianceLayer_ofReal
                (R := R) anchor K hc hmass hK (fun _ => (1 : ℝ)) n
    _ = cmp116PhysicalEndomorphismComplexMatrix
        (cmp116SourcePi4QuotientGeneratedWalkLayer
          (R := R) K hc hmass hK n) := by
      rw [cmp116SourcePi4FullWeakenedCovarianceLayer_one
        (R := R) anchor K hc hmass hK n]

/-- At full coupling the complete complex series is the exact physical
covariance matrix.  The exchange with the coordinate map is justified by
the defect-contraction summability theorem. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1) =
      cmp116PhysicalEndomorphismComplexMatrix
        (cmp116SourcePi4QuotientExactPatchedCovariance
          K hc hmass hK) := by
  have hsum :=
    summable_cmp116SourcePi4QuotientGeneratedWalkLayer
      K hsourceRange hrange hc hmass hK hD
  funext row col
  let L := cmp116PhysicalOperatorCoefficientCLM
    col.1 row.1 col.2 row.2
  calc
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1) row col =
      ∑' n : ℕ,
        cmp116ComplexPhysicalOperatorCoefficient
          (cmp116SourcePi4QuotientGeneratedWalkLayer
            (R := R) K hc hmass hK n)
          col.1 row.1 col.2 row.2 := by
      rw [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix]
      apply tsum_congr
      intro n
      rw [cmp116SourcePi4FullComplexWeakenedCovarianceLayer_one
        (R := R) anchor K hc hmass hK n,
        cmp116PhysicalEndomorphismComplexMatrix_apply]
    _ = ((L (∑' n : ℕ,
        cmp116SourcePi4QuotientGeneratedWalkLayer
          (R := R) K hc hmass hK n) : ℝ) : ℂ) := by
      change (∑' n : ℕ,
          ((L (cmp116SourcePi4QuotientGeneratedWalkLayer
            (R := R) K hc hmass hK n) : ℝ) : ℂ)) =
        ((L (∑' n : ℕ,
          cmp116SourcePi4QuotientGeneratedWalkLayer
            (R := R) K hc hmass hK n) : ℝ) : ℂ)
      rw [← Complex.ofReal_tsum,
        ← L.map_tsum hsum]
    _ = cmp116PhysicalEndomorphismComplexMatrix
        (cmp116SourcePi4QuotientExactPatchedCovariance
          K hc hmass hK) row col := by
      rw [←
        cmp116SourcePi4QuotientExactPatchedCovariance_eq_tsum_generatedLayers
          K hsourceRange hrange hc hmass hK hD,
        cmp116PhysicalEndomorphismComplexMatrix_apply]
      rfl

end

end YangMills.RG
