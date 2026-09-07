/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePi4WeakenedCoarseMiddle
import YangMills.RG.BalabanCMP116SourcePi4FullComplexContourNonsingularity

/-!
# Complex rectangular CMP99 source minimizer

The complete source weakening is naturally a complex matrix on fine
one-cochain coordinates.  CMP99 equation (3.126) additionally requires the
rectangular block map and the inverse of the coarse middle.  This module
constructs those matrices with their exact fine/coarse index types:

`M(σ) = Q C(σ) Q*`,

`H(σ) = C(σ) Q* M(σ)⁻¹`.

At full coupling they recover the canonical coordinate matrices of the
physical coarse middle and physical background minimizer.  Nonsingularity
away from full coupling is expressed first through the literal relative
coarse-middle defect; later source estimates can bound that concrete object.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

private abbrev CoarseCoord (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] :=
  CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc

/-- Canonical real coordinate matrix of a rectangular map between two
physical one-cochain lattices. -/
noncomputable def cmp99PhysicalRectangularRealMatrix
    {N₁ N₂ Nc : ℕ} [NeZero N₁] [NeZero N₂]
    (T : PhysicalGaugeOneCochain 4 N₁ Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 N₂ Nc) :
    Matrix (CMP116PhysicalWalkCoordinate 4 N₂ Nc)
      (CMP116PhysicalWalkCoordinate 4 N₁ Nc) ℝ :=
  LinearMap.toMatrix'
    (cmp116PhysicalCoordinateLinearEquiv.symm.toLinearMap.comp
      (T.toLinearMap.comp
        cmp116PhysicalCoordinateLinearEquiv.toLinearMap))

/-- Complexification of the rectangular physical coordinate matrix. -/
noncomputable def cmp99PhysicalRectangularComplexMatrix
    {N₁ N₂ Nc : ℕ} [NeZero N₁] [NeZero N₂]
    (T : PhysicalGaugeOneCochain 4 N₁ Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 N₂ Nc) :
    Matrix (CMP116PhysicalWalkCoordinate 4 N₂ Nc)
      (CMP116PhysicalWalkCoordinate 4 N₁ Nc) ℂ :=
  (cmp99PhysicalRectangularRealMatrix T).map Complex.ofRealHom

/-- Rectangular coordinate matrices preserve physical composition. -/
theorem cmp99PhysicalRectangularComplexMatrix_comp
    {N₁ N₂ N₃ Nc : ℕ} [NeZero N₁] [NeZero N₂] [NeZero N₃]
    (T : PhysicalGaugeOneCochain 4 N₂ Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 N₃ Nc)
    (S : PhysicalGaugeOneCochain 4 N₁ Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 N₂ Nc) :
    cmp99PhysicalRectangularComplexMatrix (T.comp S) =
      cmp99PhysicalRectangularComplexMatrix T *
        cmp99PhysicalRectangularComplexMatrix S := by
  rw [cmp99PhysicalRectangularComplexMatrix,
    cmp99PhysicalRectangularComplexMatrix,
    cmp99PhysicalRectangularComplexMatrix,
    cmp99PhysicalRectangularRealMatrix,
    cmp99PhysicalRectangularRealMatrix,
    cmp99PhysicalRectangularRealMatrix]
  rw [show
    cmp116PhysicalCoordinateLinearEquiv.symm.toLinearMap.comp
        ((T.comp S).toLinearMap.comp
          cmp116PhysicalCoordinateLinearEquiv.toLinearMap) =
      (cmp116PhysicalCoordinateLinearEquiv.symm.toLinearMap.comp
        (T.toLinearMap.comp
          cmp116PhysicalCoordinateLinearEquiv.toLinearMap)).comp
      (cmp116PhysicalCoordinateLinearEquiv.symm.toLinearMap.comp
        (S.toLinearMap.comp
          cmp116PhysicalCoordinateLinearEquiv.toLinearMap)) by
        apply LinearMap.ext
        intro x
        simp [LinearMap.comp_apply]]
  rw [LinearMap.toMatrix'_comp, Matrix.map_mul]

/-- In the square case the rectangular construction is the existing
canonical endomorphism matrix. -/
theorem cmp99PhysicalRectangularComplexMatrix_eq_endomorphismMatrix
    {N Nc : ℕ} [NeZero N]
    (T : PhysicalGaugeOneCochain 4 N Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 N Nc) :
    cmp99PhysicalRectangularComplexMatrix T =
      cmp116PhysicalEndomorphismComplexMatrix T := by
  rfl

/-- Complex coordinate matrix of the literal fine-to-coarse block map. -/
noncomputable def cmp99SourcePi4ComplexBlockMatrix
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :
    Matrix (CoarseCoord Q Nc) (FineCoord M Q Nc) ℂ :=
  cmp99PhysicalRectangularComplexMatrix
    (flatBlockConstraintQCLM (d := 4) (Nc := Nc) M (2 * Q))

/-- Complex coordinate matrix of the literal coarse-to-fine adjoint. -/
noncomputable def cmp99SourcePi4ComplexBlockAdjointMatrix
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :
    Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
  cmp99PhysicalRectangularComplexMatrix
    (flatBlockConstraintQCLM (d := 4) (Nc := Nc) M (2 * Q)).adjoint

/-- Literal complex coarse middle `Q C(σ) Q*`. -/
noncomputable def cmp99SourcePi4FullComplexCoarseMiddleMatrix
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
  (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    Matrix (CoarseCoord Q Nc) (CoarseCoord Q Nc) ℂ :=
  (cmp99SourcePi4ComplexBlockMatrix (M := M) (Q := Q) (Nc := Nc) *
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma) *
    cmp99SourcePi4ComplexBlockAdjointMatrix
      (M := M) (Q := Q) (Nc := Nc)

/-- At full coupling the complex coarse middle is the canonical matrix of
the physical coarse middle built with the exact patched covariance. -/
theorem cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_eq_exact
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
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
    cmp99SourcePi4FullComplexCoarseMiddleMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1) =
      cmp116PhysicalEndomorphismComplexMatrix
        ((flatBlockConstraintQCLM (d := 4) (Nc := Nc) M (2 * Q)).comp
          ((cmp116SourcePi4QuotientExactPatchedCovariance
            K hc hmass hK).comp
            (flatBlockConstraintQCLM
              (d := 4) (Nc := Nc) M (2 * Q)).adjoint)) := by
  rw [cmp99SourcePi4FullComplexCoarseMiddleMatrix,
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD]
  unfold cmp99SourcePi4ComplexBlockMatrix
    cmp99SourcePi4ComplexBlockAdjointMatrix
  rw [← cmp99PhysicalRectangularComplexMatrix_eq_endomorphismMatrix]
  rw [← cmp99PhysicalRectangularComplexMatrix_comp,
    ← cmp99PhysicalRectangularComplexMatrix_comp]
  exact cmp99PhysicalRectangularComplexMatrix_eq_endomorphismMatrix _

/-- Literal relative defect of the complex coarse middle from full
coupling. -/
noncomputable def cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    Matrix (CoarseCoord Q Nc) (CoarseCoord Q Nc) ℂ :=
  cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance *
    (cmp99SourcePi4FullComplexCoarseMiddleMatrix
        (R := R) anchor K hc hmass hK sigma -
      cmp99SourcePi4FullComplexCoarseMiddleMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1))

/-- The source complex background minimizer matrix
`C(σ) Q* (Q C(σ) Q*)⁻¹`. -/
noncomputable def cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
  (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma *
    cmp99SourcePi4ComplexBlockAdjointMatrix
      (M := M) (Q := Q) (Nc := Nc)) *
    (cmp99SourcePi4FullComplexCoarseMiddleMatrix
      (R := R) anchor K hc hmass hK sigma)⁻¹

end

end YangMills.RG
