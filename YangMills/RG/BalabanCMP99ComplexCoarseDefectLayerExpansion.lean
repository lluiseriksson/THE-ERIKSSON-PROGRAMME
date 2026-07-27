/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexCoarseNeumannExpansion
import YangMills.RG.BalabanCMP116SourceRestrictedCoordinatePivotTsumTrace

/-!
# Fine-layer expansion of the complex CMP99 coarse defect

The coarse Neumann series is useful for localization only after its relative
defect is exposed as the image of the already localized fine covariance
layers.  This module performs that passage through the literal maps

`C₀ Q (C(σ) - C(1)) Q*`

by a continuous rectangular sandwich map.  Thus no independent coarse
kernel or convergence assumption is introduced.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

/-- Continuous two-sided multiplication between finite matrix spaces. -/
noncomputable def complexRectangularSandwichCLM
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (left : Matrix κ ι ℂ) (right : Matrix ι κ ℂ) :
    Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ := by
  let L : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ := {
    toFun := fun X => left * X * right
    map_add' := fun X Y => by
      simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := fun r X => by
      simp [Matrix.mul_smul, Matrix.smul_mul]
  }
  exact ⟨L, L.continuous_of_finiteDimensional⟩

theorem complexRectangularSandwichCLM_apply
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (left : Matrix κ ι ℂ) (right : Matrix ι κ ℂ)
    (X : Matrix ι ι ℂ) :
    complexRectangularSandwichCLM left right X =
      left * X * right := rfl

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

/-- One physical fine covariance-difference layer transported to the
relative coarse-middle defect. -/
noncomputable def cmp99SourcePi4ComplexCoarseRelativeDefectLayer
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (layer : ℕ) :
    Matrix (CoarseCoord Q Nc) (CoarseCoord Q Nc) ℂ :=
  complexRectangularSandwichCLM
      (cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance *
        cmp99SourcePi4ComplexBlockMatrix
          (M := M) (Q := Q) (Nc := Nc))
      (cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc))
    (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK sigma layer -
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) layer)

/-- Summability of the physical fine difference layers passes directly to
the relative coarse defect layers. -/
theorem summable_cmp99SourcePi4ComplexCoarseRelativeDefectLayer
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hdiff : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma layer -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) layer) :
    Summable fun layer : ℕ =>
      cmp99SourcePi4ComplexCoarseRelativeDefectLayer
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma layer := by
  unfold cmp99SourcePi4ComplexCoarseRelativeDefectLayer
  exact
    (complexRectangularSandwichCLM
      (cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance *
        cmp99SourcePi4ComplexBlockMatrix
          (M := M) (Q := Q) (Nc := Nc))
      (cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc))).summable hdiff

/-- The literal relative coarse defect is exactly the norm-convergent sum
of the transported physical fine layers. -/
theorem
    cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_eq_tsum_layers
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hdiff : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma layer -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) layer)
    (hone : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) layer) :
    cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
        (R := R) anchor K hc hmass hK baseCoarseCovariance sigma =
      ∑' layer : ℕ,
        cmp99SourcePi4ComplexCoarseRelativeDefectLayer
          (R := R) anchor K hc hmass hK
          baseCoarseCovariance sigma layer := by
  let left :=
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance *
      cmp99SourcePi4ComplexBlockMatrix
        (M := M) (Q := Q) (Nc := Nc)
  let right :=
    cmp99SourcePi4ComplexBlockAdjointMatrix
      (M := M) (Q := Q) (Nc := Nc)
  let diffLayer := fun layer : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK sigma layer -
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) layer
  rw [cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect,
    cmp99SourcePi4FullComplexCoarseMiddleMatrix_sub_one,
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_eq_tsum_layers
      anchor K hc hmass hK sigma hdiff hone]
  calc
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance *
          (cmp99SourcePi4ComplexBlockMatrix
              (M := M) (Q := Q) (Nc := Nc) *
              (∑' layer : ℕ, diffLayer layer) *
            cmp99SourcePi4ComplexBlockAdjointMatrix
              (M := M) (Q := Q) (Nc := Nc)) =
        left * (∑' layer : ℕ, diffLayer layer) * right := by
          dsimp [left, right]
          simp only [Matrix.mul_assoc]
    _ = complexRectangularSandwichCLM left right
          (∑' layer : ℕ, diffLayer layer) := rfl
    _ = ∑' layer : ℕ,
          complexRectangularSandwichCLM left right (diffLayer layer) :=
      (complexRectangularSandwichCLM left right).map_tsum hdiff
    _ = ∑' layer : ℕ,
          cmp99SourcePi4ComplexCoarseRelativeDefectLayer
            (R := R) anchor K hc hmass hK
            baseCoarseCovariance sigma layer := by
      apply tsum_congr
      intro layer
      rfl

/-- The source contour certificate generates the complete fine-to-coarse
layer expansion.  In particular the caller supplies neither summability of
the fine difference nor summability of the full-coupling layers. -/
theorem
    cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_eq_tsum_layers_of_source
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
        (R := R) anchor K hc hmass hK baseCoarseCovariance sigma =
      ∑' layer : ℕ,
        cmp99SourcePi4ComplexCoarseRelativeDefectLayer
          (R := R) anchor K hc hmass hK
          baseCoarseCovariance sigma layer := by
  have hdiffLayers :
      Summable fun layer : ℕ =>
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
            (R := R) anchor K hc hmass hK sigma layer -
          cmp116SourcePi4FullComplexWeakenedCovarianceLayer
            (R := R) anchor K hc hmass hK (fun _ => 1) layer :=
    summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 sigma hradius hRweak hdiff hcap hsmall
  have honeLayers :
      Summable fun layer : ℕ =>
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) layer :=
    summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_one
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 hRweak hsmall
  exact
    cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_eq_tsum_layers
      anchor K hc hmass hK baseCoarseCovariance sigma
      hdiffLayers honeLayers

end

end YangMills.RG
