/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq223CovarianceOpNorm
import YangMills.RG.PhysicalGaugeCMP116OperatorTransport
import YangMills.RG.PhysicalGaugeCMP116Dictionary

/-!
# CMP116 equation (2.23): physical covariance root as a finite matrix

The exact Gaussian evaluator uses a matrix on the flattened bond/Lie-coordinate
space.  The physical source layer instead provides a covariance-root operator
on physical one-cochains together with its transport into CMP116 coordinates.
This module closes their finite-dimensional identification.

It constructs the canonical flattened linear map and its standard-basis
matrix, proves the literal `mulVec` identity, and finally proves that unflattening
the matrix output and transporting it through the physical coordinate chart is
exactly application of the original physical covariance root.

Honest scope: this identifies the matrix `R` once a certified physical root and
coordinate transport are supplied.  It does not construct that root, prove its
source norm/smallness estimate, or identify the remaining weights in CMP116
(2.14).
-/

namespace YangMills.RG

open Matrix

/-- Linear flattening/unflattening between the literal CMP116 scalar index and
the cube-indexed fluctuation-field representation. -/
noncomputable def cmp116FlatLinearEquiv
    {d L lieDim : ℕ} :
    (CMP116CoordIndex d L lieDim → ℝ) ≃ₗ[ℝ]
      CMP116FluctuationField d L lieDim where
  toFun x q a := x (q, a)
  invFun x qa := x qa.1 qa.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

namespace PhysicalRootToCMP116OperatorTransport

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
variable
  {root :
    PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc}
variable
  {rootWeight :
    PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}

/-- The transported physical root as a linear endomorphism of the flattened
CMP116 scalar-coordinate space. -/
noncomputable def flatRootLinearMap
    (A : PhysicalRootToCMP116OperatorTransport
      (d := d) (L := L) (lieDim := lieDim) root rootWeight) :
    (CMP116CoordIndex d L lieDim → ℝ) →ₗ[ℝ]
      (CMP116CoordIndex d L lieDim → ℝ) :=
  cmp116FlatLinearEquiv.symm.toLinearMap.comp
    (A.rootOperator.toLinearMap.comp cmp116FlatLinearEquiv.toLinearMap)

/-- The canonical standard-basis covariance-root matrix associated with the
transported physical root. -/
noncomputable def rootMatrix
    (A : PhysicalRootToCMP116OperatorTransport
      (d := d) (L := L) (lieDim := lieDim) root rootWeight) :
    Matrix (CMP116CoordIndex d L lieDim) (CMP116CoordIndex d L lieDim) ℝ :=
  LinearMap.toMatrix' A.flatRootLinearMap

/-- Matrix multiplication is literally the flattened transported root map. -/
theorem rootMatrix_mulVec
    (A : PhysicalRootToCMP116OperatorTransport
      (d := d) (L := L) (lieDim := lieDim) root rootWeight)
    (x : CMP116CoordIndex d L lieDim → ℝ) :
    A.rootMatrix *ᵥ x = A.flatRootLinearMap x := by
  exact LinearMap.toMatrix'_mulVec A.flatRootLinearMap x

/-- Coordinatewise form of the physical-root matrix identification. -/
theorem rootMatrix_mulVec_apply
    (A : PhysicalRootToCMP116OperatorTransport
      (d := d) (L := L) (lieDim := lieDim) root rootWeight)
    (x : CMP116CoordIndex d L lieDim → ℝ)
    (qa : CMP116CoordIndex d L lieDim) :
    (A.rootMatrix *ᵥ x) qa =
      A.rootOperator (fun q a => x (q, a)) qa.1 qa.2 := by
  rw [A.rootMatrix_mulVec x]
  rfl

/-- Terminal physical fidelity statement: after unflattening and applying the
coordinate transport, the matrix output is exactly the original physical
covariance root applied to the transported input field. -/
theorem coordinates_unflatten_rootMatrix_mulVec
    (A : PhysicalRootToCMP116OperatorTransport
      (d := d) (L := L) (lieDim := lieDim) root rootWeight)
    (x : CMP116CoordIndex d L lieDim → ℝ) :
    A.coordinates (fun q a => (A.rootMatrix *ᵥ x) (q, a)) =
      root (A.coordinates (fun q a => x (q, a))) := by
  have hflat :
      (fun q a => (A.rootMatrix *ᵥ x) (q, a)) =
        A.rootOperator (fun q a => x (q, a)) := by
    funext q a
    exact A.rootMatrix_mulVec_apply x (q, a)
  rw [hflat, A.coordinates_rootOperator]

end PhysicalRootToCMP116OperatorTransport
end YangMills.RG
