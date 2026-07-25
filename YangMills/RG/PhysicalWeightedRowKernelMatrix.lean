/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalWeightedRowKernel
import YangMills.RG.BalabanCMP116Eq214ContourRelativeNorm
import YangMills.RG.BalabanCMP116PhysicalEndomorphismMatrix

/-!
# Matrix consequences of a physical weighted-row bound

A fixed-rate weighted row estimate contains a pointwise exponential estimate:
one nonnegative row summand is bounded by the whole row.  The canonical
bond--Lie matrix therefore has a volume-uniform `L∞` norm bound after summing
the explicit Lie multiplicity and physical metric shells.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- The canonical complex matrix of a physical operator inherits a
volume-uniform `L∞` bound from its weighted-row kernel certificate. -/
theorem linfty_opNorm_cmp116PhysicalEndomorphismComplexMatrix_le_of_weightedRow
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc)
    {A rate : ℝ}
    (hrate : 0 < rate)
    (hgeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (hT : PhysicalCovarianceWeightedRowKernelBound
      T physicalBondDist A rate) :
    ‖cmp116PhysicalEndomorphismComplexMatrix T‖ ≤
      A * (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum d rate) := by
  have hExp :=
    physicalCovarianceExponentialKernelBound_of_weightedRow
      T physicalBondDist hrate hT
  apply physicalWalkMatrix_linfty_opNorm_le_of_fixedRate
    (cmp116PhysicalEndomorphismComplexMatrix T)
    A rate hT.1 hgeom
  intro row col
  rw [cmp116PhysicalEndomorphismComplexMatrix_apply]
  calc
    ‖cmp116ComplexPhysicalOperatorCoefficient
        T col.1 row.1 col.2 row.2‖ ≤
        ‖T (singlePhysicalBondCochain col.1
          (EuclideanSpace.single col.2 (1 : ℝ))) row.1‖ :=
      norm_cmp116ComplexPhysicalOperatorCoefficient_le_targetValue
        T col.1 row.1 col.2 row.2
    _ ≤ A * Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ))) *
        ‖EuclideanSpace.single col.2 (1 : ℝ)‖ :=
      hExp.2.2 col.1 row.1
        (EuclideanSpace.single col.2 (1 : ℝ))
    _ = A * Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ))) := by
      rw [EuclideanSpace.norm_single]
      simp

/-- The same physical weighted-row certificate also controls the column
norm of the canonical matrix.  This uses the certificate with source and
target interchanged and symmetry of `physicalBondDist`; it does not assume
that the operator itself is symmetric. -/
theorem linfty_opNorm_transpose_cmp116PhysicalEndomorphismComplexMatrix_le_of_weightedRow
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc)
    {A rate : ℝ}
    (hrate : 0 < rate)
    (hgeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (hT : PhysicalCovarianceWeightedRowKernelBound
      T physicalBondDist A rate) :
    ‖(cmp116PhysicalEndomorphismComplexMatrix T).transpose‖ ≤
      A * (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum d rate) := by
  have hExp :=
    physicalCovarianceExponentialKernelBound_of_weightedRow
      T physicalBondDist hrate hT
  apply physicalWalkMatrix_linfty_opNorm_le_of_fixedRate
    (cmp116PhysicalEndomorphismComplexMatrix T).transpose
    A rate hT.1 hgeom
  intro row col
  rw [Matrix.transpose_apply,
    cmp116PhysicalEndomorphismComplexMatrix_apply]
  calc
    ‖cmp116ComplexPhysicalOperatorCoefficient
        T row.1 col.1 row.2 col.2‖ ≤
        ‖T (singlePhysicalBondCochain row.1
          (EuclideanSpace.single row.2 (1 : ℝ))) col.1‖ :=
      norm_cmp116ComplexPhysicalOperatorCoefficient_le_targetValue
        T row.1 col.1 row.2 col.2
    _ ≤ A * Real.exp (-(rate *
          (physicalBondDist col.1 row.1 : ℝ))) *
        ‖EuclideanSpace.single row.2 (1 : ℝ)‖ :=
      hExp.2.2 row.1 col.1
        (EuclideanSpace.single row.2 (1 : ℝ))
    _ = A * Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ))) := by
      rw [EuclideanSpace.norm_single, physicalBondDist_comm]
      simp

end

end YangMills.RG
