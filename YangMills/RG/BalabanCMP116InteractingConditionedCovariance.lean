/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ConditionedRootScalarWall
import YangMills.RG.BalabanCMP116InteractingPhysicalPrecisionSource
import YangMills.RG.BalabanCMP116LocalizedCovarianceCompression
import YangMills.RG.BalabanCMP116PhysicalEndomorphismSchurNorm
import YangMills.RG.BalabanCMP99SourceEq3126PhysicalH

/-!
# The physical interacting conditioned covariance

The conditioned covariance in the terminal CMP116 Gaussian is not an
independent matrix.  Starting from the literal interacting precision `K`, this
module takes its coercively generated inverse `C = K⁻¹`, transports `C` through
the canonical physical `L²` coordinate isometry, and compresses it to the
localized scalar coordinates:

`C_S = P_S [C] P_S`.

The generic finite-matrix construction then supplies the positive spectral
root of `C_S`.  Reconstructing that matrix as a physical endomorphism makes
the exact terminal root certificate available in the representation consumed
by the centered-conditioned source.

The upper wall is derived here rather than assumed:

`‖C_S‖ ≤ ‖[C]‖ ≤ ‖C‖ ≤ coercivityConstant⁻¹`.

Honest scope: this module does not construct the strict lower covariance
certificate on the localized carrier.  That requires an upper bound on the
precision restricted to the carrier (and carrier nonemptiness), not merely
the lower/coercive estimate used here.  It therefore remains a separate
source-facing obligation before the scalar walls can be installed.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

private abbrev PhysicalCoordinate (d N Nc : ℕ) [NeZero N] :=
  CMP116PhysicalWalkCoordinate d N Nc

/-- Applying the canonical real coordinate matrix is exactly conjugation of
the physical endomorphism by the canonical physical `L²` isometry. -/
theorem cmp116PhysicalEndomorphismRealMatrix_toEuclideanCLM_apply
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc)
    (x : EuclideanSpace ℝ (PhysicalCoordinate d N Nc)) :
    (Matrix.toEuclideanCLM
        (n := PhysicalCoordinate d N Nc) (𝕜 := ℝ)
        (cmp116PhysicalEndomorphismRealMatrix T)) x =
      cmp116PhysicalCoordinateLinearIsometryEquiv.symm
        (T (cmp116PhysicalCoordinateLinearIsometryEquiv x)) := by
  let E := cmp116PhysicalCoordinateLinearIsometryEquiv
    (d := d) (N := N) (Nc := Nc)
  have hreal :
      cmp116Eq214RealPartMatrix
          (cmp116PhysicalEndomorphismComplexMatrix T) =
        cmp116PhysicalEndomorphismRealMatrix T := by
    ext i j
    simp [cmp116Eq214RealPartMatrix,
      cmp116PhysicalEndomorphismComplexMatrix]
  have haction :=
    cmp116PhysicalCoordinateLinearIsometryEquiv_symm_reconstruction
      (cmp116PhysicalEndomorphismComplexMatrix T) (E x)
  rw [cmp116PhysicalEndomorphismOfComplexMatrixCLM_canonical,
    E.symm_apply_apply, hreal] at haction
  exact haction.symm

/-- The canonical coordinate matrix cannot have larger `L²` operator norm
than the physical endomorphism it represents. -/
theorem norm_cmp116PhysicalEndomorphismRealMatrix_le
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc) :
    ‖cmp116PhysicalEndomorphismRealMatrix T‖ ≤ ‖T‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  rw [cmp116PhysicalEndomorphismRealMatrix_toEuclideanCLM_apply]
  calc
    ‖cmp116PhysicalCoordinateLinearIsometryEquiv.symm
        (T (cmp116PhysicalCoordinateLinearIsometryEquiv x))‖ =
        ‖T (cmp116PhysicalCoordinateLinearIsometryEquiv x)‖ := by
          rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖T‖ * ‖cmp116PhysicalCoordinateLinearIsometryEquiv x‖ :=
      T.le_opNorm _
    _ = ‖T‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]

/-- A positive physical endomorphism has a positive-semidefinite canonical
real coordinate matrix. -/
theorem cmp116PhysicalEndomorphismRealMatrix_posSemidef
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc)
    (hT : T.toLinearMap.IsPositive) :
    (cmp116PhysicalEndomorphismRealMatrix T).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  let E := cmp116PhysicalCoordinateLinearIsometryEquiv
    (d := d) (N := N) (Nc := Nc)
  have hconj :
      Matrix.toEuclideanLin
          (cmp116PhysicalEndomorphismRealMatrix T) =
        E.symm.toLinearMap.comp
          (T.toLinearMap.comp E.toLinearMap) := by
    apply LinearMap.ext
    intro x
    exact
      cmp116PhysicalEndomorphismRealMatrix_toEuclideanCLM_apply T x
  rw [hconj]
  exact (LinearMap.isPositive_linearIsometryEquiv_conj_iff E.symm).2 hT

/-- Reconstruction of a real coordinate matrix is a right inverse to the
canonical real coordinate matrix. -/
@[simp]
theorem cmp116PhysicalEndomorphismRealMatrix_reconstruction
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (A : Matrix (PhysicalCoordinate d N Nc)
      (PhysicalCoordinate d N Nc) ℝ) :
    cmp116PhysicalEndomorphismRealMatrix
        (cmp116PhysicalEndomorphismOfRealMatrix A) = A := by
  ext i j
  rw [cmp116PhysicalEndomorphismRealMatrix,
    LinearMap.toMatrix'_apply]
  simp [cmp116PhysicalEndomorphismFlatLinearMap,
    cmp116PhysicalEndomorphismOfRealMatrix, LinearMap.comp_apply]

namespace CMP116InteractingPhysicalPrecisionSource

variable {M Q Nc : ℕ}
  [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
  [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
  {U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc}

/-- The literal interacting covariance is symmetric because it is the exact
inverse of the symmetric Wilson-plus-gauge precision. -/
theorem covariance_isSymmetric
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U) :
    X.covariance.IsSymmetric := by
  unfold covariance interactingPhysicalCovarianceCLM
  exact covarianceOfIsCoerciveCLM_isSymmetric _
    (sub_pos.mpr X.defectBudget)
    (isCoerciveCLM_interactingPhysicalBasePrecision
      U X.a_pos X.poincare X.backgroundEpsilon_nonneg X.smallBackground)
    (interactingPhysicalBasePrecisionCLM_isSymmetric U X.a)

/-- The literal interacting covariance has nonnegative quadratic form. -/
theorem covariance_psd
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U)
    (y : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc) :
    0 ≤ inner ℝ y (X.covariance y) := by
  unfold covariance interactingPhysicalCovarianceCLM
  exact covarianceOfIsCoerciveCLM_psd _
    (sub_pos.mpr X.defectBudget)
    (isCoerciveCLM_interactingPhysicalBasePrecision
      U X.a_pos X.poincare X.backgroundEpsilon_nonneg X.smallBackground) y

/-- The literal inverse covariance has the exact coercivity-generated norm
bound, before any coordinate transport or localization. -/
theorem norm_covariance_le
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U) :
    ‖X.covariance‖ ≤ X.coercivityConstant⁻¹ := by
  unfold covariance interactingPhysicalCovarianceCLM coercivityConstant
  exact norm_covarianceOfIsCoerciveCLM_le _
    (sub_pos.mpr X.defectBudget)
    (isCoerciveCLM_interactingPhysicalBasePrecision
      U X.a_pos X.poincare X.backgroundEpsilon_nonneg X.smallBackground)

/-- Canonical real matrix of the literal interacting inverse covariance. -/
def covarianceMatrix
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U) :
    Matrix (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
      (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) ℝ :=
  cmp116PhysicalEndomorphismRealMatrix X.covariance

/-- The coordinate covariance matrix is positive semidefinite. -/
theorem covarianceMatrix_posSemidef
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U) :
    X.covarianceMatrix.PosSemidef := by
  apply cmp116PhysicalEndomorphismRealMatrix_posSemidef
  exact ⟨X.covariance_isSymmetric, fun y => by
    rw [real_inner_comm]
    exact X.covariance_psd y⟩

/-- Localized compression of the literal interacting covariance. -/
def conditionedCovariance
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U)
    (S : Finset (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)) :
    Matrix (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
      (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) ℝ :=
  cmp116LocalizedCovarianceCompression S X.covarianceMatrix

/-- Positive spectral root of the localized interacting covariance. -/
def conditionedRootMatrix
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U)
    (S : Finset (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)) :
    Matrix (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)
      (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc) ℝ :=
  cmp116LocalizedCovarianceRoot S X.covarianceMatrix
    X.covarianceMatrix_posSemidef

/-- Physical endomorphism reconstructed from the positive localized matrix
root. -/
def conditionedRoot
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U)
    (S : Finset (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)) :
    PhysicalEndomorphism 4 (M * (2 * Q)) Nc :=
  cmp116PhysicalEndomorphismOfRealMatrix (X.conditionedRootMatrix S)

/-- The reconstructed physical root has exactly the canonical coordinate
matrix used by the conditioned Gaussian. -/
theorem conditionedRoot_realMatrix
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U)
    (S : Finset (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)) :
    cmp116PhysicalEndomorphismRealMatrix (X.conditionedRoot S) =
      X.conditionedRootMatrix S := by
  simp [conditionedRoot]

/-- Exact terminal root certificate for the physically generated localized
covariance and its reconstructed root. -/
theorem conditionedRoot_certificate
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U)
    (S : Finset (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)) :
    MatrixConditionedGaussianRootCertificate
      (X.conditionedCovariance S)
      (cmp116PhysicalEndomorphismRealMatrix (X.conditionedRoot S)) S := by
  rw [X.conditionedRoot_realMatrix S]
  exact cmp116LocalizedCovarianceRoot_certificate S
    X.covarianceMatrix_posSemidef

/-- The conditioned covariance inherits the inverse-coercivity upper bound.
This is the physical input required by the separate scalar-wall reduction. -/
theorem norm_conditionedCovariance_le
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U)
    (S : Finset (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc)) :
    ‖X.conditionedCovariance S‖ ≤ X.coercivityConstant⁻¹ := by
  calc
    ‖X.conditionedCovariance S‖ ≤ ‖X.covarianceMatrix‖ :=
      norm_cmp116LocalizedCovarianceCompression_le S X.covarianceMatrix
    _ ≤ ‖X.covariance‖ :=
      norm_cmp116PhysicalEndomorphismRealMatrix_le X.covariance
    _ ≤ X.coercivityConstant⁻¹ := X.norm_covariance_le

end CMP116InteractingPhysicalPrecisionSource

end

end YangMills.RG
