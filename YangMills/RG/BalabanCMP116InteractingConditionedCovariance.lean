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

PRE-VALIDATION: the strict lower-covariance extension at the end of this
module is present in source, its updated `.olean` has not yet been
materialized, and those new declarations have not yet been verified by the
Lean compiler.

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

For the lower wall the module uses the literal source upper bound `Lambda` on
the precision together with coercivity `c`.  The deliberately non-optimal but
strict estimate

`c / Lambda^2 * ‖v‖^2 ≤ ⟪v, C v⟫`

survives compression for vectors supported on the localized carrier.  Thus
the only remaining input to the covariance-lower certificate is the honest
geometric statement that this carrier is nonempty.
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

/-- A physical coercivity estimate transports exactly to the quadratic form
of the canonical real coordinate matrix. -/
theorem cmp116PhysicalEndomorphismRealMatrix_quadratic_lower
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc) {lower : ℝ}
    (hT : IsCoerciveCLM T lower)
    (v : PhysicalCoordinate d N Nc → ℝ) :
    lower * dotProduct v v ≤
      dotProduct v
        ((cmp116PhysicalEndomorphismRealMatrix T).mulVec v) := by
  let E := cmp116PhysicalCoordinateLinearIsometryEquiv
    (d := d) (N := N) (Nc := Nc)
  let x : EuclideanSpace ℝ (PhysicalCoordinate d N Nc) := WithLp.toLp 2 v
  let y : PhysicalGaugeOneCochain d N Nc := E x
  have htransport :
      inner ℝ x
          ((Matrix.toEuclideanCLM
            (n := PhysicalCoordinate d N Nc) (𝕜 := ℝ)
            (cmp116PhysicalEndomorphismRealMatrix T)) x) =
        inner ℝ y (T y) := by
    rw [cmp116PhysicalEndomorphismRealMatrix_toEuclideanCLM_apply]
    rw [← E.inner_map_map]
    simp [x, y, E]
  calc
    lower * dotProduct v v = lower * ‖y‖ ^ 2 := by
      congr 1
      calc
        dotProduct v v = ‖x‖ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          simp [x, dotProduct, pow_two]
        _ = ‖y‖ ^ 2 := by simp [y]
    _ ≤ inner ℝ y (T y) := hT y
    _ = inner ℝ x
          ((Matrix.toEuclideanCLM
            (n := PhysicalCoordinate d N Nc) (𝕜 := ℝ)
            (cmp116PhysicalEndomorphismRealMatrix T)) x) := htransport.symm
    _ = dotProduct v
          ((cmp116PhysicalEndomorphismRealMatrix T).mulVec v) := by
      simpa [x] using
        Matrix.inner_toEuclideanCLM
          (cmp116PhysicalEndomorphismRealMatrix T) x x

/-- The diagonal localization projector fixes every vector already supported
on its carrier. -/
theorem cmp116Eq223CoordinateProjection_mulVec_eq_of_vectorSupportedOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (v : ι → ℝ) (hv : VectorSupportedOn S v) :
    (cmp116Eq223CoordinateProjection S).mulVec v = v := by
  funext i
  rw [cmp116Eq223CoordinateProjection, Matrix.mulVec_diagonal]
  by_cases hi : i ∈ S
  · simp [hi]
  · simp [hi, hv i hi]

/-- Bilateral compression does not change the covariance quadratic form on
vectors already supported on the localized carrier. -/
theorem dotProduct_cmp116LocalizedCovarianceCompression_mulVec_eq_of_vectorSupportedOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (C : Matrix ι ι ℝ) (v : ι → ℝ)
    (hv : VectorSupportedOn S v) :
    dotProduct v ((cmp116LocalizedCovarianceCompression S C).mulVec v) =
      dotProduct v (C.mulVec v) := by
  let P := cmp116Eq223CoordinateProjection S
  have hPv : P.mulVec v = v :=
    cmp116Eq223CoordinateProjection_mulVec_eq_of_vectorSupportedOn S v hv
  rw [cmp116LocalizedCovarianceCompression, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, cmp116Eq223CoordinateProjection_transpose,
    hPv]

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

/-- Literal equation-(3.126) upper bound for the interacting precision. -/
def precisionUpperBound
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U) : ℝ :=
  cmp99SourceEq3126PhysicalPrecisionUpperBound
    4 M Nc X.a X.backgroundEpsilon

theorem precisionUpperBound_pos
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U) :
    0 < X.precisionUpperBound := by
  exact cmp99SourceEq3126PhysicalPrecisionUpperBound_pos
    X.a X.backgroundEpsilon_nonneg

theorem norm_precision_le
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U) :
    ‖X.precision‖ ≤ X.precisionUpperBound := by
  simpa [precision, precisionUpperBound] using
    (norm_interactingPhysicalBasePrecisionCLM_le_sourceEq3126
      U X.a X.backgroundEpsilon_nonneg X.smallBackground)

/-- The exact inverse covariance is strictly coercive.  The source upper
bound on the precision gives the explicit (non-optimal) constant
`c / Lambda^2`, which is sufficient for nondegeneracy. -/
theorem covariance_coercive
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U) :
    IsCoerciveCLM X.covariance
      (X.coercivityConstant / X.precisionUpperBound ^ 2) := by
  intro y
  let x := X.covariance y
  have hKx : X.precision x = y := by
    have h := congrArg
      (fun T : PhysicalEndomorphism 4 (M * (2 * Q)) Nc => T y)
      X.precision_comp_covariance
    simpa [ContinuousLinearMap.comp_apply, x] using h
  have hinverse : ‖y‖ ≤ X.precisionUpperBound * ‖x‖ := by
    calc
      ‖y‖ = ‖X.precision x‖ := by rw [hKx]
      _ ≤ ‖X.precision‖ * ‖x‖ := X.precision.le_opNorm x
      _ ≤ X.precisionUpperBound * ‖x‖ :=
        mul_le_mul_of_nonneg_right X.norm_precision_le (norm_nonneg x)
  have hsquare :
      ‖y‖ ^ 2 ≤ X.precisionUpperBound ^ 2 * ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg y, norm_nonneg x,
      X.precisionUpperBound_pos.le]
  have hLambdaSq : 0 < X.precisionUpperBound ^ 2 :=
    sq_pos_of_pos X.precisionUpperBound_pos
  have hscaled :
      ‖y‖ ^ 2 / X.precisionUpperBound ^ 2 ≤ ‖x‖ ^ 2 :=
    (div_le_iff₀ hLambdaSq).2 (by simpa [mul_comm] using hsquare)
  calc
    (X.coercivityConstant / X.precisionUpperBound ^ 2) * ‖y‖ ^ 2 =
        X.coercivityConstant *
          (‖y‖ ^ 2 / X.precisionUpperBound ^ 2) := by ring
    _ ≤ X.coercivityConstant * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hscaled X.coercivity_pos.le
    _ ≤ inner ℝ x (X.precision x) := X.coercive x
    _ = inner ℝ y (X.covariance y) := by
      rw [hKx]
      exact real_inner_comm _ _

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

/-- Coordinate quadratic lower bound inherited from the literal interacting
inverse covariance. -/
theorem covarianceMatrix_quadratic_lower
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U)
    (v : PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc → ℝ) :
    (X.coercivityConstant / X.precisionUpperBound ^ 2) * dotProduct v v ≤
      dotProduct v (X.covarianceMatrix.mulVec v) := by
  exact cmp116PhysicalEndomorphismRealMatrix_quadratic_lower
    X.covariance X.covariance_coercive v

/-- Strict nondegeneracy of the localized interacting covariance.  Carrier
nonemptiness remains an explicit geometric input rather than being fabricated
by the analytic covariance construction. -/
def conditionedCovariance_lowerCertificate
    (X : CMP116InteractingPhysicalPrecisionSource (M := M) (Q := Q) U)
    (S : Finset (PhysicalGaugeCoordIndex 4 (M * (2 * Q)) Nc))
    (hS : S.Nonempty) :
    MatrixConditionedGaussianCovarianceLowerCertificate
      (X.conditionedCovariance S) S where
  lowerBound := X.coercivityConstant / X.precisionUpperBound ^ 2
  lowerBound_pos := div_pos X.coercivity_pos
    (sq_pos_of_pos X.precisionUpperBound_pos)
  carrier_nonempty := hS
  covariance_lower := by
    intro v hv
    change
      (X.coercivityConstant / X.precisionUpperBound ^ 2) * dotProduct v v ≤
        dotProduct v
          ((cmp116LocalizedCovarianceCompression S X.covarianceMatrix).mulVec v)
    rw [dotProduct_cmp116LocalizedCovarianceCompression_mulVec_eq_of_vectorSupportedOn
      S X.covarianceMatrix v hv]
    exact X.covarianceMatrix_quadratic_lower v

end CMP116InteractingPhysicalPrecisionSource

end

end YangMills.RG
