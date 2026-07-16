import YangMills.RG.BalabanCMP116Eq223PhysicalRootNormBridge
import YangMills.RG.CoerciveCovariance
import YangMills.RG.InverseSqrtResolventCFC
import Mathlib.Analysis.Matrix.Order

/-!
# Canonical inverse square roots for real coercive CMP116 precisions

This module constructs the positive inverse square root of a real symmetric
coercive physical precision.  The construction is finite dimensional:

1. transport the physical precision through the exact CMP116 isometry;
2. form its positive-definite real matrix;
3. take the spectral positive square root of the inverse matrix;
4. transport that square root back to the physical one-cochain space.

The terminal theorem proves literally that the transported operator squares to
`covarianceOfIsCoerciveCLM K hc hcoer`.

This is intentionally a real self-adjoint result.  It does not assert a positive
square root for the complex contour-dependent precisions used later in CMP116.
-/

set_option synthInstance.maxHeartbeats 100000

namespace YangMills.RG

open scoped RealInnerProductSpace Matrix.Norms.L2Operator ComplexOrder

namespace PhysicalGaugeCMP116Dictionary

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- Isometric conjugation preserves symmetry of a real physical precision. -/
theorem flatPhysicalPrecision_isSymmetric
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    (D.flatPhysicalRootCLM K :
      EuclideanSpace ℝ (CMP116CoordIndex d L lieDim) →ₗ[ℝ]
        EuclideanSpace ℝ (CMP116CoordIndex d L lieDim)).IsSymmetric := by
  intro x y
  calc
    inner ℝ (D.flatPhysicalRootCLM K x) y =
        inner ℝ
          (D.flatPhysicalLinearIsometryEquiv
            (D.flatPhysicalRootCLM K x))
          (D.flatPhysicalLinearIsometryEquiv y) :=
      (D.flatPhysicalLinearIsometryEquiv.inner_map_map _ _).symm
    _ = inner ℝ
          (K (D.flatPhysicalLinearIsometryEquiv x))
          (D.flatPhysicalLinearIsometryEquiv y) := by
      simp [flatPhysicalRootCLM]
    _ = inner ℝ
          (D.flatPhysicalLinearIsometryEquiv x)
          (K (D.flatPhysicalLinearIsometryEquiv y)) :=
      hK _ _
    _ = inner ℝ
          (D.flatPhysicalLinearIsometryEquiv x)
          (D.flatPhysicalLinearIsometryEquiv
            (D.flatPhysicalRootCLM K y)) := by
      simp [flatPhysicalRootCLM]
    _ = inner ℝ x (D.flatPhysicalRootCLM K y) :=
      D.flatPhysicalLinearIsometryEquiv.inner_map_map _ _

/-- The exact CMP116 matrix of a symmetric physical precision is Hermitian. -/
theorem physicalPrecisionMatrix_isHermitian
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    (D.physicalRootMatrix K).IsHermitian := by
  have hflat := flatPhysicalPrecision_isSymmetric D K hK
  change star (D.physicalRootMatrix K) = D.physicalRootMatrix K
  apply Matrix.toEuclideanCLM.injective
  calc
    (Matrix.toEuclideanCLM
      (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
        (star (D.physicalRootMatrix K)) =
        star ((Matrix.toEuclideanCLM
          (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
            (D.physicalRootMatrix K)) :=
      Matrix.toEuclideanCLM.map_star' _
    _ = (Matrix.toEuclideanCLM
          (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
            (D.physicalRootMatrix K) := by
      simp only [physicalRootMatrix, StarAlgEquiv.apply_symm_apply]
      exact hflat.clm_adjoint_eq

/-- Coercivity becomes positive definiteness of the exact CMP116 matrix. -/
theorem physicalPrecisionMatrix_posDef
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    (D.physicalRootMatrix K).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (physicalPrecisionMatrix_isHermitian D K hK)
  intro x hx
  let ex : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim) :=
    WithLp.toLp 2 x
  let y : PhysicalGaugeOneCochain dPhys N Nc :=
    D.flatPhysicalLinearIsometryEquiv ex
  have hex : ex ≠ 0 := by
    intro hzero
    apply hx
    have := congrArg WithLp.ofLp hzero
    simpa [ex] using this
  have hy : y ≠ 0 :=
    D.flatPhysicalLinearIsometryEquiv.injective.ne hex
  have hstrict : 0 < inner ℝ y (K y) := by
    exact (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hy))).trans_le
      (hcoer y)
  have htransport :
      inner ℝ ex (D.flatPhysicalRootCLM K ex) =
        inner ℝ y (K y) := by
    rw [← D.flatPhysicalLinearIsometryEquiv.inner_map_map]
    simp [ex, y, flatPhysicalRootCLM]
  calc
    0 < inner ℝ ex
          ((Matrix.toEuclideanCLM
            (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
              (D.physicalRootMatrix K) ex) := by
      rw [show
        (Matrix.toEuclideanCLM
          (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
            (D.physicalRootMatrix K) =
          D.flatPhysicalRootCLM K by
            exact (Matrix.toEuclideanCLM
              (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ)).apply_symm_apply _]
      rwa [htransport]
    _ = star x ⬝ᵥ (Matrix.mulVec (D.physicalRootMatrix K) x) := by
      simpa [ex] using
        Matrix.inner_toEuclideanCLM (D.physicalRootMatrix K) ex ex

/-- Transport a real CMP116 matrix back to the physical one-cochain space. -/
noncomputable def physicalCLMOfMatrix
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ) :
    PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc :=
  D.flatPhysicalLinearIsometryEquiv.toContinuousLinearMap.comp
    ((Matrix.toEuclideanCLM
      (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ) A).comp
        D.flatPhysicalLinearIsometryEquiv.symm.toContinuousLinearMap)

theorem physicalCLMOfMatrix_physicalRootMatrix
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc) :
    physicalCLMOfMatrix D (D.physicalRootMatrix K) = K := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [physicalCLMOfMatrix, ContinuousLinearMap.comp_apply]
  have haction := D.physicalRootMatrix_action K
    (D.flatPhysicalLinearIsometryEquiv.symm x)
  simpa using haction

theorem physicalCLMOfMatrix_mul
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A B : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ) :
    physicalCLMOfMatrix D (A * B) =
      (physicalCLMOfMatrix D A).comp (physicalCLMOfMatrix D B) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [physicalCLMOfMatrix, ContinuousLinearMap.comp_apply]
  rw [map_mul]
  simp

theorem physicalCLMOfMatrix_one
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim) :
    physicalCLMOfMatrix D 1 =
      ContinuousLinearMap.id ℝ
        (PhysicalGaugeOneCochain dPhys N Nc) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [physicalCLMOfMatrix]

theorem physicalCLMOfMatrix_add
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A B : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ) :
    physicalCLMOfMatrix D (A + B) =
      physicalCLMOfMatrix D A + physicalCLMOfMatrix D B := by
  apply ContinuousLinearMap.ext
  intro x
  simp [physicalCLMOfMatrix]

theorem physicalCLMOfMatrix_sub
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A B : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ) :
    physicalCLMOfMatrix D (A - B) =
      physicalCLMOfMatrix D A - physicalCLMOfMatrix D B := by
  apply ContinuousLinearMap.ext
  intro x
  simp [physicalCLMOfMatrix]

theorem physicalCLMOfMatrix_smul
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (r : ℝ)
    (A : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ) :
    physicalCLMOfMatrix D (r • A) =
      r • physicalCLMOfMatrix D A := by
  apply ContinuousLinearMap.ext
  intro x
  simp [physicalCLMOfMatrix]

/-- The matrix-to-physical-operator transport as a continuous linear map.
Finite dimensionality makes the algebraic transport automatically continuous. -/
noncomputable def physicalCLMOfMatrixCLM
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim) :
    Matrix (CMP116CoordIndex d L lieDim)
        (CMP116CoordIndex d L lieDim) ℝ →L[ℝ]
      (PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc) :=
  LinearMap.toContinuousLinearMap {
    toFun := physicalCLMOfMatrix D
    map_add' := physicalCLMOfMatrix_add D
    map_smul' := physicalCLMOfMatrix_smul D }

@[simp]
theorem physicalCLMOfMatrixCLM_apply
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ) :
    physicalCLMOfMatrixCLM D A = physicalCLMOfMatrix D A := by
  rfl

/-- Spectral positive square root of a real positive-semidefinite matrix. -/
noncomputable def positiveSqrtMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : Matrix ι ι ℝ :=
  hA.isHermitian.eigenvectorUnitary *
    Matrix.diagonal
      (Real.sqrt ∘ hA.isHermitian.eigenvalues) *
    star (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)

theorem positiveSqrtMatrix_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (positiveSqrtMatrix hA).PosSemidef := by
  classical
  unfold positiveSqrtMatrix
  apply (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (Unitary.isUnit_coe
      (U := hA.isHermitian.eigenvectorUnitary))).2
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  exact Real.sqrt_nonneg _

theorem positiveSqrtMatrix_mul_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    positiveSqrtMatrix hA * positiveSqrtMatrix hA = A := by
  classical
  unfold positiveSqrtMatrix
  simp only [mul_assoc]
  rw [← mul_assoc
    (star hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)
    (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)]
  rw [Unitary.coe_star_mul_self, one_mul]
  rw [← mul_assoc
    (Matrix.diagonal
      (Real.sqrt ∘ hA.isHermitian.eigenvalues))
    (Matrix.diagonal
      (Real.sqrt ∘ hA.isHermitian.eigenvalues))]
  rw [Matrix.diagonal_mul_diagonal]
  have hsqrt (i : ι) :
      Real.sqrt (hA.isHermitian.eigenvalues i) *
          Real.sqrt (hA.isHermitian.eigenvalues i) =
        hA.isHermitian.eigenvalues i :=
    Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
  have hfun :
      (fun i : ι => Real.sqrt (hA.isHermitian.eigenvalues i)) *
          (fun i : ι => Real.sqrt (hA.isHermitian.eigenvalues i)) =
        (fun i : ι => hA.isHermitian.eigenvalues i) := by
    funext i
    exact hsqrt i
  change
    (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
        (Matrix.diagonal
          ((fun i : ι => Real.sqrt (hA.isHermitian.eigenvalues i)) *
            (fun i : ι => Real.sqrt (hA.isHermitian.eigenvalues i))) *
          star (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)) =
      A
  rw [hfun]
  simpa only [Unitary.conjStarAlgAut_apply, mul_assoc] using
    hA.isHermitian.spectral_theorem.symm

/-- The positive square root of the inverse physical precision matrix. -/
noncomputable def canonicalInverseSqrtMatrix
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ :=
  spectralInverseSqrtMatrix
    (D.physicalRootMatrix K)
    (physicalPrecisionMatrix_posDef D K hc hcoer hK)

theorem canonicalInverseSqrtMatrix_posSemidef
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    (canonicalInverseSqrtMatrix D K hc hcoer hK).PosSemidef := by
  exact spectralInverseSqrtMatrix_posSemidef _ _

theorem canonicalInverseSqrtMatrix_mul_self
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    canonicalInverseSqrtMatrix D K hc hcoer hK *
        canonicalInverseSqrtMatrix D K hc hcoer hK =
      (D.physicalRootMatrix K)⁻¹ := by
  exact spectralInverseSqrtMatrix_mul_self _ _

theorem physicalCLMOfMatrix_inv_physicalRootMatrix
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    physicalCLMOfMatrix D (D.physicalRootMatrix K)⁻¹ =
      covarianceOfIsCoerciveCLM K hc hcoer := by
  let hpos := physicalPrecisionMatrix_posDef D K hc hcoer hK
  letI := hpos.isUnit.invertible
  apply ContinuousLinearMap.ext
  intro x
  let z := physicalCLMOfMatrix D (D.physicalRootMatrix K)⁻¹ x
  have hright : K z = x := by
    calc
      K z = physicalCLMOfMatrix D (D.physicalRootMatrix K) z := by
        rw [physicalCLMOfMatrix_physicalRootMatrix]
      _ = physicalCLMOfMatrix D
          (D.physicalRootMatrix K * (D.physicalRootMatrix K)⁻¹) x := by
        rw [physicalCLMOfMatrix_mul]
        rfl
      _ = physicalCLMOfMatrix D 1 x := by
        rw [Matrix.mul_inv_of_invertible]
      _ = x := by
        rw [physicalCLMOfMatrix_one]
        rfl
  calc
    physicalCLMOfMatrix D (D.physicalRootMatrix K)⁻¹ x =
        covarianceOfIsCoerciveCLM K hc hcoer
          (K (physicalCLMOfMatrix D (D.physicalRootMatrix K)⁻¹ x)) := by
      rw [covarianceOfIsCoerciveCLM_apply_precision]
    _ = covarianceOfIsCoerciveCLM K hc hcoer x := by
      rw [show K (physicalCLMOfMatrix D
        (D.physicalRootMatrix K)⁻¹ x) = x by exact hright]

/-- Canonical positive inverse square root of a real coercive physical precision. -/
noncomputable def physicalCanonicalInverseSqrt
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc :=
  physicalCLMOfMatrix D
    (canonicalInverseSqrtMatrix D K hc hcoer hK)

/-- The canonical inverse square root squares to the exact coercive covariance. -/
theorem physicalCanonicalInverseSqrt_comp_self
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    (physicalCanonicalInverseSqrt D K hc hcoer hK).comp
        (physicalCanonicalInverseSqrt D K hc hcoer hK) =
      covarianceOfIsCoerciveCLM K hc hcoer := by
  unfold physicalCanonicalInverseSqrt
  rw [← physicalCLMOfMatrix_mul]
  rw [canonicalInverseSqrtMatrix_mul_self D K hc hcoer hK]
  exact physicalCLMOfMatrix_inv_physicalRootMatrix D K hc hcoer hK

/-- The canonical inverse square root is nonnegative in the physical inner product. -/
theorem physicalCanonicalInverseSqrt_inner_nonneg
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric)
    (x : PhysicalGaugeOneCochain dPhys N Nc) :
    0 ≤ inner ℝ x (physicalCanonicalInverseSqrt D K hc hcoer hK x) := by
  let u : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim) :=
    D.flatPhysicalLinearIsometryEquiv.symm x
  let M := canonicalInverseSqrtMatrix D K hc hcoer hK
  have hM : M.PosSemidef :=
    canonicalInverseSqrtMatrix_posSemidef D K hc hcoer hK
  let uv : CMP116CoordIndex d L lieDim → ℝ :=
    EuclideanSpace.equiv _ _ u
  have hquad : 0 ≤ star uv ⬝ᵥ Matrix.mulVec M uv :=
    hM.dotProduct_mulVec_nonneg uv
  calc
    0 ≤ inner ℝ u
        ((Matrix.toEuclideanCLM
          (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ)) M u) := by
      rw [Matrix.inner_toEuclideanCLM]
      simpa [uv, EuclideanSpace.equiv] using hquad
    _ = inner ℝ x (physicalCanonicalInverseSqrt D K hc hcoer hK x) := by
      rw [← D.flatPhysicalLinearIsometryEquiv.inner_map_map]
      simp [u, M, physicalCanonicalInverseSqrt, physicalCLMOfMatrix]

end PhysicalGaugeCMP116Dictionary
end YangMills.RG
