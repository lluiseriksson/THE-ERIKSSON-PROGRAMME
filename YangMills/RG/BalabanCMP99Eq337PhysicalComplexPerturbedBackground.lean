import YangMills.RG.BalabanCMP98Eq124Eq125Bridge
import YangMills.RG.BalabanCMP98PhysicalSpecialUnitaryChart
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexCovariantDerivative
import YangMills.RG.MatrixDetExponential

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# CMP99 (3.37): literal complex perturbation of the physical background

CMP99 writes the perturbation as `exp(i eta A') U`, using Hermitian printed
coordinates.  The repository's real `SUNLieCoord` chart is represented by
skew-Hermitian matrices.  This module keeps the conversion visible: it first
complexifies the skew-matrix realization, then multiplies by `1/i` to obtain
the printed coordinate.  Multiplication back by `i` is theorem-proved before
the exponential is formed.

The traceless exponential is packaged in `SL(N,C)` and a full oriented gauge
configuration is reconstructed from its positive bonds.  No localized
average, tower, Green operator or analytic estimate is accepted or claimed.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

/-- Canonical complex-linear matrix realization of the repository's
skew-Hermitian real chart.  Away from the real slice its values need not be
skew-Hermitian. -/
noncomputable def cmp99SUNLieComplexCoordMatrixLM (Nc : ℕ) :
    SUNLieComplexCoord Nc →ₗ[ℂ] Matrix (Fin Nc) (Fin Nc) ℂ where
  toFun Z :=
    cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart Z) +
      Complex.I •
        cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart Z)
  map_add' Z W := by
    rw [cmp99SUNLieComplexCoordRealPart_add,
      cmp99SUNLieComplexCoordImagPart_add,
      cmp98LieCoordMatrix_add, cmp98LieCoordMatrix_add]
    module
  map_smul' c Z := by
    rw [cmp99SUNLieComplexCoordRealPart_smul,
      cmp99SUNLieComplexCoordImagPart_smul]
    simp only [cmp98LieCoordMatrix, map_sub, map_add, map_smul]
    ext i j
    simp [Complex.mul_re, Complex.mul_im]
    ring

@[simp] theorem cmp99SUNLieComplexCoordMatrixLM_complexification
    (X : SUNLieCoord Nc) :
    cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SUNLieCoordComplexificationLM Nc X) =
      cmp98LieCoordMatrix X := by
  simp [cmp99SUNLieComplexCoordMatrixLM]

/-- The complex-linear matrix realization lands in the traceless complex
Lie algebra.  This is the literal `sl(N,C)` carrier property; skew-adjointness
is asserted only on the real slice, not after complexification. -/
theorem cmp99SUNLieComplexCoordMatrixLM_trace
    (Z : SUNLieComplexCoord Nc) :
    Matrix.trace (cmp99SUNLieComplexCoordMatrixLM Nc Z) = 0 := by
  unfold cmp99SUNLieComplexCoordMatrixLM
  rw [Matrix.trace_add, Matrix.trace_smul]
  have hre : Matrix.trace
      (cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart Z)) = 0 :=
    ((suLieCoordIso Nc).symm
      (cmp99SUNLieComplexCoordRealPart Z)).property.2
  have him : Matrix.trace
      (cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart Z)) = 0 :=
    ((suLieCoordIso Nc).symm
      (cmp99SUNLieComplexCoordImagPart Z)).property.2
  rw [hre, him]
  simp

/-! ## The literal `sl(N,C)` coordinate equivalence

This is deliberately proved by explicit real/skew and imaginary/skew
decomposition.  No dimension count or arbitrary inverse is used.
-/

/-- The complex matrix realization, with its already proved trace equation,
as a linear map into Mathlib's literal special-linear Lie algebra. -/
noncomputable def cmp99SUNLieComplexCoordToSlLM (Nc : ℕ) :
    SUNLieComplexCoord Nc →ₗ[ℂ]
      LieAlgebra.SpecialLinear.sl (Fin Nc) ℂ :=
  (cmp99SUNLieComplexCoordMatrixLM Nc).codRestrict
    (LieAlgebra.SpecialLinear.sl (Fin Nc) ℂ) fun Z => by
      change Matrix.trace (cmp99SUNLieComplexCoordMatrixLM Nc Z) = 0
      exact cmp99SUNLieComplexCoordMatrixLM_trace Z

@[simp] theorem cmp99SUNLieComplexCoordToSlLM_val
    (Z : SUNLieComplexCoord Nc) :
    (cmp99SUNLieComplexCoordToSlLM Nc Z).1 =
      cmp99SUNLieComplexCoordMatrixLM Nc Z :=
  rfl

/-- Assemble a complex coordinate from two real physical Lie coordinates. -/
def cmp99SUNLieComplexCoordOfRealImag
    (X Y : SUNLieCoord Nc) : SUNLieComplexCoord Nc :=
  cmp99SUNLieCoordComplexificationLM Nc X +
    Complex.I • cmp99SUNLieCoordComplexificationLM Nc Y

@[simp] theorem cmp99SUNLieComplexCoordRealPart_ofRealImag
    (X Y : SUNLieCoord Nc) :
    cmp99SUNLieComplexCoordRealPart
        (cmp99SUNLieComplexCoordOfRealImag X Y) = X := by
  rw [cmp99SUNLieComplexCoordOfRealImag,
    cmp99SUNLieComplexCoordRealPart_add,
    cmp99SUNLieComplexCoordRealPart_smul]
  simp

@[simp] theorem cmp99SUNLieComplexCoordImagPart_ofRealImag
    (X Y : SUNLieCoord Nc) :
    cmp99SUNLieComplexCoordImagPart
        (cmp99SUNLieComplexCoordOfRealImag X Y) = Y := by
  rw [cmp99SUNLieComplexCoordOfRealImag,
    cmp99SUNLieComplexCoordImagPart_add,
    cmp99SUNLieComplexCoordImagPart_smul]
  simp

@[simp] theorem cmp99SUNLieComplexCoordMatrixLM_ofRealImag
    (X Y : SUNLieCoord Nc) :
    cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SUNLieComplexCoordOfRealImag X Y) =
      cmp98LieCoordMatrix X + Complex.I • cmp98LieCoordMatrix Y := by
  simp [cmp99SUNLieComplexCoordMatrixLM]

/-- Conjugate transpose of the complex matrix chart.  Both real-coordinate
pieces are skew-Hermitian, so the `i B` term is fixed while `A` changes sign.
This is the separation used in the injectivity proof. -/
theorem cmp99SUNLieComplexCoordMatrixLM_conjTranspose
    (Z : SUNLieComplexCoord Nc) :
    (cmp99SUNLieComplexCoordMatrixLM Nc Z)ᴴ =
      -cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart Z) +
        Complex.I •
          cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart Z) := by
  unfold cmp99SUNLieComplexCoordMatrixLM
  rw [conjTranspose_add, conjTranspose_smul]
  have hre :
      (cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart Z))ᴴ =
        -cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart Z) :=
    ((suLieCoordIso Nc).symm
      (cmp99SUNLieComplexCoordRealPart Z)).property.1
  have him :
      (cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart Z))ᴴ =
        -cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart Z) :=
    ((suLieCoordIso Nc).symm
      (cmp99SUNLieComplexCoordImagPart Z)).property.1
  rw [hre, him]
  simp

/-- The complex coordinate-to-matrix map is injective.  Equality of matrices
and equality of their conjugate transposes separate the real and imaginary
skew-Hermitian components; the sealed real chart then recovers coordinates. -/
theorem cmp99SUNLieComplexCoordMatrixLM_injective :
    Function.Injective (cmp99SUNLieComplexCoordMatrixLM Nc) := by
  intro Z W h
  have hdag := congrArg Matrix.conjTranspose h
  rw [cmp99SUNLieComplexCoordMatrixLM_conjTranspose,
    cmp99SUNLieComplexCoordMatrixLM_conjTranspose] at hdag
  change
    cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart Z) +
        Complex.I • cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart Z) =
      cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart W) +
        Complex.I • cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart W)
      at h
  have hreMatrix :
      cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart Z) =
        cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart W) := by
    ext i j
    have h1 := congrArg (fun M => M i j) h
    have h2 := congrArg (fun M => M i j) hdag
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply] at h1 h2
    linear_combination (h1 - h2) / 2
  have himMatrix :
      cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart Z) =
        cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart W) := by
    ext i j
    have h1 := congrArg (fun M => M i j) h
    have h2 := congrArg (fun M => M i j) hdag
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply] at h1 h2
    linear_combination (h1 + h2) / (2 * Complex.I)
  have hre : cmp99SUNLieComplexCoordRealPart Z =
      cmp99SUNLieComplexCoordRealPart W := by
    calc
      cmp99SUNLieComplexCoordRealPart Z =
          cmp98AmbientToLieCoordCLM Nc
            (cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart Z)) :=
        (cmp98AmbientToLieCoordCLM_leftInverse _).symm
      _ = cmp98AmbientToLieCoordCLM Nc
            (cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart W)) := by
        rw [hreMatrix]
      _ = cmp99SUNLieComplexCoordRealPart W :=
        cmp98AmbientToLieCoordCLM_leftInverse _
  have him : cmp99SUNLieComplexCoordImagPart Z =
      cmp99SUNLieComplexCoordImagPart W := by
    calc
      cmp99SUNLieComplexCoordImagPart Z =
          cmp98AmbientToLieCoordCLM Nc
            (cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart Z)) :=
        (cmp98AmbientToLieCoordCLM_leftInverse _).symm
      _ = cmp98AmbientToLieCoordCLM Nc
            (cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart W)) := by
        rw [himMatrix]
      _ = cmp99SUNLieComplexCoordImagPart W :=
        cmp98AmbientToLieCoordCLM_leftInverse _
  ext a
  apply Complex.ext
  · exact congrArg (fun X : SUNLieCoord Nc => X a) hre
  · exact congrArg (fun X : SUNLieCoord Nc => X a) him

/-- Real skew-Hermitian component `(Z-Z†)/2` of a traceless complex matrix. -/
noncomputable def cmp99SlSkewReal
    (Z : LieAlgebra.SpecialLinear.sl (Fin Nc) ℂ) : SuLie Nc :=
  (⟨(2 : ℂ)⁻¹ • (Z.1 - Z.1ᴴ), by
    rw [mem_suMatrixSubmodule_iff]
    constructor
    · rw [conjTranspose_smul, conjTranspose_sub,
        conjTranspose_conjTranspose]
      ext i j
      simp [Matrix.smul_apply]
      ring
    · change Matrix.trace ((2 : ℂ)⁻¹ • (Z.1 - Z.1ᴴ)) = 0
      have hz : Matrix.trace Z.1 = 0 := by
        exact LinearMap.mem_ker.mp Z.property
      rw [Matrix.trace_smul, Matrix.trace_sub,
        Matrix.trace_conjTranspose, hz]
      simp⟩ : ↥(suMatrixSubmodule Nc))

/-- Imaginary skew-Hermitian component `(Z+Z†)/(2i)` of a traceless complex
matrix.  It satisfies `Z = A + i B` with `A = cmp99SlSkewReal Z`. -/
noncomputable def cmp99SlSkewImag
    (Z : LieAlgebra.SpecialLinear.sl (Fin Nc) ℂ) : SuLie Nc :=
  (⟨((2 : ℂ) * Complex.I)⁻¹ • (Z.1 + Z.1ᴴ), by
    rw [mem_suMatrixSubmodule_iff]
    constructor
    · rw [conjTranspose_smul, conjTranspose_add,
        conjTranspose_conjTranspose]
      ext i j
      simp [Matrix.smul_apply]
      ring
    · change Matrix.trace
        (((2 : ℂ) * Complex.I)⁻¹ • (Z.1 + Z.1ᴴ)) = 0
      have hz : Matrix.trace Z.1 = 0 := by
        exact LinearMap.mem_ker.mp Z.property
      rw [Matrix.trace_smul, Matrix.trace_add,
        Matrix.trace_conjTranspose, hz]
      simp⟩ : ↥(suMatrixSubmodule Nc))

/-- Explicit coordinate witness attached to a traceless complex matrix. -/
noncomputable def cmp99SlToSUNLieComplexCoord
    (Z : LieAlgebra.SpecialLinear.sl (Fin Nc) ℂ) :
    SUNLieComplexCoord Nc :=
  cmp99SUNLieComplexCoordOfRealImag
    (suLieCoordIso Nc (cmp99SlSkewReal Z))
    (suLieCoordIso Nc (cmp99SlSkewImag Z))

/-- The explicit skew decomposition is a right inverse of the matrix chart. -/
theorem cmp99SUNLieComplexCoordToSlLM_surjective :
    Function.Surjective (cmp99SUNLieComplexCoordToSlLM Nc) := by
  intro Z
  refine ⟨cmp99SlToSUNLieComplexCoord Z, ?_⟩
  apply Subtype.ext
  rw [cmp99SUNLieComplexCoordToSlLM_val,
    cmp99SlToSUNLieComplexCoord,
    cmp99SUNLieComplexCoordMatrixLM_ofRealImag]
  simp only [cmp98LieCoordMatrix,
    (suLieCoordIso Nc).symm_apply_apply]
  change
    (cmp99SlSkewReal Z).toMatrix +
        Complex.I • (cmp99SlSkewImag Z).toMatrix = Z.1
  unfold cmp99SlSkewReal cmp99SlSkewImag SuLie.toMatrix
  ext i j
  simp [Matrix.smul_apply]
  ring

/-- Literal complex-linear equivalence between the physical complexified Lie
coordinate fibre and Mathlib's traceless complex matrices.  Its bijectivity
is the explicit skew decomposition above, not a dimension argument. -/
noncomputable def cmp99SUNLieComplexCoordSlEquiv (Nc : ℕ) :
    SUNLieComplexCoord Nc ≃₁[ℂ]
      LieAlgebra.SpecialLinear.sl (Fin Nc) ℂ :=
  LinearEquiv.ofBijective (cmp99SUNLieComplexCoordToSlLM Nc)
    ⟨fun _ _ h => cmp99SUNLieComplexCoordMatrixLM_injective
      (congrArg
        (fun Z : LieAlgebra.SpecialLinear.sl (Fin Nc) ℂ => Z.1) h),
      cmp99SUNLieComplexCoordToSlLM_surjective⟩

/-- Hermitian-coordinate convention printed in CMP98/CMP99: repository
skew coordinates are divided by `i`.  This remains a complex matrix away
from the real slice; no Hermiticity claim is made there. -/
def cmp99Eq337PrintedComplexLieMatrix (Z : SUNLieComplexCoord Nc) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  (Complex.I : ℂ)⁻¹ • cmp99SUNLieComplexCoordMatrixLM Nc Z

/-- The visible `i` in `exp(i eta A')` cancels the printed `1/i`
normalization, without changing chart convention silently. -/
theorem Complex.I_smul_cmp99Eq337PrintedComplexLieMatrix
    (Z : SUNLieComplexCoord Nc) :
    (Complex.I : ℂ) • cmp99Eq337PrintedComplexLieMatrix Z =
      cmp99SUNLieComplexCoordMatrixLM Nc Z := by
  rw [cmp99Eq337PrintedComplexLieMatrix, smul_smul]
  simp

/-- The printed complex coordinate restricts to the already sealed CMP98
Hermitian coordinate on the real slice. -/
@[simp] theorem cmp99Eq337PrintedComplexLieMatrix_complexification
    (X : SUNLieCoord Nc) :
    cmp99Eq337PrintedComplexLieMatrix
        (cmp99SUNLieCoordComplexificationLM Nc X) =
      cmp98Eq121PrintedLieCoordMatrix X := by
  simp [cmp99Eq337PrintedComplexLieMatrix,
    cmp98Eq121PrintedLieCoordMatrix]

/-- Positive-bond ambient matrix in the literal printed convention
`exp(i eta A'_b) U_b`. -/
def cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (b : PhysicalBond d N) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  physicalMatrixExp
      (((Complex.I : ℂ) * (eta : ℂ)) •
        cmp99Eq337PrintedComplexLieMatrix (A b)) *
    (U (positiveEdgeOfPhysicalBond b)).val

/-- The exponential generator is exactly `eta` times the canonical complex
skew-coordinate matrix. -/
theorem cmp99Eq337PrintedComplexGenerator_eq
    (eta : ℝ) (Z : SUNLieComplexCoord Nc) :
    (((Complex.I : ℂ) * (eta : ℂ)) •
        cmp99Eq337PrintedComplexLieMatrix Z) =
      (eta : ℂ) • cmp99SUNLieComplexCoordMatrixLM Nc Z := by
  rw [cmp99Eq337PrintedComplexLieMatrix, smul_smul]
  simp
  ring

/-- On the real slice, the printed complex perturbation is exactly the
matrix underlying the repository's physical `SU(N)` left variation. -/
theorem cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix_realSlice
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (eta : ℝ) (b : PhysicalBond d N) :
    cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix U
        (cmp99Eq337PhysicalComplexifyOneCochain A) eta b =
      (cmp98PhysicalSuLeftVariation U A eta
          (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) := by
  rw [cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix,
    cmp99Eq337PrintedComplexGenerator_eq,
    cmp99SUNLieComplexCoordMatrixLM_complexification]
  change physicalMatrixExp
        ((eta : ℂ) • ((suLieCoordIso Nc).symm (A b)).toMatrix) *
      (U (positiveEdgeOfPhysicalBond b)).val =
    ((physicalLeftVariation U
        (fun q t _ => cmp98PhysicalSuIncrement A q t) eta 0
          (positiveEdgeOfPhysicalBond b) : SUN Nc) :
      Matrix (Fin Nc) (Fin Nc) ℂ)
  rw [physicalLeftVariation_apply_pos]
  rfl

/-- The printed complex perturbation remains determinant one.  Unlike the
real slice, unitarity is neither true nor used. -/
theorem cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix_det
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (b : PhysicalBond d N) :
    Matrix.det
        (cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix U A eta b) =
      1 := by
  rw [cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix, Matrix.det_mul]
  have htrace : Matrix.trace
      (((Complex.I : ℂ) * (eta : ℂ)) •
        cmp99Eq337PrintedComplexLieMatrix (A b)) = 0 := by
    rw [cmp99Eq337PrintedComplexGenerator_eq, Matrix.trace_smul,
      cmp99SUNLieComplexCoordMatrixLM_trace, smul_zero]
  have hexp : Matrix.det
      (physicalMatrixExp
        (((Complex.I : ℂ) * (eta : ℂ)) •
          cmp99Eq337PrintedComplexLieMatrix (A b))) = 1 := by
    simpa [physicalMatrixExp, htrace] using
      det_matrix_exp_eq_exp_trace
        (((Complex.I : ℂ) * (eta : ℂ)) •
          cmp99Eq337PrintedComplexLieMatrix (A b))
  have hU : Matrix.det (U (positiveEdgeOfPhysicalBond b)).val = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp
      (U (positiveEdgeOfPhysicalBond b)).property).2
  rw [hexp, hU, one_mul]

/-- Positive-bond value in the literal complex gauge group `SL(N,C)`. -/
def cmp99Eq337PhysicalComplexPerturbedPositiveBondSL
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (b : PhysicalBond d N) :
    Matrix.SpecialLinearGroup (Fin Nc) ℂ :=
  ⟨cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix U A eta b,
    cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix_det U A eta b⟩

/-- Full oriented complex background reconstructed canonically from the
literal positive-bond perturbations. -/
def cmp99Eq337PhysicalComplexPerturbedBackground
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) :
    GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ) :=
  gaugeConfigOfPositiveBonds fun b =>
    cmp99Eq337PhysicalComplexPerturbedPositiveBondSL U A eta b

@[simp] theorem cmp99Eq337PhysicalComplexPerturbedBackground_apply_pos
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (b : PhysicalBond d N) :
    ((cmp99Eq337PhysicalComplexPerturbedBackground U A eta
        (positiveEdgeOfPhysicalBond b) :
      Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
        Matrix (Fin Nc) (Fin Nc) ℂ) =
      cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix U A eta b := by
  simp [cmp99Eq337PhysicalComplexPerturbedBackground,
    cmp99Eq337PhysicalComplexPerturbedPositiveBondSL]

end

end YangMills.RG
