import YangMills.RG.BalabanCMP98ContourExponentialTransport
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbedLinkRadius
import YangMills.RG.BalabanCMP99Eq351ExponentialAdjointRemainder
import YangMills.RG.BalabanCMP99Eq351PhysicalComplexOrientedPerturbation
import YangMills.RG.BalabanCMP99Eq351PhysicalComplexPositiveBondFactorization

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# CMP99 (3.50): exact negative-bond factorization

The regional stencil contains both orientations.  This leaf proves that the
canonical negative edge of the reconstructed complex background is still the
literal source exponential `exp(i eta A'(b))` followed by the same oriented
compact background.  The negative `A'` is constructed internally from the
sealed physical reversal transport; no negative-edge field or factorization
is supplied by the caller.
-/

namespace YangMills.RG

noncomputable section

open Matrix

variable {d N Nc : Nat} [NeZero d] [NeZero N] [NeZero Nc]

local instance cmp99Eq351NegativeBondMatrixNormedRing :
    NormedRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
  Matrix.frobeniusNormedRing

local instance cmp99Eq351NegativeBondMatrixNormedAlgebra :
    NormedAlgebra ℂ (Matrix (Fin Nc) (Fin Nc) ℂ) :=
  Matrix.frobeniusNormedAlgebra

/-- The explicitly complexified compact adjoint action is literal matrix
conjugation on every complex coordinate, not only on the real slice. -/
theorem cmp99SUNLieComplexCoordMatrixLM_adjointComplexAction
    (g : SUN Nc) (Z : SUNLieComplexCoord Nc) :
    cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SUNAdjointComplexActionLM (matrixSUNAdjointModel Nc) g Z) =
      (g : Matrix (Fin Nc) (Fin Nc) ℂ) *
        cmp99SUNLieComplexCoordMatrixLM Nc Z *
          Matrix.conjTranspose (g : Matrix (Fin Nc) (Fin Nc) ℂ) := by
  change
    cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SUNLieCoordComplexificationLM Nc
              ((matrixSUNAdjointModel Nc).adCLM g
                (cmp99SUNLieComplexCoordRealPart Z)) +
          Complex.I • cmp99SUNLieCoordComplexificationLM Nc
              ((matrixSUNAdjointModel Nc).adCLM g
                (cmp99SUNLieComplexCoordImagPart Z))) = _
  rw [map_add, map_smul,
    cmp99SUNLieComplexCoordMatrixLM_complexification,
    cmp99SUNLieComplexCoordMatrixLM_complexification,
    cmp98LieCoordMatrix_adCLM, cmp98LieCoordMatrix_adCLM]
  change
    (g : Matrix (Fin Nc) (Fin Nc) ℂ) *
          cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart Z) *
            Matrix.conjTranspose (g : Matrix (Fin Nc) (Fin Nc) ℂ) +
        Complex.I •
          ((g : Matrix (Fin Nc) (Fin Nc) ℂ) *
            cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart Z) *
              Matrix.conjTranspose (g : Matrix (Fin Nc) (Fin Nc) ℂ)) =
      (g : Matrix (Fin Nc) (Fin Nc) ℂ) *
        (cmp98LieCoordMatrix (cmp99SUNLieComplexCoordRealPart Z) +
          Complex.I •
            cmp98LieCoordMatrix (cmp99SUNLieComplexCoordImagPart Z)) *
          Matrix.conjTranspose (g : Matrix (Fin Nc) (Fin Nc) ℂ)
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]

/-- The printed Hermitian-coordinate convention commutes with the same
compact adjoint transport. -/
theorem cmp99Eq337PrintedComplexLieMatrix_adjointComplexAction
    (g : SUN Nc) (Z : SUNLieComplexCoord Nc) :
    cmp99Eq337PrintedComplexLieMatrix
        (cmp99SUNAdjointComplexActionLM (matrixSUNAdjointModel Nc) g Z) =
      (g : Matrix (Fin Nc) (Fin Nc) ℂ) *
        cmp99Eq337PrintedComplexLieMatrix Z *
          Matrix.conjTranspose (g : Matrix (Fin Nc) (Fin Nc) ℂ) := by
  unfold cmp99Eq337PrintedComplexLieMatrix
  rw [cmp99SUNLieComplexCoordMatrixLM_adjointComplexAction]
  rw [mul_smul_comm, smul_mul_assoc]

@[simp] theorem cmp99Eq337PrintedComplexLieMatrix_neg
    (Z : SUNLieComplexCoord Nc) :
    cmp99Eq337PrintedComplexLieMatrix (-Z) =
      -cmp99Eq337PrintedComplexLieMatrix Z := by
  unfold cmp99Eq337PrintedComplexLieMatrix
  rw [map_neg]
  module

/-- Literal matrix generator `i eta A'(e)` on an arbitrary oriented edge. -/
def cmp99Eq351PhysicalComplexOrientedGeneratorMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (e : ConcreteEdge d N) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  (((Complex.I : ℂ) * (eta : ℂ)) •
    cmp99Eq337PrintedComplexLieMatrix
      (cmp99Eq351PhysicalComplexOrientedPerturbation U A e))

@[simp] theorem cmp99Eq351PhysicalComplexOrientedGeneratorMatrix_pos
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (x : FinBox d N) (mu : Fin d) :
    cmp99Eq351PhysicalComplexOrientedGeneratorMatrix U A eta
        (ConcreteEdge.mk x mu true) =
      cmp99Eq351PhysicalComplexPositiveGeneratorMatrix A eta (x, mu) := by
  simp [cmp99Eq351PhysicalComplexOrientedGeneratorMatrix,
    cmp99Eq351PhysicalComplexPositiveGeneratorMatrix]

/-- The negative generator is the compact conjugate of the negative positive-
bond generator.  This is the exact transport needed by the negative stencil
term; it is not inferred from the positive factorization. -/
theorem cmp99Eq351PhysicalComplexOrientedGeneratorMatrix_neg
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (x : FinBox d N) (mu : Fin d) :
    cmp99Eq351PhysicalComplexOrientedGeneratorMatrix U A eta
        (ConcreteEdge.mk x mu false) =
      (U (ConcreteEdge.mk x mu false) :
          Matrix (Fin Nc) (Fin Nc) ℂ) *
        (-cmp99Eq351PhysicalComplexPositiveGeneratorMatrix A eta (x, mu)) *
          Matrix.conjTranspose
            (U (ConcreteEdge.mk x mu false) :
              Matrix (Fin Nc) (Fin Nc) ℂ) := by
  rw [cmp99Eq351PhysicalComplexOrientedGeneratorMatrix,
    cmp99Eq351PhysicalComplexOrientedPerturbation_neg,
    cmp99Eq337PrintedComplexLieMatrix_neg,
    cmp99Eq337PrintedComplexLieMatrix_adjointComplexAction]
  unfold cmp99Eq351PhysicalComplexPositiveGeneratorMatrix
  rw [smul_neg, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]

/-- Canonical determinant-one exponential of the literal oriented generator. -/
def cmp99Eq351PhysicalComplexOrientedExponentSL
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (e : ConcreteEdge d N) :
    Matrix.SpecialLinearGroup (Fin Nc) ℂ := by
  let Y := cmp99Eq351PhysicalComplexOrientedGeneratorMatrix U A eta e
  refine ⟨physicalMatrixExp Y, ?_⟩
  have htrace : Matrix.trace Y = 0 := by
    dsimp [Y, cmp99Eq351PhysicalComplexOrientedGeneratorMatrix]
    rw [cmp99Eq337PrintedComplexGenerator_eq, Matrix.trace_smul,
      cmp99SUNLieComplexCoordMatrixLM_trace, smul_zero]
  simpa [physicalMatrixExp, htrace] using
    det_matrix_exp_eq_exp_trace Y

@[simp] theorem cmp99Eq351PhysicalComplexOrientedExponentSL_coe
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (e : ConcreteEdge d N) :
    ((cmp99Eq351PhysicalComplexOrientedExponentSL U A eta e :
        Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
      Matrix (Fin Nc) (Fin Nc) ℂ) =
      physicalMatrixExp
        (cmp99Eq351PhysicalComplexOrientedGeneratorMatrix U A eta e) :=
  rfl

/-- The inverse of the oriented source exponential is the exponential of the
negative of the same internally constructed generator.  The later negative-
edge adjoint expansion cites this theorem rather than treating inversion of
the exponential as a simplifier convention. -/
@[simp] theorem cmp99Eq351PhysicalComplexOrientedExponentSL_inv_coe
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (e : ConcreteEdge d N) :
    (((cmp99Eq351PhysicalComplexOrientedExponentSL U A eta e)⁻¹ :
        Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
      Matrix (Fin Nc) (Fin Nc) ℂ) =
      physicalMatrixExp
        (-cmp99Eq351PhysicalComplexOrientedGeneratorMatrix U A eta e) := by
  let Y := cmp99Eq351PhysicalComplexOrientedGeneratorMatrix U A eta e
  have hinv : (physicalMatrixExp Y)⁻¹ = physicalMatrixExp (-Y) := by
    apply Matrix.inv_eq_left_inv
    simpa only [physicalMatrixExp] using cmp98_exp_neg_mul_exp Y
  rw [Matrix.SpecialLinearGroup.coe_inv]
  change Matrix.adjugate (physicalMatrixExp Y) = physicalMatrixExp (-Y)
  have hdet : Matrix.det (physicalMatrixExp Y) = 1 :=
    (cmp99Eq351PhysicalComplexOrientedExponentSL U A eta e).property
  rw [← show (physicalMatrixExp Y)⁻¹ = Matrix.adjugate (physicalMatrixExp Y) by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]]
  exact hinv

/-- Exact matrix factorization of the canonical perturbed negative edge.
The proof uses physical unitarity to conjugate the same positive-bond
exponential; the negative field and background are both the canonical
oriented objects already present in the tree. -/
theorem cmp99Eq351PhysicalComplexPerturbedNegativeBondMatrix_eq_mul
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (x : FinBox d N) (mu : Fin d) :
    ((cmp99Eq337PhysicalComplexPerturbedBackground U A eta
        (ConcreteEdge.mk x mu false) :
          Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
      Matrix (Fin Nc) (Fin Nc) ℂ) =
      ((cmp99Eq351PhysicalComplexOrientedExponentSL U A eta
          (ConcreteEdge.mk x mu false) :
            Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
        Matrix (Fin Nc) (Fin Nc) ℂ) *
      (U (ConcreteEdge.mk x mu false) :
        Matrix (Fin Nc) (Fin Nc) ℂ) := by
  let g : SUN Nc := U (ConcreteEdge.mk x mu false)
  let Y := cmp99Eq351PhysicalComplexPositiveGeneratorMatrix A eta (x, mu)
  have hU := U.map_reverse (ConcreteEdge.mk x mu true)
  change U (ConcreteEdge.mk x mu false) =
      (U (ConcreteEdge.mk x mu true))⁻¹ at hU
  have hg : (g : Matrix (Fin Nc) (Fin Nc) ℂ) =
      Matrix.conjTranspose
        (U (positiveEdgeOfPhysicalBond (x, mu)) :
          Matrix (Fin Nc) (Fin Nc) ℂ) := by
    rw [show g = U (ConcreteEdge.mk x mu false) by rfl, hU,
      coe_sun_inv_eq_conjTranspose]
    rfl
  have hunit : Matrix.conjTranspose
        (g : Matrix (Fin Nc) (Fin Nc) ℂ) *
      (g : Matrix (Fin Nc) (Fin Nc) ℂ) = 1 := by
    simpa using su_conjTranspose_mul_self g
  have hgen :
      cmp99Eq351PhysicalComplexOrientedGeneratorMatrix U A eta
          (ConcreteEdge.mk x mu false) =
        (g : Matrix (Fin Nc) (Fin Nc) ℂ) * (-Y) *
          Matrix.conjTranspose (g : Matrix (Fin Nc) (Fin Nc) ℂ) := by
    simpa only [g, Y] using
      cmp99Eq351PhysicalComplexOrientedGeneratorMatrix_neg U A eta x mu
  have hexp := physicalMatrixExp_unitary_conj
    (specialUnitaryToUnitary g) (-Y)
  change physicalMatrixExp
      ((g : Matrix (Fin Nc) (Fin Nc) ℂ) * (-Y) *
        Matrix.conjTranspose (g : Matrix (Fin Nc) (Fin Nc) ℂ)) =
      (g : Matrix (Fin Nc) (Fin Nc) ℂ) *
        physicalMatrixExp (-Y) *
          Matrix.conjTranspose (g : Matrix (Fin Nc) (Fin Nc) ℂ) at hexp
  have hnegexp :
      NormedSpace.exp
          ((-eta) • cmp99SUNLieComplexCoordMatrixLM Nc (A (x, mu))) =
        physicalMatrixExp (-Y) := by
    unfold physicalMatrixExp
    change NormedSpace.exp
      (((-eta : ℝ) : ℂ) •
        cmp99SUNLieComplexCoordMatrixLM Nc (A (x, mu))) =
      NormedSpace.exp (-Y)
    rw [← cmp99Eq337PrintedComplexGenerator_eq (-eta) (A (x, mu))]
    change NormedSpace.exp
      (cmp99Eq351PhysicalComplexPositiveGeneratorMatrix A (-eta) (x, mu)) =
      NormedSpace.exp (-Y)
    rw [cmp99Eq351PhysicalComplexPositiveGeneratorMatrix_neg]
  rw [cmp99Eq337PhysicalComplexPerturbedBackground_apply_neg_matrix,
    cmp99Eq351PhysicalComplexOrientedExponentSL_coe, hgen, hexp,
    hnegexp]
  rw [← hg]
  symm
  calc
    ((g : Matrix (Fin Nc) (Fin Nc) ℂ) * physicalMatrixExp (-Y) *
        Matrix.conjTranspose (g : Matrix (Fin Nc) (Fin Nc) ℂ)) *
        (g : Matrix (Fin Nc) (Fin Nc) ℂ) =
      (g : Matrix (Fin Nc) (Fin Nc) ℂ) * physicalMatrixExp (-Y) *
        (Matrix.conjTranspose (g : Matrix (Fin Nc) (Fin Nc) ℂ) *
          (g : Matrix (Fin Nc) (Fin Nc) ℂ)) := by
            simp only [mul_assoc]
    _ = (g : Matrix (Fin Nc) (Fin Nc) ℂ) * physicalMatrixExp (-Y) := by
          rw [hunit, mul_one]

/-- Group-level source identity consumed by the regional Laplacian
regrouping. -/
theorem cmp99Eq351PhysicalComplexPerturbedNegativeBondSL_eq_mul
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (x : FinBox d N) (mu : Fin d) :
    cmp99Eq337PhysicalComplexPerturbedBackground U A eta
        (ConcreteEdge.mk x mu false) =
      cmp99Eq351PhysicalComplexOrientedExponentSL U A eta
          (ConcreteEdge.mk x mu false) *
        cmp99SUNToSpecialLinear Nc
          (U (ConcreteEdge.mk x mu false)) := by
  apply Subtype.ext
  simpa [cmp99SUNToSpecialLinear_coe] using
    cmp99Eq351PhysicalComplexPerturbedNegativeBondMatrix_eq_mul
      U A eta x mu

/-- Matrix form of the exact negative-bond adjoint expansion used in (3.51).

The oriented generator, the compact baseline transport and the nonlinear
remainder are all constructed internally from the canonical negative edge.
In particular, this is not obtained by relabelling the positive-bond theorem
or by accepting a caller-supplied negative perturbation. -/
theorem cmp99Eq351PhysicalComplexPerturbedNegativeAdjointMatrix_eq
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (x : FinBox d N) (mu : Fin d)
    (Z : SUNLieComplexCoord Nc) :
    let e := ConcreteEdge.mk x mu false
    let Y := cmp99Eq351PhysicalComplexOrientedGeneratorMatrix U A eta e
    let X := cmp99SUNLieComplexCoordMatrixLM Nc
      (cmp99SpecialLinearAdjointCoordLM
        (cmp99SUNToSpecialLinear Nc (U e)) Z)
    cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SpecialLinearAdjointCoordLM
          (cmp99Eq337PhysicalComplexPerturbedBackground U A eta e) Z) =
      X + (Y * X - X * Y) +
        cmp99Eq351ExponentialAdjointRemainderCLM Y X := by
  dsimp only
  rw [cmp99Eq351PhysicalComplexPerturbedNegativeBondSL_eq_mul,
    cmp99SpecialLinearAdjointCoordLM_mul,
    cmp99SUNLieComplexCoordMatrixLM_specialLinearAdjoint,
    cmp99Eq351PhysicalComplexOrientedExponentSL_coe,
    cmp99Eq351PhysicalComplexOrientedExponentSL_inv_coe]
  simpa only [physicalMatrixExp] using
    cmp99Eq351_exponentialAdjoint_apply_eq_linear_add_remainder
      (cmp99Eq351PhysicalComplexOrientedGeneratorMatrix U A eta
        (ConcreteEdge.mk x mu false))
      (cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SpecialLinearAdjointCoordLM
          (cmp99SUNToSpecialLinear Nc
            (U (ConcreteEdge.mk x mu false))) Z))

/-- Backward-stencil form of the same source factorization.

The regional Laplacian reads the inverse of the positive link.  This theorem
rewrites that inverse to the canonical negative edge by the gauge-config
reversal law and then applies the internally proved negative factorization.
No inverse-link equality is supplied by a caller. -/
theorem cmp99Eq351PhysicalComplexPerturbedPositiveBondSL_inv_eq_oriented_mul
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (x : FinBox d N) (mu : Fin d) :
    (cmp99Eq337PhysicalComplexPerturbedBackground U A eta
        (ConcreteEdge.mk x mu true))⁻¹ =
      cmp99Eq351PhysicalComplexOrientedExponentSL U A eta
          (ConcreteEdge.mk x mu false) *
        cmp99SUNToSpecialLinear Nc
          (U (ConcreteEdge.mk x mu false)) := by
  have hreverse :=
    (cmp99Eq337PhysicalComplexPerturbedBackground U A eta).map_reverse
      (ConcreteEdge.mk x mu true)
  change
    cmp99Eq337PhysicalComplexPerturbedBackground U A eta
        (ConcreteEdge.mk x mu false) =
      (cmp99Eq337PhysicalComplexPerturbedBackground U A eta
        (ConcreteEdge.mk x mu true))⁻¹ at hreverse
  rw [← hreverse]
  exact cmp99Eq351PhysicalComplexPerturbedNegativeBondSL_eq_mul
    U A eta x mu

end

end YangMills.RG
