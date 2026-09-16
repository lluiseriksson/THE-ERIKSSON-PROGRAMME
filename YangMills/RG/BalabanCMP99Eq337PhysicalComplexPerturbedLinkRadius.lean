import YangMills.RG.BalabanCMP99ComplexUbarCoordinateExponent
import YangMills.RG.BalabanCMP116WilsonBackgroundFactorBounds
import YangMills.RG.BalabanCMP98GAdConjugation
import YangMills.RG.OrderedExponentialQuadraticBound

/-!
# Positive-link radius for the literal complex CMP99 (3.37) background

This leaf consumes the named operator-norm cost of the complex physical Lie
coordinate chart.  It proves the positive-orientation radius directly for
`exp(eta A) U`; it neither assumes that the chart is isometric nor imports
unitarity for the complex exponential.  The reverse-orientation identity
`(exp(eta A) U)⁻¹ = U⁻¹ exp(-eta A)` remains a separate downstream gate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

local instance cmp99Eq337PhysicalComplexPerturbedMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Literal visible radius: physical background displacement plus twice the
complex exponential scale. -/
noncomputable def cmp99Eq337PhysicalComplexPerturbedLinkRadius
    (Nc : ℕ) [NeZero Nc] (epsilonU eta rA : ℝ) : ℝ :=
  epsilonU + 2 *
    (|eta| * cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA)

/-- The positive bond of the literal complex (3.37) background has the named
chart-cost radius.  The only analytic inputs are the physical link radius,
the printed complex-coordinate radius and the half-unit exponential gate. -/
theorem norm_cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix_sub_one_le
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta epsilonU rA : ℝ) (b : PhysicalBond d N)
    (hA : ‖A b‖ ≤ rA)
    (hsmall : |eta| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (hU : ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU) :
    ‖cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix U A eta b - 1‖ ≤
      cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA := by
  let X := cmp99SUNLieComplexCoordMatrixLM Nc (A b)
  let U0 : Matrix (Fin Nc) (Fin Nc) ℂ :=
    U (positiveEdgeOfPhysicalBond b)
  have hbudget : 0 ≤ cmp99SUNLieComplexCoordMatrixNormBudget Nc :=
    cmp99SUNLieComplexCoordMatrixNormBudget_nonneg
  have hX : ‖X‖ ≤
      cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA := by
    exact (norm_cmp99SUNLieComplexCoordMatrixLM_le (A b)).trans
      (mul_le_mul_of_nonneg_left hA hbudget)
  have hexp := norm_exp_smul_sub_one_le_two_mul eta
    (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) X hX hsmall
  have hU0 : ‖U0‖ = 1 := by
    let e : ConcreteEdge d N := ⟨b.1, b.2, true⟩
    simpa [U0, e, orientedWilsonPositiveBase] using
      norm_orientedWilsonPositiveBase U e
  have hproduct :
      ‖NormedSpace.exp (eta • X) * U0 - 1‖ ≤
        ‖NormedSpace.exp (eta • X) - 1‖ * ‖U0‖ + ‖U0 - 1‖ := by
    calc
      ‖NormedSpace.exp (eta • X) * U0 - 1‖ =
          ‖(NormedSpace.exp (eta • X) - 1) * U0 + (U0 - 1)‖ := by
            congr 1
            noncomm_ring
      _ ≤ ‖(NormedSpace.exp (eta • X) - 1) * U0‖ + ‖U0 - 1‖ :=
        norm_add_le _ _
      _ ≤ ‖NormedSpace.exp (eta • X) - 1‖ * ‖U0‖ + ‖U0 - 1‖ :=
        add_le_add (norm_mul_le _ _) le_rfl
  rw [cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix,
    cmp99Eq337PrintedComplexGenerator_eq]
  change ‖NormedSpace.exp (eta • X) * U0 - 1‖ ≤ _
  calc
    ‖NormedSpace.exp (eta • X) * U0 - 1‖ ≤
        ‖NormedSpace.exp (eta • X) - 1‖ * ‖U0‖ + ‖U0 - 1‖ := hproduct
    _ ≤ (2 * (|eta| *
          (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA))) * ‖U0‖ +
          epsilonU := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hexp (norm_nonneg U0)) hU
    _ = cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA := by
      rw [hU0]
      unfold cmp99Eq337PhysicalComplexPerturbedLinkRadius
      ring

/-- The explicit reverse-orientation matrix model `U† exp(-eta A)` has the
same radius.  This is the analytic half of the negative-link theorem; the
separate algebraic bridge to the inverse value of the reconstructed
`SL(N,C)` background is intentionally not hidden here. -/
theorem norm_cmp99Eq337PhysicalComplexPerturbedNegativeBondModel_sub_one_le
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta epsilonU rA : ℝ) (b : PhysicalBond d N)
    (hA : ‖A b‖ ≤ rA)
    (hsmall : |eta| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (hU : ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU) :
    ‖Matrix.conjTranspose (U (positiveEdgeOfPhysicalBond b) :
          Matrix (Fin Nc) (Fin Nc) ℂ) *
        NormedSpace.exp
          ((-eta) • cmp99SUNLieComplexCoordMatrixLM Nc (A b)) - 1‖ ≤
      cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA := by
  let X := cmp99SUNLieComplexCoordMatrixLM Nc (A b)
  let U0 : Matrix (Fin Nc) (Fin Nc) ℂ :=
    U (positiveEdgeOfPhysicalBond b)
  have hbudget : 0 ≤ cmp99SUNLieComplexCoordMatrixNormBudget Nc :=
    cmp99SUNLieComplexCoordMatrixNormBudget_nonneg
  have hX : ‖X‖ ≤
      cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA := by
    exact (norm_cmp99SUNLieComplexCoordMatrixLM_le (A b)).trans
      (mul_le_mul_of_nonneg_left hA hbudget)
  have hexp :
      ‖NormedSpace.exp ((-eta) • X) - 1‖ ≤
        2 * (|eta| *
          (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA)) := by
    simpa only [abs_neg] using
      norm_exp_smul_sub_one_le_two_mul (-eta)
        (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) X hX
        (by simpa only [abs_neg] using hsmall)
  have hU0 : ‖Matrix.conjTranspose U0‖ = 1 := by
    let e : ConcreteEdge d N := ⟨b.1, b.2, true⟩
    rw [Matrix.l2_opNorm_conjTranspose]
    simpa [U0, e, orientedWilsonPositiveBase] using
      norm_orientedWilsonPositiveBase U e
  have hUdev : ‖Matrix.conjTranspose U0 - 1‖ ≤ epsilonU := by
    calc
      ‖Matrix.conjTranspose U0 - 1‖ =
          ‖Matrix.conjTranspose (U0 - 1)‖ := by simp
      _ = ‖U0 - 1‖ := Matrix.l2_opNorm_conjTranspose _
      _ ≤ epsilonU := hU
  change ‖Matrix.conjTranspose U0 *
      NormedSpace.exp ((-eta) • X) - 1‖ ≤ _
  calc
    ‖Matrix.conjTranspose U0 * NormedSpace.exp ((-eta) • X) - 1‖ =
        ‖Matrix.conjTranspose U0 *
            (NormedSpace.exp ((-eta) • X) - 1) +
          (Matrix.conjTranspose U0 - 1)‖ := by
          congr 1
          noncomm_ring
    _ ≤ ‖Matrix.conjTranspose U0 *
          (NormedSpace.exp ((-eta) • X) - 1)‖ +
        ‖Matrix.conjTranspose U0 - 1‖ :=
      norm_add_le _ _
    _ ≤ ‖Matrix.conjTranspose U0‖ *
          ‖NormedSpace.exp ((-eta) • X) - 1‖ + epsilonU :=
      add_le_add (norm_mul_le _ _) hUdev
    _ ≤ 1 * (2 * (|eta| *
          (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA))) + epsilonU := by
      exact add_le_add
        (mul_le_mul hU0.le hexp (norm_nonneg _) (by norm_num)) le_rfl
    _ = cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA := by
      unfold cmp99Eq337PhysicalComplexPerturbedLinkRadius
      ring

/-- Coercing the inverse positive `SL(N,C)` bond gives the literal reversed
matrix `U† exp(-eta A)`.  This is an algebraic equality, not an inverse-norm
estimate. -/
theorem cmp99Eq337PhysicalComplexPerturbedPositiveBondSL_inv_coe
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (b : PhysicalBond d N) :
    (((cmp99Eq337PhysicalComplexPerturbedPositiveBondSL U A eta b)⁻¹ :
        Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
          Matrix (Fin Nc) (Fin Nc) ℂ) =
      Matrix.conjTranspose (U (positiveEdgeOfPhysicalBond b) :
          Matrix (Fin Nc) (Fin Nc) ℂ) *
        NormedSpace.exp
          ((-eta) • cmp99SUNLieComplexCoordMatrixLM Nc (A b)) := by
  let X := cmp99SUNLieComplexCoordMatrixLM Nc (A b)
  let U0 : Matrix (Fin Nc) (Fin Nc) ℂ :=
    U (positiveEdgeOfPhysicalBond b)
  have hexp :
      NormedSpace.exp ((-eta) • X) * NormedSpace.exp (eta • X) = 1 := by
    simpa only [neg_smul] using cmp98_exp_neg_mul_exp (eta • X)
  have hunit : Matrix.conjTranspose U0 * U0 = 1 := by
    simpa only [U0] using
      su_conjTranspose_mul_self (U (positiveEdgeOfPhysicalBond b))
  have hinv :
      (cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix U A eta b)⁻¹ =
        Matrix.conjTranspose U0 * NormedSpace.exp ((-eta) • X) := by
    apply Matrix.inv_eq_left_inv
    rw [cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix,
      cmp99Eq337PrintedComplexGenerator_eq]
    change (Matrix.conjTranspose U0 * NormedSpace.exp ((-eta) • X)) *
        (NormedSpace.exp (eta • X) * U0) = 1
    calc
      (Matrix.conjTranspose U0 * NormedSpace.exp ((-eta) • X)) *
          (NormedSpace.exp (eta • X) * U0) =
        Matrix.conjTranspose U0 *
          ((NormedSpace.exp ((-eta) • X) *
            NormedSpace.exp (eta • X)) * U0) := by
              simp only [mul_assoc]
      _ = Matrix.conjTranspose U0 * U0 := by rw [hexp, one_mul]
      _ = 1 := hunit
  have hmatrixInv :
      (cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix U A eta b)⁻¹ =
        Matrix.adjugate
          (cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix U A eta b) := by
    rw [Matrix.inv_def,
      cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix_det,
      Ring.inverse_one, one_smul]
  rw [Matrix.SpecialLinearGroup.coe_inv]
  change Matrix.adjugate
      (cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix U A eta b) = _
  rw [← hmatrixInv]
  exact hinv

/-- The public negative edge of the reconstructed complex background is the
same reversed matrix model used by the analytic radius theorem. -/
theorem cmp99Eq337PhysicalComplexPerturbedBackground_apply_neg_matrix
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (x : FinBox d N) (mu : Fin d) :
    ((cmp99Eq337PhysicalComplexPerturbedBackground U A eta
        (ConcreteEdge.mk x mu false) :
          Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
            Matrix (Fin Nc) (Fin Nc) ℂ) =
      Matrix.conjTranspose (U (positiveEdgeOfPhysicalBond (x, mu)) :
          Matrix (Fin Nc) (Fin Nc) ℂ) *
        NormedSpace.exp
          ((-eta) • cmp99SUNLieComplexCoordMatrixLM Nc (A (x, mu))) := by
  rw [cmp99Eq337PhysicalComplexPerturbedBackground,
    gaugeConfigOfPositiveBonds_apply_neg]
  exact cmp99Eq337PhysicalComplexPerturbedPositiveBondSL_inv_coe
    U A eta (x, mu)

end

end YangMills.RG
