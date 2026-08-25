import YangMills.RG.BalabanCMP99ComplexUbarCoordinateExponent
import YangMills.RG.BalabanCMP116WilsonBackgroundFactorBounds
import YangMills.RG.OrderedExponentialQuadraticBound

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

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

/-- Literal visible radius: physical background displacement plus twice the
complex exponential scale. -/
noncomputable def cmp99Eq337PhysicalComplexPerturbedLinkRadius
    (Nc : ℕ) (epsilonU eta rA : ℝ) : ℝ :=
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
    norm_nonneg _
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

end

end YangMills.RG
