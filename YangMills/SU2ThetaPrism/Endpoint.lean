import YangMills.SU2ThetaPrism.Analysis
import YangMills.SU2ThetaPrism.Coefficients

/-!
# (9) Fabricante del prisma theta: six-point manufacturing endpoint

This endpoint composes only the abstract six-point theta gate.  It does not
state a physical-cell realization, reflection positivity, OS positivity, or
programme Gate 7.
-/

noncomputable section

open MeasureTheory

namespace YangMills.SU2ThetaPrism

/-- Pairing attached to the actually integrated witness norm. -/
def certifiedThetaPairing (a : TwiceSpin → ℝ) : ℝ :=
  thetaPairingFromMultipliers witnessNormSq.re a

theorem certifiedThetaPairing_exact (moments : NormMomentSteps)
    (a : TwiceSpin → ℝ) :
    certifiedThetaPairing a = a 2 * (a 1) ^ 2 / 16 := by
  have hnorm := congrArg Complex.re (witnessNormSq_eq_three_quarters moments)
  have hnormReal : witnessNormSq.re = 3 / 4 := by
    norm_num at hnorm ⊢
    exact hnorm
  rw [certifiedThetaPairing, hnormReal]
  exact thetaPairing_factor_sixteen a

theorem certifiedThetaPairing_gate (moments : NormMomentSteps)
    {a : TwiceSpin → ℝ} {beta : ℝ} (hbeta : BetaDomain beta)
    (series : CoefficientRemainderSteps a beta) :
    beta ^ 4 / 512 ≤ certifiedThetaPairing a := by
  have hnorm := congrArg Complex.re (witnessNormSq_eq_three_quarters moments)
  have hnormReal : witnessNormSq.re = 3 / 4 := by
    norm_num at hnorm ⊢
    exact hnorm
  rw [certifiedThetaPairing, hnormReal]
  exact thetaPairing_gate hbeta series

/-- The sole remaining manufacturing obligation.  Six former fields are now
discharged by concrete theorems: trace reality, the character bound,
fundamental Schur, ordinary Fubini plus the separately named Haar coordinate
change, witness norm moments, and weight measurability. -/
structure ManufacturingTechnicalInputs (beta : ℝ) : Prop where
  coefficientSeries :
    SpinOneCoefficientRemainderStep beta

/-- Concrete-Haar, concrete-probe conditional front door.  It deliberately
retains the genuinely open coefficient-series obligation and therefore is not
a closed manufacturing certificate. -/
theorem manufactured_six_point_theta_gate
    (beta : ℝ) (hbeta : BetaDomain beta)
    (input : ManufacturingTechnicalInputs beta) :
    connectedCycleRank (Fintype.card HalfVertex) (Fintype.card Branch) = 2 ∧
    connectedCycleRank (Fintype.card HalfVertex) (Fintype.card ReducedBranch) = 1 ∧
    HasThreeDistinctBranches Branch ∧
    (¬ HasThreeDistinctBranches ReducedBranch) ∧
    (∀ c i, holonomy (reflect c) i = c.s⁻¹ * (holonomy c i)⁻¹ * c.s) ∧
    (∀ c, cellWeight beta (reflect c) = cellWeight beta c) ∧
    (∀ h U V, witness (h * U * h⁻¹) (h * V * h⁻¹) = witness U V) ∧
    witness ≠ (0 : SU2 → SU2 → ℂ) ∧
    CompleteUOrthogonality ∧
    CompleteVOrthogonality ∧
    CompleteRelativeOrthogonality ∧
    witnessNormSq = 3 / 4 ∧
    couplingMultiplicity 2 1 1 = 1 ∧
    certifiedThetaPairing (fun j => alpha su2WeylPolynomial beta j) =
      alpha su2WeylPolynomial beta 2 *
        (alpha su2WeylPolynomial beta 1) ^ 2 / 16 ∧
    beta ^ 4 / 512 ≤
      certifiedThetaPairing (fun j => alpha su2WeylPolynomial beta j) ∧
    Integrable (cellWeight beta) cellHaar := by
  refine ⟨threeBranch_cycleRank, reduced_cycleRank, branch_hasThreeDistinct,
    reducedBranch_not_hasThreeDistinct, holonomy_reflect,
    cellWeight_reflection_invariant traceRealityConcrete beta,
    witness_simultaneous_conj, witness_ne_zero,
    complete_U_orthogonality haarSchurConcrete fubiniCoordinatesConcrete,
    complete_V_orthogonality haarSchurConcrete fubiniCoordinatesConcrete,
    complete_relative_orthogonality haarSchurConcrete fubiniCoordinatesConcrete,
    witnessNormSq_eq_three_quarters normMomentsConcrete,
    theta_coupling_multiplicity_one,
    certifiedThetaPairing_exact normMomentsConcrete _,
    certifiedThetaPairing_gate normMomentsConcrete hbeta
      (coefficientRemainderSteps_of_spinOne hbeta.1.le input.coefficientSeries),
    cellWeight_integrable characterBoundConcrete beta
      (weightMeasurabilityConcrete beta)⟩

/-- Anti-vacuity bundle proved without using the endpoint inputs. -/
theorem endpoint_anti_vacuity :
    witness (1 : SU2) (1 : SU2) = 3 ∧
    haarSU2 (Set.univ : Set SU2) ≠ 0 ∧
    BetaDomain 1 ∧
    Fintype.card Branch = 3 ∧
    Nontrivial SU2 := by
  exact ⟨witness_one_one, haar_measure_nonzero, one_mem_betaDomain,
    branch_card, su2_nontrivial⟩

end YangMills.SU2ThetaPrism
