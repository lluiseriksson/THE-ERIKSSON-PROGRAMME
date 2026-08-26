import tmp.BalabanCMP99Eq359ComplexClosedPhysicalTowerPair.draft
import tmp.BalabanCMP99Eq360ComplexRegionalLaplacian.draft
import tmp.BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation.draft

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# Source-specific complex precision identity for CMP99 (3.60)

This producer constructs both analytic backgrounds, both regional covariant
Laplacians, the common-target Eq. (3.59) tower pair, both complete precisions
and the four-term perturbation from one physical source input.  In particular,
the caller supplies neither `Delta0/Delta1`, `Q0/Q1`, the printed starred
operators nor a finished Eq. (3.60) equality.

The local expansion of the Laplacian difference into `V'_1(A)` and the
source estimates (3.61)--(3.63) remain open and visible downstream.  This
module proves only the exact source-operator identity needed before them.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]
variable [NeZero (d * (M - 1))]

/-- Physical inputs and already named source-domain/radius premises required
to construct the two analytic towers.  No operator or Eq. (3.60) conclusion
is a field of this input. -/
structure CMP99Eq360ComplexClosedPhysicalInput
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (spacing : ℝ) where
  U : PhysicalGaugeBackground d N Nc
  A : CMP99Eq337PhysicalComplexOneCochain d N Nc
  eta epsilonU rA R : ℝ
  rA_nonneg : 0 ≤ rA
  A_bound : ∀ b, ‖A b‖ ≤ rA
  perturbation_small : |eta| *
    (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2
  baseline_near_identity : ∀ b,
    ‖(U (positiveEdgeOfPhysicalBond b) :
      Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU
  radiusBudget : CMP99ComplexClosedRadiusBudget
    (d * (M - 1)) M depth
    (cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA)
    R (cmp99UbarNoWindingThreshold Nc)

namespace CMP99Eq360ComplexClosedPhysicalInput

variable {Omega : ActiveGaugeRegion d N}
variable {regions : CMP99SourceActiveRegionChain d M N Omega depth}
variable {hd : 2 ≤ d} {hM : 2 ≤ M} {spacing : ℝ}

/-- Baseline analytic background, using the same literal perturbation
constructor at parameter zero as the paired Eq. (3.59) recursion. -/
def background0
    (S : CMP99Eq360ComplexClosedPhysicalInput regions hd hM spacing) :
    GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ) :=
  cmp99Eq337PhysicalComplexPerturbedBackground S.U S.A 0

/-- Perturbed analytic background `exp(i eta A') U`. -/
def background1
    (S : CMP99Eq360ComplexClosedPhysicalInput regions hd hM spacing) :
    GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ) :=
  cmp99Eq337PhysicalComplexPerturbedBackground S.U S.A S.eta

/-- Common-target source Eq. (3.59) tower pair, constructed internally. -/
noncomputable def towerPair
    (S : CMP99Eq360ComplexClosedPhysicalInput regions hd hM spacing) :
    CMP99Eq359ComplexRegionalTowerPair (Nc := Nc) Omega spacing :=
  cmp99Eq359SourceComplexClosedPhysicalTowerPair regions hd hM spacing
    S.U S.A S.eta S.epsilonU S.rA S.R S.rA_nonneg S.A_bound
    S.perturbation_small S.baseline_near_identity S.radiusBudget

/-- Literal analytic baseline regional Laplacian. -/
noncomputable def baselineLaplacian
    (S : CMP99Eq360ComplexClosedPhysicalInput regions hd hM spacing) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99Eq360ComplexRegionalLaplacian Omega S.background0 spacing

/-- Literal analytic perturbed regional Laplacian. -/
noncomputable def perturbedLaplacian
    (S : CMP99Eq360ComplexClosedPhysicalInput regions hd hM spacing) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99Eq360ComplexRegionalLaplacian Omega S.background1 spacing

/-- Complete baseline analytic precision, with the source `Q'` and printed
starred synthesis from the internally constructed pair. -/
noncomputable def baselinePrecision
    (S : CMP99Eq360ComplexClosedPhysicalInput regions hd hM spacing)
    (a : ℂ) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99Eq360ComplexRegionalPrecision S.baselineLaplacian
    S.towerPair.Q0 S.towerPair.starred0 a

/-- Complete perturbed analytic precision on the same regional carrier. -/
noncomputable def perturbedPrecision
    (S : CMP99Eq360ComplexClosedPhysicalInput regions hd hM spacing)
    (a : ℂ) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99Eq360ComplexRegionalPrecision S.perturbedLaplacian
    S.towerPair.Q1 S.towerPair.starred1 a

/-- Literal four-term analytic perturbation `V'(A)` of (3.60). -/
noncomputable def precisionPerturbation
    (S : CMP99Eq360ComplexClosedPhysicalInput regions hd hM spacing)
    (a : ℂ) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99Eq360ComplexRegionalPrecisionPerturbation S.towerPair
    S.baselineLaplacian S.perturbedLaplacian a

/-- Source-specific exact Eq. (3.60).  Every operator in the equality is
constructed from `S`; the proof is the already isolated four-term algebra. -/
theorem perturbedPrecision_eq_baselinePrecision_sub_perturbation
    (S : CMP99Eq360ComplexClosedPhysicalInput regions hd hM spacing)
    (a : ℂ) :
    S.perturbedPrecision a =
      S.baselinePrecision a - S.precisionPerturbation a := by
  exact cmp99Eq360_complexRegionalPrecision_eq_sub_perturbation
    S.towerPair S.baselineLaplacian S.perturbedLaplacian a

end CMP99Eq360ComplexClosedPhysicalInput

end

end YangMills.RG
