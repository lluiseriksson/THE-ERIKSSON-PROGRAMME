import YangMills.RG.BalabanCMP99SourceGaugeTransportedPrecisionGreen
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalPrecision

/-!
PRE-VALIDATION: source is present only in scratch; no `.olean` has been
materialized and none of the declarations below is compiler-verified.

# The canonical CMP99 Green on a regular gauge background

This closes the source specialization of C6c.8d.  The transformed endpoint is
the existing generated physical precision/Green on `gaugeAct u background`.
The regular endpoint is constructed internally through the paired retained
tower and exact inverse transport.  No regular-side smallness or Green
equality is accepted from the caller.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The canonical paired retained object on the source-generated active
region chain. -/
noncomputable def cmp99SourceGeneratedGaugeTransportedRetainedPair
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (u : GaugeTransform d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (transformedSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(gaugeAct u background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        epsilon) :
    CMP99SourceGaugeTransportedRetainedPair
      (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1))
      hd hM (matrixSUNAdjointModel Nc) spacing epsilon background u
      budget.toRadiusChain transformedSmall :=
  cmp99SourceGaugeTransportedRetainedPair
    (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1))
    hd hM (matrixSUNAdjointModel Nc) spacing epsilon background u
    budget.toRadiusChain transformedSmall

/-- The transformed precision of the paired construction is literally the
existing source-generated physical precision. -/
theorem cmp99SourceGeneratedGaugeTransportedRetainedPair_transformedPrecision_eq
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (u : GaugeTransform d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (transformedSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(gaugeAct u background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        epsilon) :
    let P := cmp99SourceGeneratedGaugeTransportedRetainedPair hd hM Omega
      depth spacing epsilon background budget u transformedSmall
    P.transformedPrecision
        (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon) =
      cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
        (gaugeAct u background) budget transformedSmall := by
  dsimp only
  unfold CMP99SourceGaugeTransportedRetainedPair.transformedPrecision
  unfold cmp99SourceGeneratedPhysicalPrecision
  rw [CMP99SourceGaugeTransportedRetainedPair.transformedTerminal_eq_generated]

/-- Coercivity of the exact canonical transformed precision, re-expressed on
the paired endpoint without weakening its constant. -/
theorem isCoerciveCLM_cmp99SourceGeneratedGaugeTransported_transformedPrecision
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (u : GaugeTransform d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (transformedSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(gaugeAct u background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    let P := cmp99SourceGeneratedGaugeTransportedRetainedPair hd hM Omega
      depth spacing epsilon background budget u transformedSmall
    IsCoerciveCLM
      (P.transformedPrecision
        (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon))
      (cmp99SourceGeneratedCoercivity d M (depth + 1) spacing epsilon) := by
  dsimp only
  rw [cmp99SourceGeneratedGaugeTransportedRetainedPair_transformedPrecision_eq]
  exact isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth
    hspacing (gaugeAct u background) budget transformedSmall hsmall

/-- The regular-background Green constructed from the exact physical mass
and the canonical transformed coercivity theorem. -/
noncomputable def cmp99SourceGeneratedGaugeRegularPhysicalGreen
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (u : GaugeTransform d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (transformedSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(gaugeAct u background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) :=
  let P := cmp99SourceGeneratedGaugeTransportedRetainedPair hd hM Omega
    depth spacing epsilon background budget u transformedSmall
  P.originalGreen
    (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon)
    (cmp99SourceGeneratedCoercivity_pos d M depth hspacing hsmall)
    (isCoerciveCLM_cmp99SourceGeneratedGaugeTransported_transformedPrecision
      hd hM Omega depth hspacing background budget u transformedSmall hsmall)

/-- The transformed Green inside the pair is the existing canonical
source-generated physical Green. -/
theorem cmp99SourceGeneratedGaugeTransported_transformedGreen_eq
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (u : GaugeTransform d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (transformedSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(gaugeAct u background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    let P := cmp99SourceGeneratedGaugeTransportedRetainedPair hd hM Omega
      depth spacing epsilon background budget u transformedSmall
    P.transformedGreen
        (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon)
        (cmp99SourceGeneratedCoercivity_pos d M depth hspacing hsmall)
        (isCoerciveCLM_cmp99SourceGeneratedGaugeTransported_transformedPrecision
          hd hM Omega depth hspacing background budget u transformedSmall
          hsmall) =
      cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
        (gaugeAct u background) budget transformedSmall hsmall := by
  dsimp only
  unfold CMP99SourceGaugeTransportedRetainedPair.transformedGreen
  unfold cmp99SourceGeneratedPhysicalGreen
  rw [cmp99SourceGeneratedGaugeTransportedRetainedPair_transformedPrecision_eq]

/-- Canonical CMP99 (3.31) for the generated Green: the known small Green
intertwines with the internally constructed regular-background Green. -/
theorem cmp99SourceGeneratedPhysicalGreen_gaugeRegular_intertwines
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (u : GaugeTransform d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (transformedSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(gaugeAct u background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    (cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
        (gaugeAct u background) budget transformedSmall hsmall).comp
        (cmp99RegionalFineGaugeLinearIsometryEquiv
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
          (matrixSUNAdjointModel Nc) u : _ →L[ℝ] _) =
      (cmp99RegionalFineGaugeLinearIsometryEquiv
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (matrixSUNAdjointModel Nc) u : _ →L[ℝ] _).comp
        (cmp99SourceGeneratedGaugeRegularPhysicalGreen hd hM Omega depth
          hspacing background budget u transformedSmall hsmall) := by
  let P := cmp99SourceGeneratedGaugeTransportedRetainedPair hd hM Omega
    depth spacing epsilon background budget u transformedSmall
  have h := P.transformedGreen_comp_gaugeIsometry
    (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon)
    (cmp99SourceGeneratedCoercivity_pos d M depth hspacing hsmall)
    (isCoerciveCLM_cmp99SourceGeneratedGaugeTransported_transformedPrecision
      hd hM Omega depth hspacing background budget u transformedSmall hsmall)
  rw [cmp99SourceGeneratedGaugeTransported_transformedGreen_eq] at h
  exact h

end

end YangMills.RG
