/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395Partition
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCRightFactor

/-!
# The physical local inverse in CMP99 equation (3.95)

For one generated source region this file transports the literal middle
operator `Q' (G')² Q'^*` to its coarse coordinates and proves that its
generated covariance is an exact right inverse there.  This is the
`A_D C_D = I` ingredient in (3.95), not an abstract inverse certificate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

/-- Restriction is a left inverse of zero extension on an arbitrary finite
active region. -/
theorem activeGaugeRegion_restrictZero_comp_extendZero
    {d N : ℕ} [NeZero N] {g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] (Omega : ActiveGaugeRegion d N) :
    (restrictZeroCLM (𝔤 := g) Omega).comp
        (extendZeroZeroCLM (𝔤 := g) Omega) =
      ContinuousLinearMap.id ℝ (ActiveGaugeZeroCochain Omega g) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  simp [restrictZeroCLM, extendZeroZeroCLM]

/-- The ambient realization of an active region is exactly its diagonal
characteristic projector. -/
theorem activeGaugeRegion_extendZero_comp_restrict_eq_multiplier
    {d N : ℕ} [NeZero N] {g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] (Omega : ActiveGaugeRegion d N) :
    (extendZeroZeroCLM (𝔤 := g) Omega).comp
        (restrictZeroCLM (𝔤 := g) Omega) =
      finitePiLpScalarMultiplier (g := g)
        (fun x : FinBox d N => if x ∈ Omega.sites then 1 else 0) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  by_cases hx : x ∈ Omega.sites <;>
    simp [ContinuousLinearMap.comp_apply, restrictZeroCLM,
      extendZeroZeroCLM, finitePiLpScalarMultiplier_apply, hx]

/-- Transporting an identity operator along one equality of terminal Hilbert
bundles is again the identity operator. -/
theorem cmp99SourceTerminalCLMTransport_id
    {E E' : CMP99SourceWeightedTowerHilbertSpace} (hE : E = E') :
    cmp99SourceTerminalCLMTransport hE hE
        (ContinuousLinearMap.id ℝ E.carrier) =
      ContinuousLinearMap.id ℝ E'.carrier := by
  cases hE
  rfl

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

/-- The literal regional middle `Q' (G')² Q'^*`, expressed on the same
finite coarse coordinate field as its generated inverse covariance. -/
noncomputable def generatedPhysicalCoarseCovarianceMiddleCoordinates
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpField
        (ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
        (SUNLieCoord Nc) →L[ℝ]
      FinitePiLpField
        (ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
        (SUNLieCoord Nc) := by
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM (D.operatorCoarseRegion hpi5 s) depth
    hspacing background budget fineSmall hsmall
  have hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 s) (depth + 1) spacing epsilon background
    budget.toRadiusChain fineSmall
  exact cmp99SourceTerminalCLMTransport hs hs Middle

/-- Exact physical local inverse identity `A_D C_D = I` in the common
coarse coordinates used by the Section C factors. -/
theorem generatedPhysicalCoarseCovarianceMiddleCoordinates_comp_covariance
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    (D.generatedPhysicalCoarseCovarianceMiddleCoordinates hpi5 s hM depth
      hspacing background budget fineSmall hsmall).comp
      (D.generatedPhysicalCoarseCovarianceCoordinates hpi5 s hM depth
        hspacing background budget fineSmall hsmall) =
      ContinuousLinearMap.id ℝ _ := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  have hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    Omega (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  have hinverse : Middle.comp C = ContinuousLinearMap.id ℝ _ :=
    cmp99SourceGeneratedPhysicalCoarseCovariance_middle_comp
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall
  change (cmp99SourceTerminalCLMTransport hs hs Middle).comp
      (cmp99SourceTerminalCLMTransport hs hs C) = _
  rw [cmp99SourceTerminalCLMTransport_comp, hinverse]
  exact cmp99SourceTerminalCLMTransport_id hs

/-- The regional middle operator, extended by zero to the common ambient
coarse block field used in the finite sum of (3.95). -/
noncomputable def generatedPhysicalCoarseCovarianceMiddleAmbient
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc) :=
  (extendZeroZeroCLM (D.operatorCoarseRegion hpi5 s)).comp
    ((D.generatedPhysicalCoarseCovarianceMiddleCoordinates hpi5 s hM depth
      hspacing background budget fineSmall hsmall).comp
      (restrictZeroCLM (D.operatorCoarseRegion hpi5 s)))

/-- The generated regional covariance, extended by zero to the same ambient
coarse block field. -/
noncomputable def generatedPhysicalCoarseCovarianceAmbient
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc) :=
  (extendZeroZeroCLM (D.operatorCoarseRegion hpi5 s)).comp
    ((D.generatedPhysicalCoarseCovarianceCoordinates hpi5 s hM depth
      hspacing background budget fineSmall hsmall).comp
      (restrictZeroCLM (D.operatorCoarseRegion hpi5 s)))

/-- Exact source-faithful ambient inverse identity.  The product of the two
zero-extended regional operators is the regional characteristic projector,
not the identity on the ambient torus. -/
theorem generatedPhysicalCoarseCovarianceMiddleAmbient_comp_covarianceAmbient
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    (D.generatedPhysicalCoarseCovarianceMiddleAmbient hpi5 s hM depth
      hspacing background budget fineSmall hsmall).comp
      (D.generatedPhysicalCoarseCovarianceAmbient hpi5 s hM depth
        hspacing background budget fineSmall hsmall) =
      (extendZeroZeroCLM (D.operatorCoarseRegion hpi5 s)).comp
        (restrictZeroCLM (D.operatorCoarseRegion hpi5 s)) := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let Middle := D.generatedPhysicalCoarseCovarianceMiddleCoordinates hpi5 s
    hM depth hspacing background budget fineSmall hsmall
  let C := D.generatedPhysicalCoarseCovarianceCoordinates hpi5 s hM depth
    hspacing background budget fineSmall hsmall
  have hlocal : Middle.comp C = ContinuousLinearMap.id ℝ _ :=
    D.generatedPhysicalCoarseCovarianceMiddleCoordinates_comp_covariance
      hpi5 s hM depth hspacing background budget fineSmall hsmall
  have hrext : (restrictZeroCLM (𝔤 := SUNLieCoord Nc) Omega).comp
      (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega) =
      ContinuousLinearMap.id ℝ (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :=
    activeGaugeRegion_restrictZero_comp_extendZero Omega
  apply ContinuousLinearMap.ext
  intro phi
  simp only [generatedPhysicalCoarseCovarianceMiddleAmbient,
    generatedPhysicalCoarseCovarianceAmbient, ContinuousLinearMap.comp_apply]
  have hrextApply := congrArg (fun T => T (C
    (restrictZeroCLM Omega phi))) hrext
  have hlocalApply := congrArg (fun T => T
    (restrictZeroCLM Omega phi)) hlocal
  change extendZeroZeroCLM Omega
      (Middle (restrictZeroCLM Omega
        (extendZeroZeroCLM Omega (C (restrictZeroCLM Omega phi))))) =
    extendZeroZeroCLM Omega (restrictZeroCLM Omega phi)
  rw [show restrictZeroCLM Omega
      (extendZeroZeroCLM Omega (C (restrictZeroCLM Omega phi))) =
      C (restrictZeroCLM Omega phi) by simpa using hrextApply]
  rw [show Middle (C (restrictZeroCLM Omega phi)) =
      restrictZeroCLM Omega phi by simpa using hlocalApply]

/-- At the physical source index `j`, the operator region is exactly
`tilde Pi^4`; hence the CMP95 smooth cutoff is unchanged by the regional
projector. -/
theorem cmp95SourcePeriodicCoarseSquarePartition_multiplier_comp_pi4RegionProjector
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile) :
    (finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
      (fun block : FinBox 4 (2 * Q) =>
        (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block)).comp
      ((extendZeroZeroCLM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j))).comp
        (restrictZeroCLM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)))) =
      finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
        (fun block : FinBox 4 (2 * Q) =>
          (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block) := by
  rw [activeGaugeRegion_extendZero_comp_restrict_eq_multiplier]
  have hregion :
      (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)).sites =
        cmp99SourceTildePiLargeBlocks cell 4 := by
    rw [D.operatorCoarseRegion_sites, D.fineRegion_pi4Index]
  rw [hregion]
  exact cmp95SourcePeriodicCoarseSquarePartition_multiplier_comp_pi4 P cell

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
