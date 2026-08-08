/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395LocalInverse

/-!
# The physical finite source family in CMP99 equation (3.95)

This file puts every source cell on one ambient coarse block field.  The
smooth CMP95 partition, the literal source characteristic, the physical
`Omega_j = tilde Pi^4` projector, and the generated regional middle and
covariance operators are all explicit functions of the cell.  The local
resolution in (3.95) is then derived from the zero-extended projected inverse
identity; it is not supplied as a hypothesis.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

/-- Common ambient operator ring for the finite source sum in (3.95). -/
abbrev CMP99Eq395AmbientOperator (Q Nc : ℕ) [NeZero Q] [NeZero Nc] :=
  GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc) →L[ℝ]
    GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc)

/-- Literal smooth source multiplier `h_Pi`. -/
noncomputable def cmp99Eq395PhysicalSmoothMultiplier
    {Q Nc : ℕ} [NeZero Q] [NeZero Nc]
    (P : CMP95SourceSmoothPartitionProfile) (cell : FinBox 4 Q) :
    CMP99Eq395AmbientOperator Q Nc :=
  finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun block : FinBox 4 (2 * Q) =>
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block)

/-- Literal source-cell characteristic `chi_Pi`. -/
noncomputable def cmp99Eq395PhysicalSourceCharacteristic
    {Q Nc : ℕ} [NeZero Q] [NeZero Nc] (cell : FinBox 4 Q) :
    CMP99Eq395AmbientOperator Q Nc :=
  finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun block : FinBox 4 (2 * Q) =>
      cmp99SourcePiCharacteristic cell block)

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- Regional characteristic projector for the physical source index
`Omega_j = tilde Pi^4`, realized on the ambient coarse field. -/
noncomputable def cmp99Eq395PhysicalRegionProjector
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (cell : FinBox 4 Q) : CMP99Eq395AmbientOperator Q Nc :=
  (extendZeroZeroCLM
    ((D cell).operatorCoarseRegion (hpi5 cell) (cmp99OmegaPi4Index j))).comp
    (restrictZeroCLM
      ((D cell).operatorCoarseRegion (hpi5 cell) (cmp99OmegaPi4Index j)))

/-- Generated physical middle `Q' (G')² Q'^*`, zero-extended to the ambient
coarse field for one source cell. -/
noncomputable def cmp99Eq395PhysicalMiddle
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) : CMP99Eq395AmbientOperator Q Nc :=
  (D cell).generatedPhysicalCoarseCovarianceMiddleAmbient (hpi5 cell)
    (cmp99OmegaPi4Index j) hM depth hspacing background budget fineSmall hsmall

/-- Generated physical regional covariance, zero-extended to the same
ambient coarse field. -/
noncomputable def cmp99Eq395PhysicalCovariance
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) : CMP99Eq395AmbientOperator Q Nc :=
  (D cell).generatedPhysicalCoarseCovarianceAmbient (hpi5 cell)
    (cmp99OmegaPi4Index j) hM depth hspacing background budget fineSmall hsmall

/-- The full ambient coarse region used by the global middle operator in
(3.95). -/
noncomputable def cmp99Eq395FullCoarseRegion {Q : ℕ} [NeZero Q] :
    ActiveGaugeRegion 4 (2 * Q) :=
  ActiveGaugeRegion.mk Finset.univ

/-- Literal global middle `A = Q' G'^2 Q'^*`, transported from the generated
terminal tower over the full coarse torus and realized on the ambient block
field. -/
noncomputable def cmp99Eq395PhysicalGlobalMiddle
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) : CMP99Eq395AmbientOperator Q Nc := by
  let Omega := cmp99Eq395FullCoarseRegion (Q := Q)
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  have hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    Omega (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  let MiddleCoordinates := cmp99SourceTerminalCLMTransport hs hs Middle
  exact (extendZeroZeroCLM Omega).comp
    (MiddleCoordinates.comp (restrictZeroCLM Omega))

/-- Fully physical finite-family form of CMP99 (3.95), with the global
covariance represented by its literal smooth regional sum.  The only free
operator is the displayed global middle `A`; every local inverse, source
characteristic, region projector, and square-partition identity is produced
internally. -/
theorem cmp99Eq395_physical_source_family
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (A : CMP99Eq395AmbientOperator Q Nc) :
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P
    let chi := cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc)
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall
    let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
      budget fineSmall hsmall
    A * (∑ cell : FinBox 4 Q, h cell * C cell * h cell) =
      1 - cmp99Eq395R Finset.univ A AD chi h C := by
  dsimp only
  apply cmp99Eq395_eq_one_sub_R_of_projected_local_inverses
    (domains := (Finset.univ : Finset (FinBox 4 Q)))
    (A := A)
    (C0 := ∑ cell : FinBox 4 Q,
      cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell *
        cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
          budget fineSmall hsmall cell *
        cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell)
    (AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall)
    (chi := cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc))
    (proj := cmp99Eq395PhysicalRegionProjector (Nc := Nc) D hpi5)
    (h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P)
    (C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
      budget fineSmall hsmall)
  · rfl
  · intro cell _hcell
    simpa [cmp99Eq395PhysicalSmoothMultiplier,
      cmp99Eq395PhysicalSourceCharacteristic] using
      (cmp95SourcePeriodicCoarseSquarePartition_multiplier_comp_characteristic
        (g := SUNLieCoord Nc) P cell (fun block => block))
  · intro cell _hcell
    simpa [cmp99Eq395PhysicalSmoothMultiplier,
      cmp99Eq395PhysicalRegionProjector] using
      ((D cell).cmp95SourcePeriodicCoarseSquarePartition_multiplier_comp_pi4RegionProjector
        (hpi5 cell) (Nc := Nc) P)
  · intro cell _hcell
    simpa [cmp99Eq395PhysicalMiddle, cmp99Eq395PhysicalCovariance,
      cmp99Eq395PhysicalRegionProjector] using
      ((D cell).generatedPhysicalCoarseCovarianceMiddleAmbient_comp_covarianceAmbient
        (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background
        budget fineSmall hsmall)
  · simpa [cmp99Eq395PhysicalSmoothMultiplier] using
      (sum_cmp99SourceSquarePartition_multiplier_sq_eq_id
        (g := SUNLieCoord Nc)
        (cmp95SourcePeriodicCoarseSquarePartition P Q)
        (fun block : FinBox 4 (2 * Q) => block))

/-- Fully instantiated physical equation (3.95).  The global middle is the
generated `Q' G'^2 Q'^*` on the full coarse torus, while all regional
covariances and correction factors come from the source-cell family. -/
theorem cmp99Eq395_physical_global_middle_source_family
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P
    let chi := cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc)
    let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
      budget fineSmall hsmall
    let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
      budget fineSmall hsmall
    A * (∑ cell : FinBox 4 Q, h cell * C cell * h cell) =
      1 - cmp99Eq395R Finset.univ A AD chi h C := by
  exact cmp99Eq395_physical_source_family D hpi5 P hM depth hspacing
    background budget fineSmall hsmall
    (cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
      fineSmall hsmall)

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
