/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395PhysicalFamily
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCHeadFactor

/-!
# The exact head dictionary for CMP99 equation (3.95)

The literal source summand in (3.95) is the ambient operator

`h_Pi C_Pi h_Pi`.

The Section C estimates already apply to the regional head with the same
CMP95 cutoff.  This file proves that the two objects are exactly related by
zero extension and restriction.  Thus the exhaustive (3.95) word expansion
can consume the existing local support and weighted-row results without a
new head hypothesis or a condition-number loss.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

/-- A scalar multiplier commutes exactly with extension by zero after its
symbol is restricted to the regional carrier. -/
theorem finitePiLpScalarMultiplier_comp_extendZeroZeroCLM
    {d N : ℕ} [NeZero N] {g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) (f : FinBox d N → ℝ) :
    (finitePiLpScalarMultiplier (g := g) f).comp
        (extendZeroZeroCLM (𝔤 := g) Omega) =
      (extendZeroZeroCLM (𝔤 := g) Omega).comp
        (finitePiLpScalarMultiplier (g := g)
          (fun x : ActiveGaugeRegion.Site Omega => f x.1)) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  by_cases hx : x ∈ Omega.sites <;>
    simp [ContinuousLinearMap.comp_apply, finitePiLpScalarMultiplier_apply,
      extendZeroZeroCLM, hx]

/-- Restriction after an ambient scalar multiplier is exactly the regional
multiplier after restriction. -/
theorem restrictZeroCLM_comp_finitePiLpScalarMultiplier
    {d N : ℕ} [NeZero N] {g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) (f : FinBox d N → ℝ) :
    (restrictZeroCLM (𝔤 := g) Omega).comp
        (finitePiLpScalarMultiplier (g := g) f) =
      (finitePiLpScalarMultiplier (g := g)
        (fun x : ActiveGaugeRegion.Site Omega => f x.1)).comp
        (restrictZeroCLM (𝔤 := g) Omega) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  simp [ContinuousLinearMap.comp_apply, finitePiLpScalarMultiplier_apply,
    restrictZeroCLM]

/-- Zero extension is contractive as an operator (in fact it is an
isometry). -/
theorem norm_extendZeroZeroCLM_operator_le_one
    {d N : ℕ} [NeZero N] {g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) :
    ‖extendZeroZeroCLM (𝔤 := g) Omega‖ ≤ 1 := by
  exact opNorm_le_one_of_norm_map_eq _ (norm_extendZeroZeroCLM_eq Omega)

/-- Regional restriction is contractive as the adjoint of the isometric
zero extension. -/
theorem norm_restrictZeroCLM_operator_le_one
    {d N : ℕ} [NeZero N] {g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) :
    ‖restrictZeroCLM (𝔤 := g) Omega‖ ≤ 1 := by
  rw [cmp99ActiveRegion_restrictZero_eq_extendZero_adjoint]
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact norm_extendZeroZeroCLM_operator_le_one Omega

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- One literal ambient head `h_Pi C_Pi h_Pi` from the patched covariance
sum in (3.95). -/
noncomputable def cmp99Eq395PhysicalHead
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
    (cell : FinBox 4 Q) : CMP99Eq395AmbientOperator Q Nc :=
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  h * C * h

/-- Exact source dictionary: the ambient head in (3.95) is the zero extension
of the already generated CMP95 Section C head, followed by restriction.
No estimate and no new physical hypothesis is used. -/
theorem cmp99Eq395PhysicalHead_eq_extend_localHead_restrict
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
    (cell : FinBox 4 Q) :
    cmp99Eq395PhysicalHead D hpi5 P hM depth hspacing background budget
        fineSmall hsmall cell =
      (extendZeroZeroCLM
        ((D cell).operatorCoarseRegion (hpi5 cell) (cmp99OmegaPi4Index j))).comp
        (((D cell).generatedCMP95SectionCSourceHeadFactorCoordinates P
          (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background
          budget fineSmall hsmall).comp
        (restrictZeroCLM
          ((D cell).operatorCoarseRegion (hpi5 cell)
            (cmp99OmegaPi4Index j)))) := by
  let Omega := (D cell).operatorCoarseRegion (hpi5 cell) (cmp99OmegaPi4Index j)
  let Hambient := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  let Hlocal := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site Omega =>
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell x.1)
  let C := (D cell).generatedPhysicalCoarseCovarianceCoordinates
    (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background budget
    fineSmall hsmall
  let E := extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  let R := restrictZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  have hHE : Hambient.comp E = E.comp Hlocal := by
    simpa [Hambient, Hlocal, cmp99Eq395PhysicalSmoothMultiplier] using
      finitePiLpScalarMultiplier_comp_extendZeroZeroCLM
        (g := SUNLieCoord Nc) Omega
        (fun block : FinBox 4 (2 * Q) =>
          (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block)
  have hRH : R.comp Hambient = Hlocal.comp R := by
    simpa [Hambient, Hlocal, cmp99Eq395PhysicalSmoothMultiplier] using
      restrictZeroCLM_comp_finitePiLpScalarMultiplier
        (g := SUNLieCoord Nc) Omega
        (fun block : FinBox 4 (2 * Q) =>
          (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block)
  change Hambient.comp ((E.comp (C.comp R)).comp Hambient) =
    E.comp ((Hlocal.comp (C.comp Hlocal)).comp R)
  calc
    _ = Hambient.comp (E.comp ((C.comp R).comp Hambient)) := by
      rw [← ContinuousLinearMap.comp_assoc E (C.comp R) Hambient]
    _ = (Hambient.comp E).comp ((C.comp R).comp Hambient) :=
      (ContinuousLinearMap.comp_assoc _ _ _).symm
    _ = (E.comp Hlocal).comp ((C.comp R).comp Hambient) := by rw [hHE]
    _ = E.comp (Hlocal.comp ((C.comp R).comp Hambient)) :=
      ContinuousLinearMap.comp_assoc _ _ _
    _ = E.comp (Hlocal.comp (C.comp (R.comp Hambient))) := by
      rw [ContinuousLinearMap.comp_assoc C R Hambient]
    _ = E.comp (Hlocal.comp (C.comp (Hlocal.comp R))) := by rw [hRH]
    _ = E.comp ((Hlocal.comp (C.comp Hlocal)).comp R) := by
      simp only [ContinuousLinearMap.comp_assoc]

/-- Transporting the local head to the ambient torus introduces no operator
norm loss. -/
theorem norm_cmp99Eq395PhysicalHead_le_localHead
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
    (cell : FinBox 4 Q) :
    ‖cmp99Eq395PhysicalHead D hpi5 P hM depth hspacing background budget
        fineSmall hsmall cell‖ ≤
      ‖(D cell).generatedCMP95SectionCSourceHeadFactorCoordinates P
        (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background
        budget fineSmall hsmall‖ := by
  let Omega := (D cell).operatorCoarseRegion (hpi5 cell) (cmp99OmegaPi4Index j)
  let E := extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  let R := restrictZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  let F := (D cell).generatedCMP95SectionCSourceHeadFactorCoordinates P
    (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background budget
    fineSmall hsmall
  rw [cmp99Eq395PhysicalHead_eq_extend_localHead_restrict]
  have hE : ‖E‖ ≤ 1 := norm_extendZeroZeroCLM_operator_le_one Omega
  have hR : ‖R‖ ≤ 1 := norm_restrictZeroCLM_operator_le_one Omega
  have hFR : ‖F.comp R‖ ≤ ‖F‖ := by
    calc
      ‖F.comp R‖ ≤ ‖F‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hR (norm_nonneg F)
      _ = ‖F‖ := mul_one _
  calc
    ‖E.comp (F.comp R)‖ ≤ ‖E‖ * ‖F.comp R‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖F‖ := mul_le_mul hE hFR (norm_nonneg _) zero_le_one
    _ = ‖F‖ := one_mul _

/-- Volume-independent norm bound for the literal ambient head, inherited
from the generated regional covariance with no transport loss. -/
theorem norm_cmp99Eq395PhysicalHead_le
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
    (cell : FinBox 4 Q) :
    ‖cmp99Eq395PhysicalHead D hpi5 P hM depth hspacing background budget
        fineSmall hsmall cell‖ ≤
      cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
        M depth spacing epsilon := by
  refine (norm_cmp99Eq395PhysicalHead_le_localHead D hpi5 P hM depth
    hspacing background budget fineSmall hsmall cell).trans ?_
  exact (D cell).norm_generatedSectionCSourceHeadFactorCoordinates_le
    (cmp95SourcePeriodicCoarseSquarePartition P Q) (hpi5 cell)
      (cmp99OmegaPi4Index j) hM depth hspacing background budget fineSmall
        hsmall

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
