/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCCommutatorFactor
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCRightFactorNorm

/-!
# The basic generated CMP99 Section C factor

CMP99 printed p. 409, equation (3.88), defines

`K(h) = h Delta' - Delta' h`,

and printed p. 412 lists `K(h'_Pi) G'_Pi h'_Pi` as the basic factor of the
generalized random-walk expansion.  This file constructs that operator on the
literal fine terminal carrier of the generated source tower.  It is not
identified with the rectangular consecutive-region precision defect, and it
is not padded into the coarse-only typed walk: CMP99 printed p. 413 explicitly
notes that Section C factors may act between different scales.

The volume-independent bound proved here is the direct operator bound.  The
sharper `O(M^-1)` estimate (3.89) additionally uses the derivative estimates
of the smooth partition from Sect. A of the preceding propagator paper; that
source input is not replaced here by an arbitrary commutator hypothesis.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/-- Direct volume-independent norm budget for the basic factor.  The missing
source-small `M^-1` gain is deliberately not asserted here. -/
noncomputable def cmp99SourceGeneratedPhysicalFineBasicFactorNormBound
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  2 * cmp99SourceGeneratedPhysicalPrecisionUpperBound
      4 M (depth + 1) spacing epsilon *
    (1 / cmp99SourceGeneratedCoercivity
      4 M (depth + 1) spacing epsilon)

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 3000000

/-- Literal `K(h'_Pi) = h'_Pi Delta' - Delta' h'_Pi` from (3.88), on the
fine terminal field over one generated regional tower. -/
noncomputable def generatedPhysicalFineSectionCPrecisionCommutator
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :=
  let Omega := D.operatorCoarseRegion hpi5 s
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (cmp99SourceGeneratedFinePartitionCutoff (M := M) P cell Omega depth)
  let Precision := cmp99SourceGeneratedPhysicalPrecision
    (show 2 ≤ 4 by norm_num) hM Omega depth spacing epsilon background budget
      fineSmall
  H.comp Precision - Precision.comp H

/-- The exact basic factor `K(h'_Pi) G'_Pi h'_Pi` printed on p. 412. -/
noncomputable def generatedPhysicalFineSectionCBasicFactor
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
      spacing epsilon < 1) :=
  let Omega := D.operatorCoarseRegion hpi5 s
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (cmp99SourceGeneratedFinePartitionCutoff (M := M) P cell Omega depth)
  let K := D.generatedPhysicalFineSectionCPrecisionCommutator P hpi5 s hM
    depth spacing epsilon background budget fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    Omega depth hspacing background budget fineSmall hsmall
  K.comp (G.comp H)

/-- The basic factor unfolds to the exact source commutator, Green operator,
and right partition cutoff; this is the literal (3.88) -> p. 412 dictionary. -/
theorem generatedPhysicalFineSectionCBasicFactor_eq_source
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
    D.generatedPhysicalFineSectionCBasicFactor P hpi5 s hM depth hspacing
        background budget fineSmall hsmall =
      (D.generatedPhysicalFineSectionCPrecisionCommutator P hpi5 s hM depth
        spacing epsilon background budget fineSmall).comp
      ((cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
        (D.operatorCoarseRegion hpi5 s) depth hspacing background budget
        fineSmall hsmall).comp
      (finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
        (cmp99SourceGeneratedFinePartitionCutoff (M := M) P cell
          (D.operatorCoarseRegion hpi5 s) depth))) := rfl

/-- Direct volume-independent norm control of the literal basic factor. -/
theorem norm_generatedPhysicalFineSectionCBasicFactor_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
    ‖D.generatedPhysicalFineSectionCBasicFactor P hpi5 s hM depth hspacing
      background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalFineBasicFactorNormBound
        M depth spacing epsilon := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let H := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (cmp99SourceGeneratedFinePartitionCutoff (M := M) P cell Omega depth)
  let Precision := cmp99SourceGeneratedPhysicalPrecision
    (show 2 ≤ 4 by norm_num) hM Omega depth spacing epsilon background budget
      fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    Omega depth hspacing background budget fineSmall hsmall
  let A := cmp99SourceGeneratedPhysicalPrecisionUpperBound
    4 M (depth + 1) spacing epsilon
  let c := cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon
  have hA : 0 ≤ A :=
    (cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos
      4 M (depth + 1) hspacing).le
  have hc : 0 < c :=
    cmp99SourceGeneratedCoercivity_pos 4 M depth hspacing hsmall
  have hH : ‖H‖ ≤ 1 :=
    norm_finitePiLpScalarMultiplier_le_one _
      (norm_cmp99SourceGeneratedFinePartitionCutoff_le_one
        (M := M) P cell Omega depth)
  have hPrecision : ‖Precision‖ ≤ A := by
    simpa [Precision, A] using
      norm_cmp99SourceGeneratedPhysicalPrecision_le
        (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall
  have hG : ‖G‖ ≤ 1 / c := by
    simpa [G, c] using norm_covarianceOfIsCoerciveCLM_le
      (cmp99SourceGeneratedPhysicalPrecision (show 2 ≤ 4 by norm_num) hM
        Omega depth spacing epsilon background budget fineSmall)
      hc
      (isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision
        (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall hsmall)
  have hHP : ‖H.comp Precision‖ ≤ A := by
    calc
      ‖H.comp Precision‖ ≤ ‖H‖ * ‖Precision‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * A := mul_le_mul hH hPrecision (norm_nonneg Precision)
        zero_le_one
      _ = A := one_mul A
  have hPH : ‖Precision.comp H‖ ≤ A := by
    calc
      ‖Precision.comp H‖ ≤ ‖Precision‖ * ‖H‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ A * 1 := mul_le_mul hPrecision hH (norm_nonneg H) hA
      _ = A := mul_one A
  have hK : ‖H.comp Precision - Precision.comp H‖ ≤ 2 * A := by
    calc
      ‖H.comp Precision - Precision.comp H‖ ≤
          ‖H.comp Precision‖ + ‖Precision.comp H‖ := norm_sub_le _ _
      _ ≤ A + A := add_le_add hHP hPH
      _ = 2 * A := by ring
  have hGH : ‖G.comp H‖ ≤ 1 / c := by
    calc
      ‖G.comp H‖ ≤ ‖G‖ * ‖H‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 / c) * 1 :=
        mul_le_mul hG hH (norm_nonneg H) (by positivity)
      _ = 1 / c := mul_one _
  unfold generatedPhysicalFineSectionCBasicFactor
    generatedPhysicalFineSectionCPrecisionCommutator
    cmp99SourceGeneratedPhysicalFineBasicFactorNormBound
  change ‖(H.comp Precision - Precision.comp H).comp (G.comp H)‖ ≤
    2 * A * (1 / c)
  calc
    ‖(H.comp Precision - Precision.comp H).comp (G.comp H)‖ ≤
        ‖H.comp Precision - Precision.comp H‖ * ‖G.comp H‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (2 * A) * (1 / c) :=
      mul_le_mul hK hGH (norm_nonneg _) (mul_nonneg (by norm_num) hA)
    _ = 2 * A * (1 / c) := by ring

/-- The exact basic factor packaged with the proved direct norm bound. -/
noncomputable def generatedPhysicalFineSectionCBasicFactorCertificate
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
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
    CMP99SectionCTypedEndomorphismWithNorm
      (ActiveGaugeRegion.Site (cmp99IteratedLiftActiveRegion (M := M)
        (D.operatorCoarseRegion hpi5 s) (depth + 1)))
      (SUNLieCoord Nc)
      (cmp99SourceGeneratedPhysicalFineBasicFactorNormBound
        M depth spacing epsilon) where
  operator := D.generatedPhysicalFineSectionCBasicFactor P hpi5 s hM depth
    hspacing background budget fineSmall hsmall
  norm_le := D.norm_generatedPhysicalFineSectionCBasicFactor_le P hpi5 s hM
    depth hspacing background budget fineSmall hsmall

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
