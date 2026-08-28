import YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanionZeroDepthGreen
import YangMills.RG.BalabanCMP99SourceSeparatedLargeBlockPartition

/-!
PRE-VALIDATION: scratch source only; no `.olean` has been materialized for
this file and no compiler or axiom-oracle verdict is claimed.

# Exact depth-zero Green on the source-separated carrier

This is the missing base branch of the unrestricted Eq. (3.42) family.  It
specializes the already constructed full-companion ambient precision and
canonical depth-zero Green directly to the source-separated carrier.  The
literal coefficient remains `spacing^(-2)` through the existing producer;
no precision, Green, equality or coercivity floor is caller data.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

variable (OmegaSource : ActiveGaugeRegion 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)))
variable (regions : CMP99SourceActiveRegionChain 4 L
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) OmegaSource 0)
variable (hL : 2 ≤ L)
variable {spacing epsilon : ℝ}
variable (background : GaugeConfig 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) (SUN Nc))
variable (chain : CMP99SourceUbarRadiusChain 4 L Nc 0 epsilon)
variable (fineSmall : ∀ e : ConcreteEdge 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)),
  ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)

/-- The literal depth-zero coercivity floor on the source carrier. -/
noncomputable def cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity : ℝ :=
  cmp99SourceActiveRegionFullCompanionCountingCoefficient regions (by
    norm_num) hL (matrixSUNAdjointModel Nc) spacing epsilon background chain
    fineSmall

/-- The internally generated full-companion ambient precision on the exact
source-separated carrier at depth zero. -/
noncomputable def cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q))
        (SUNLieCoord Nc) :=
  cmp99SourceActiveRegionFullCompanionAmbientPrecision regions (by
    norm_num) hL (matrixSUNAdjointModel Nc) spacing epsilon background chain
    fineSmall

/-- The source ambient precision has the literal positive depth-zero floor.
-/
theorem isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero :
    IsCoerciveCLM
      (cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
        (Nc := Nc) regions hL background chain fineSmall)
      (cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
        (Nc := Nc) regions hL background chain fineSmall) := by
  simpa [cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero,
    cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity] using
    (isCoerciveCLM_cmp99SourceActiveRegionFullCompanionAmbientPrecision_zero
      regions (by norm_num) hL background chain fineSmall)

/-- Exact Dirichlet compression of the one depth-zero ambient precision. -/
noncomputable def cmp99Eq360C6dSourceSeparatedDirichletPrecision_zero :
    ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) :=
  cmp99SourceActiveRegionFullCompanionDirichletPrecision_zero regions (by
    norm_num) hL spacing epsilon background chain fineSmall

/-- The Eq. (3.42) regional notation is exactly the generic depth-zero
Dirichlet compression on this carrier. -/
theorem cmp99Eq360C6dSourceSeparatedRegionalDirichletPrecision_eq_zero :
    cmp99RegionalDirichletPrecision
        (M := cmp99SourceSeparatedLargeBlockSide L K 0) (Q := Q)
        OmegaSource
        (cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
          (Nc := Nc) regions hL background chain fineSmall) =
      cmp99Eq360C6dSourceSeparatedDirichletPrecision_zero
        (Nc := Nc) regions hL background chain fineSmall := by
  rfl

/-- Canonical depth-zero Green on the exact source-separated region. -/
noncomputable def cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
    (hspacing : 0 < spacing) :
    ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) :=
  cmp99SourceActiveRegionFullCompanionDirichletGreen_zero regions (by
    norm_num) hL hspacing background chain fineSmall

/-- The regional-Green spelling fixed by Eq. (3.42) is the same internally
generated base Green. -/
theorem cmp99Eq360C6dSourceSeparatedRegionalDirichletGreen_eq_zero
    (hspacing : 0 < spacing) :
    cmp99RegionalDirichletGreen
        (M := cmp99SourceSeparatedLargeBlockSide L K 0) (Q := Q)
        OmegaSource
        (cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
          (Nc := Nc) regions hL background chain fineSmall)
        (cmp99SourceActiveRegionFullCompanionCountingCoefficient_pos_zero
          regions (by norm_num) hL hspacing background chain fineSmall)
        (isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
          (Nc := Nc) regions hL background chain fineSmall) =
      cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
        (Nc := Nc) regions hL hspacing background chain fineSmall := by
  rfl

/-- The exact base precision is a left inverse of the base Green. -/
theorem cmp99Eq360C6dSourceSeparatedDirichletPrecision_comp_green_zero
    (hspacing : 0 < spacing) :
    (cmp99Eq360C6dSourceSeparatedDirichletPrecision_zero
      (Nc := Nc) regions hL background chain fineSmall).comp
      (cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
        (Nc := Nc) regions hL hspacing background chain fineSmall) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc)) := by
  exact
    cmp99SourceActiveRegionFullCompanionDirichletPrecision_comp_green_zero
      regions (by norm_num) hL hspacing background chain fineSmall

/-- The exact base Green is a left inverse of the base precision. -/
theorem cmp99Eq360C6dSourceSeparatedAmbientGreen_comp_precision_zero
    (hspacing : 0 < spacing) :
    (cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
      (Nc := Nc) regions hL hspacing background chain fineSmall).comp
      (cmp99Eq360C6dSourceSeparatedDirichletPrecision_zero
        (Nc := Nc) regions hL background chain fineSmall) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc)) := by
  exact
    cmp99SourceActiveRegionFullCompanionDirichletGreen_comp_precision_zero
      regions (by norm_num) hL hspacing background chain fineSmall

/-- The base Green inherits the inverse-floor operator-norm bound. -/
theorem norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_le
    (hspacing : 0 < spacing) :
    ‖cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
      (Nc := Nc) regions hL hspacing background chain fineSmall‖ ≤
      (cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
        (Nc := Nc) regions hL background chain fineSmall)⁻¹ := by
  exact norm_cmp99SourceActiveRegionFullCompanionDirichletGreen_zero_le
    regions (by norm_num) hL hspacing background chain fineSmall

end

end YangMills.RG
