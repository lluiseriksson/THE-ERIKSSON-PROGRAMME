/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0
import YangMills.RG.FinitePiLpBlockLocalizedSup

/-!
# Localized coarse-field bound for the literal source-flow Green

PRE-VALIDATION: source is present, but its `.olean` has not been materialized
and no result in this file has yet been compiler-verified.

C6a controls one coarse point source.  On the coarse source carrier the owner
map is the identity, so an arbitrary field supported in one owner fibre is
definitionally supported at one point.  This file proves that reduction
inside the physical theorem and upgrades C6a to the literal localized-field
sup-norm quantifier without a source-cardinality factor.

The conclusion still concerns the ambient complex operator `G Q'^*`.  It is
not the canonical real regional Dirichlet Green and supplies none of its three
derivative actions.  Thus it is C6b, not the regional (3.42) certificate,
window-15 attainment or a terminal field.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The literal C6a coefficient controls an arbitrary coarse field supported
at one source owner, measured in the existing finite supremum norm.  No
owner-fibre cardinality appears because the source-owner map is the identity. -/
theorem
    norm_cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_localizedField_apply_siteEquiv_le_pointSourceB0
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (owner : FinBox 4 (2 * (K * Q)))
    (f : FinitePiLpField (FinBox 4 (2 * (K * Q)))
      (SUNLieComplexCoord Nc))
    (hf : FinitePiLpSupportedInOwner (fun y => y) owner f)
    (target : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceFlowFlatFullComplexA a L depth) rho) :
    ‖(((cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1))
          (N' := 2 * (K * Q)) (Nc := Nc)))
        (WithLp.ofLp f))
          (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth target)‖ ≤
      cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0
          a L depth rho *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth target)
            owner : ℝ)) * finitePiLpSupNorm f := by
  have hfpoint :
      WithLp.ofLp f =
        cmp99FlatComplexFibrePointSource owner (f owner) := by
    funext source
    by_cases hsource : source = owner
    · subst source
      simp [cmp99FlatComplexFibrePointSource]
    · have hz : f source = 0 := hf source hsource
      simp [cmp99FlatComplexFibrePointSource, hsource, hz]
  rw [hfpoint]
  have hpoint :=
    norm_cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_pointSource_apply_siteEquiv_le_pointSourceB0
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth ha owner (f owner) target
      hrho hamplitude hradius hwindow
  have hB0 :=
    cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0_nonneg
      (L := L) depth ha hrho hamplitude hradius hwindow
  have hcoefficient :
      0 ≤ cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0
          a L depth rho *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth target)
            owner : ℝ)) :=
    mul_nonneg hB0 (Real.exp_pos _).le
  exact hpoint.trans (mul_le_mul_of_nonneg_left
    (norm_apply_le_finitePiLpSupNorm f owner) hcoefficient)

/-- The same localized-field estimate with the single point-source
coefficient evaluated at the CMP85 floor.  The depth-specific strip window
is derived internally from the floor window. -/
theorem
    norm_cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_localizedField_apply_siteEquiv_le_uniformPointSourceB0
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (owner : FinBox 4 (2 * (K * Q)))
    (f : FinitePiLpField (FinBox 4 (2 * (K * Q)))
      (SUNLieComplexCoord Nc))
    (hf : FinitePiLpSupportedInOwner (fun y => y) owner f)
    (target : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hfloorWindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) rho) :
    ‖(((cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1))
          (N' := 2 * (K * Q)) (Nc := Nc)))
        (WithLp.ofLp f))
          (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth target)‖ ≤
      cmp99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0
          a L rho *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth target)
            owner : ℝ)) * finitePiLpSupNorm f := by
  have hLnat : 1 < L := lt_of_lt_of_le (by omega) hL
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hLnat
  have hfloor :
      0 < cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ) :=
    cmp85Eq215SourceAveragingCoefficientFloor_pos ha hLreal
  have hfloorLe :
      cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ) ≤
        cmp99SourceMassParameter a (L : ℝ) depth :=
    cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter
      ha hLreal depth
  have hdepthWindow :
      CMP89Eq249CentralStabilizedComplexWindow
        (cmp99SourceFlowFlatFullComplexA a L depth) rho := by
    rw [cmp99SourceFlowFlatFullComplexA]
    exact CMP89Eq249CentralStabilizedComplexWindow_mono
      hfloor hfloorLe hrho.le hfloorWindow
  have hfixed :=
    norm_cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_localizedField_apply_siteEquiv_le_pointSourceB0
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth ha owner f hf target hrho hamplitude hradius hdepthWindow
  have hB0 :=
    cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0_le_uniform
      ha hL depth hrho hfloorWindow
  exact hfixed.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hB0 (Real.exp_pos _).le)
      (finitePiLpSupNorm_nonneg f))

end

end YangMills.RG
