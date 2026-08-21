/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceB0
import YangMills.RG.FinitePiLpBlockLocalizedSup

/-!
# Localized coarse-field bound for the separated generated Green

PRE-VALIDATION: source present, `.olean` not yet materialized, and results in
this module are not yet compiler-verified.

C6a controls one coarse point source.  On the coarse source carrier the owner
map is the identity, so an arbitrary field supported in one owner fibre is
definitionally supported at one point.  This file proves that reduction and
upgrades C6a to the literal localized-field/sup-norm quantifier without a
source-cardinality factor.

The conclusion still concerns the ambient complex operator `G Q'^*`.  It is
not the canonical real regional Dirichlet Green and supplies none of its
three derivative actions.  Thus it is C6b, not the regional (3.42)
certificate, window-15 attainment or a terminal field.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- A coarse field supported in one identity-owner fibre is the literal point
source carrying its value at that owner. -/
theorem finitePiLp_of_supportedInIdentityOwner_eq_flatComplexFibrePointSource
    (owner : FinBox 4 (2 * (K * Q)))
    (f : FinitePiLpField (FinBox 4 (2 * (K * Q)))
      (SUNLieComplexCoord Nc))
    (hf : FinitePiLpSupportedInOwner (fun y => y) owner f) :
    WithLp.ofLp f = cmp99FlatComplexFibrePointSource owner (f owner) := by
  funext source
  by_cases hsource : source = owner
  · subst source
    simp [cmp99FlatComplexFibrePointSource]
  · have hz : f source = 0 := hf source hsource
    simp [cmp99FlatComplexFibrePointSource, hsource, hz]

/-- The C6a coefficient controls an arbitrary coarse field supported at one
source owner, measured in the existing finite supremum norm.  No owner-fibre
cardinality appears because the source-owner map is literally the identity. -/
theorem
    norm_cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_localizedField_apply_siteEquiv_le_pointSourceB0
    (hL : 2 ≤ L) (depth : ℕ)
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
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho) :
    ‖(((cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1))
          (N' := 2 * (K * Q)) (Nc := Nc)))
        (WithLp.ofLp f))
          (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth target)‖ ≤
      cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceB0 L depth rho *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth target)
            owner : ℝ)) * finitePiLpSupNorm f := by
  have hfpoint :=
    finitePiLp_of_supportedInIdentityOwner_eq_flatComplexFibrePointSource
      owner f hf
  rw [hfpoint]
  have hpoint :=
    norm_cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_apply_siteEquiv_le_pointSourceB0
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth owner (f owner) target hrho hamplitude hradius hwindow
  have hB0 :=
    cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceB0_nonneg
      (L := L) depth hrho hamplitude hradius hwindow
  have hcoefficient :
      0 ≤ cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceB0 L depth rho *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth target)
            owner : ℝ)) :=
    mul_nonneg hB0 (Real.exp_pos _).le
  exact hpoint.trans (mul_le_mul_of_nonneg_left
    (norm_apply_le_finitePiLpSupNorm f owner) hcoefficient)

end

end YangMills.RG
