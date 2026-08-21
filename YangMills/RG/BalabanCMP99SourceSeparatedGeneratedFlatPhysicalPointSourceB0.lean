/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalSourceOwnerBound

/-!
# Ambient point-source coefficient for the separated generated Green

PRE-VALIDATION: source present, `.olean` not yet materialized, and results in
this module are not yet compiler-verified.

C5 leaves the complete coefficient visible in front of the literal CMP99
source-owner decay.  This file names that coefficient and restates the C5
column estimate with it.  The coefficient still depends explicitly on
`depth` through the generated physical `a`; no uniform-in-depth bound is
asserted here.

The name deliberately says `PointSourceB0`, not regional `B0`.  This is a
bound for the ambient complex operator `G Q'^*` on one coarse point source.
It does not provide the arbitrary localized-field quantifier, identify the
canonical real regional Dirichlet Green, supply its three derivative actions,
attain window 15 or discharge a terminal field.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Exact coefficient already displayed by the separated Unit-F owner bound.
At fixed `L`, `depth` and `rho`, it is uniform in the independent large-block
parameter `K`, the owner period `Q` and the target/source sites. -/
def cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceB0
    (L depth : ℕ) (rho : ℝ) : ℝ :=
  cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho *
    (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho)

/-- The explicit point-source coefficient is nonnegative on the same physical
strip window used to construct the C5 estimate. -/
theorem cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceB0_nonneg
    (depth : ℕ) {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho) :
    0 ≤ cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceB0 L depth rho := by
  let Kfine : ℕ := L ^ (depth + 1)
  let a : ℝ :=
    cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0
  letI : NeZero Kfine := by
    dsimp [Kfine]
    infer_instance
  have hA : 0 ≤ cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho := by
    have hpoint :=
      norm_cmp89Eq248PhysicalZeroMassGreen_le_signedLatticeWeight_draft
        (K := Kfine)
        (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
        hrho.le hamplitude hradius hwindow 0
    simpa using (le_trans (norm_nonneg _) hpoint)
  have hgeom : 0 ≤ (2 / (1 - Real.exp (-rho))) ^ 4 := by positivity
  rw [cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceB0]
  exact mul_nonneg (mul_nonneg hA hgeom) (Real.exp_pos _).le

/-- C5 in the exact named-coefficient normal form. -/
theorem
    norm_cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_apply_siteEquiv_le_pointSourceB0
    (hL : 2 ≤ L) (depth : ℕ)
    (y : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
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
        (cmp99FlatComplexFibrePointSource y v))
          (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth target)‖ ≤
      cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceB0 L depth rho *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth target)
            y : ℝ)) * ‖v‖ := by
  simpa [cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceB0,
    mul_assoc] using
    (norm_cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_apply_siteEquiv_le_sourceOwner
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth y v target hrho hamplitude hradius hwindow)

end

end YangMills.RG
