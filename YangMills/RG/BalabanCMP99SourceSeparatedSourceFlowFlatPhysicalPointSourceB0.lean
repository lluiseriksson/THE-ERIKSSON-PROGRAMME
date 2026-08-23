/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalSourceOwnerBound

/-!
# Ambient point-source coefficient for the literal source-flow Green

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

C5 leaves the complete source-flow coefficient visible in front of the CMP99
source-owner decay.  This file names that coefficient and restates the C5
column estimate with it.  Its dependence on the physical source mass `a`,
`L`, `depth` and the strip radius `rho` remains explicit; no uniform-in-depth
bound is asserted here.

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

/-- Exact coefficient displayed by the literal source-flow Unit-F owner
bound.  At fixed `a`, `L`, `depth` and `rho`, it is uniform in the independent
large-block parameter `K`, the owner period `Q` and the target/source sites. -/
def cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0
    (a : ℝ) (L depth : ℕ) (rho : ℝ) : ℝ :=
  cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
      (cmp99SourceFlowFlatFullComplexA a L depth) rho *
    (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho)

/-- The explicit source-flow point-source coefficient is nonnegative on the
same physical strip window used to construct the C5 estimate. -/
theorem cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0_nonneg
    (depth : ℕ) {a rho : ℝ} (ha : 0 < a)
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceFlowFlatFullComplexA a L depth) rho) :
    0 ≤ cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0
      a L depth rho := by
  let Kfine : ℕ := L ^ (depth + 1)
  let weightedA : ℝ := cmp99SourceFlowFlatFullComplexA a L depth
  letI : NeZero Kfine := by
    dsimp [Kfine]
    infer_instance
  have hweightedA : 0 ≤ weightedA := by
    dsimp [weightedA, cmp99SourceFlowFlatFullComplexA]
    exact (cmp99SourceMassParameter_pos ha
      (by exact_mod_cast (NeZero.pos L)) depth).le
  have hA :
      0 ≤ cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
        weightedA rho := by
    have hpoint :=
      norm_cmp89Eq248PhysicalZeroMassGreen_le_signedLatticeWeight_draft
        (K := Kfine) hweightedA hrho.le hamplitude hradius hwindow 0
    simpa [cmp89SignedLatticeL1ExponentialWeight,
      cmp89SignedLatticeOneDimensionalExpWeight] using
      (le_trans (norm_nonneg _) hpoint)
  have hgeom : 0 ≤ (2 / (1 - Real.exp (-rho))) ^ 4 := by positivity
  rw [cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0]
  exact mul_nonneg (mul_nonneg hA hgeom) (Real.exp_pos _).le

/-- C5 in the exact named-coefficient normal form. -/
theorem
    norm_cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_pointSource_apply_siteEquiv_le_pointSourceB0
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a)
    (y : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
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
        (cmp99FlatComplexFibrePointSource y v))
          (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth target)‖ ≤
      cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0
          a L depth rho *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth target)
            y : ℝ)) * ‖v‖ := by
  simpa [cmp99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0,
    mul_assoc] using
    (norm_cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_pointSource_apply_siteEquiv_le_sourceOwner
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth ha y v target hrho hamplitude hradius hwindow)

end

end YangMills.RG
