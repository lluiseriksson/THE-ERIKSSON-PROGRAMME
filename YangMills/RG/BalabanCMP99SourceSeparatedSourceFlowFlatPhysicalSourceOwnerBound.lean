/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceOwnerBound
import YangMills.RG.BalabanCMP99Eq389SourceLocalizationOwner

/-!
# Source-localization owner form of the literal source-flow Green bound

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

The Unit-F point-source endpoint is evaluated at the sealed source-separated
site equivalence and its block owner is rewritten to the literal CMP99 (3.89)
`cmp99Eq389SourceLocalizationOwner`.  The source coefficient remains
`cmp99SourceFlowFlatFullComplexA a L depth`, with positivity derived upstream
from `ha`.

No generated coefficient, cardinality equivalence, supplied readout,
regional compression, `B0`, window-15 attainment or terminal field is
introduced.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The literal source-flow point-source Green bound measured from the CMP99
source-localization owner of the regional target to the actual coarse source
site. -/
theorem
    norm_cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_pointSource_apply_siteEquiv_le_sourceOwner
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
      (cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
          (cmp99SourceFlowFlatFullComplexA a L depth) rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist
              (cmp99Eq389SourceLocalizationOwner L K Q depth target)
              y : ℝ))) * ‖v‖ := by
  simpa [cmp99Eq389SourceLocalizationOwner] using
    (norm_cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_pointSource_apply_le_owner
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth ha y v
      (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth target)
      hrho hamplitude hradius hwindow)

end

end YangMills.RG
