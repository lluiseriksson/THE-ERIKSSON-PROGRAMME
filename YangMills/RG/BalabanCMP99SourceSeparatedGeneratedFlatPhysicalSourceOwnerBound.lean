/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBound
import YangMills.RG.BalabanCMP99Eq389SourceLocalizationOwner

/-!
# Source-localization owner form of the separated generated Green bound

C4b is stated on the flat source-localization carrier.  The physical regional
presentation stores the same fine site through the already sealed
source-separated site equivalence.  This module evaluates C4b at that exact
image and rewrites its block owner to the literal CMP99 (3.89)
`cmp99Eq389SourceLocalizationOwner`.

No cardinality equivalence, diagonal `K=L` cast, supplied readout, regional
compression, `B0`, window-15 attainment or terminal field is introduced.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The generated point-source Green bound measured between the literal
CMP99 source-localization owner of the regional target and the actual coarse
source site. -/
theorem
    norm_cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_apply_siteEquiv_le_sourceOwner
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
      (cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist
              (cmp99Eq389SourceLocalizationOwner L K Q depth target)
              y : ℝ))) * ‖v‖ := by
  simpa [cmp99Eq389SourceLocalizationOwner] using
    (norm_cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_apply_le_owner
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth y v
      (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth target)
      hrho hamplitude hradius hwindow)

end

end YangMills.RG
