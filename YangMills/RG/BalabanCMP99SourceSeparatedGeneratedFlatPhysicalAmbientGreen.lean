/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreen
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary
import YangMills.RG.FinitePiLpTypedKernelReindexAlgebra

/-!
# Source-separated generated flat physical ambient Green

PRE-VALIDATION: source present, `.olean` not yet materialized, and results in
this module are not yet compiler-verified.

The generated tower already keeps its RG ratio and initial coarse carrier as
independent parameters.  This file specializes the ratio to `L`, the coarse
carrier to `2*(K*Q)`, and transports the canonical flat precision and Green
through the sealed source-separated full-site equivalence.  Both ordered
inverse laws are retained internally.

No diagonal `K=L` cast, complexification, Step-7b dictionary, regional bound,
physical `B0`, window-15 attainment or terminal field is asserted here.
-/

namespace YangMills.RG

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Canonical flat specialization of the source-separated generated ambient
precision.  The generated ratio is `L`; the independent coarse carrier is
`2*(K*Q)`. -/
noncomputable def cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision
    (hL : 2 ≤ L) (depth : ℕ) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  cmp99SourceSeparatedGeneratedPhysicalAmbientPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    (spacing := cmp99SourceGeneratedFullComplexSpacing L (depth + 1))
    (epsilon := 0) hL depth
    (cmp99SourceFlatGaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) Nc)
    (cmp99SourceFlatZeroClosedBudget
      (d := 4) (M := L) (Nc := Nc) (depth + 1))
    cmp99SourceFlatGaugeConfig_zero_small

/-- The flat separated precision is literally the isometric reindexing of
the internally generated active precision. -/
theorem cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision_eq_reindex
    (hL : 2 ≤ L) (depth : ℕ) :
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth =
      finitePiLpTypedKernelReindex
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
        (cmp99SourceGeneratedFlatPhysicalPrecision
          (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
          (by norm_num) hL
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) depth
          (cmp99SourceGeneratedFullComplexSpacing L (depth + 1))) := by
  rfl

/-- The internally generated flat Green transported onto the source-separated
ambient carrier. -/
noncomputable def cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreen
    (hL : 2 ≤ L) (depth : ℕ) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  finitePiLpTypedKernelReindex
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (cmp99SourceGeneratedFlatPhysicalGreen
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) depth)

/-- The separated ambient flat precision followed by its generated Green is
the identity. -/
theorem cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision_comp_green
    (hL : 2 ≤ L) (depth : ℕ) :
    (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreen
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth) =
      ContinuousLinearMap.id ℝ
        (GaugeZeroCochain 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
          (SUNLieCoord Nc)) := by
  rw [cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision_eq_reindex]
  exact finitePiLpTypedKernelReindex_comp_eq_id
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (cmp99SourceGeneratedFlatPhysicalPrecision
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) depth
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)))
    (cmp99SourceGeneratedFlatPhysicalGreen
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) depth)
    (cmp99SourceGeneratedFlatPhysicalPrecision_comp_green
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) depth)

/-- The separated generated Green followed by the same ambient flat
precision is the identity. -/
theorem cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreen_comp_precision
    (hL : 2 ≤ L) (depth : ℕ) :
    (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreen
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth) =
      ContinuousLinearMap.id ℝ
        (GaugeZeroCochain 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
          (SUNLieCoord Nc)) := by
  rw [cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision_eq_reindex]
  exact finitePiLpTypedKernelReindex_comp_eq_id
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (cmp99SourceGeneratedFlatPhysicalGreen
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) depth)
    (cmp99SourceGeneratedFlatPhysicalPrecision
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) depth
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)))
    (cmp99SourceGeneratedFlatPhysicalGreen_comp_precision
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) depth)

end

end YangMills.RG
