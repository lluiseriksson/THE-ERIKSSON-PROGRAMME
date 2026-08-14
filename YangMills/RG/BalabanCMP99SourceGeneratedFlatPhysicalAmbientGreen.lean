/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreen
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalAmbientDictionary
import YangMills.RG.FinitePiLpTypedKernelReindexAlgebra

/-!
# Generated flat physical Green on the source ambient carrier

PRE-VALIDATION: source present; `.olean` not yet materialized; result not yet
verified by the compiler.

The internally generated flat precision and Green initially live on the full
active terminal carrier.  This file transports both through the one sealed
full-site equivalence used by the regional large-block construction and
retains both ordered inverse laws exactly.

No complexification, Step-7b physical precision dictionary, complex inverse,
or literal full-box Green identification is asserted here.
-/

namespace YangMills.RG

noncomputable section

variable {M Q Nc : ℕ}
variable [NeZero M] [NeZero Q] [NeZero Nc]

/-- Canonical flat specialization of the already named generated physical
ambient precision. -/
noncomputable def cmp99SourceGeneratedFlatPhysicalAmbientPrecision
    (hM : 2 ≤ M) (depth : ℕ) :
    GaugeZeroCochain 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
        (SUNLieCoord Nc) :=
  cmp99SourceGeneratedPhysicalAmbientPrecision
    (M := M) (Q := Q) (Nc := Nc)
    (spacing := cmp99SourceGeneratedFullComplexSpacing M (depth + 1))
    (epsilon := 0) hM depth
    (cmp99SourceFlatGaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) Nc)
    (cmp99SourceFlatZeroClosedBudget
      (d := 4) (M := M) (Nc := Nc) (depth + 1))
    cmp99SourceFlatGaugeConfig_zero_small

/-- The same flat precision is literally the isometric reindexing of the
internally generated active precision. -/
theorem cmp99SourceGeneratedFlatPhysicalAmbientPrecision_eq_reindex
    (hM : 2 ≤ M) (depth : ℕ) :
    cmp99SourceGeneratedFlatPhysicalAmbientPrecision
        (M := M) (Q := Q) (Nc := Nc) hM depth =
      finitePiLpTypedKernelReindex
        (cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth)
        (cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth)
        (cmp99SourceGeneratedFlatPhysicalPrecision
          (d := 4) (M := M) (N := 2 * (M * Q)) (Nc := Nc)
          (by norm_num) hM
          (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth
          (cmp99SourceGeneratedFullComplexSpacing M (depth + 1))) := by
  rfl

/-- The internally generated flat physical Green transported to the same
ambient carrier as the regional precision. -/
noncomputable def cmp99SourceGeneratedFlatPhysicalAmbientGreen
    (hM : 2 ≤ M) (depth : ℕ) :
    GaugeZeroCochain 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
        (SUNLieCoord Nc) :=
  finitePiLpTypedKernelReindex
    (cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth)
    (cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth)
    (cmp99SourceGeneratedFlatPhysicalGreen
      (d := 4) (M := M) (N := 2 * (M * Q)) (Nc := Nc)
      (by norm_num) hM
      (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth)

/-- The ambient flat precision followed by its reindexed generated Green is
the identity. -/
theorem cmp99SourceGeneratedFlatPhysicalAmbientPrecision_comp_green
    (hM : 2 ≤ M) (depth : ℕ) :
    (cmp99SourceGeneratedFlatPhysicalAmbientPrecision
      (M := M) (Q := Q) (Nc := Nc) hM depth).comp
        (cmp99SourceGeneratedFlatPhysicalAmbientGreen
          (M := M) (Q := Q) (Nc := Nc) hM depth) =
      ContinuousLinearMap.id ℝ
        (GaugeZeroCochain 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
          (SUNLieCoord Nc)) := by
  rw [cmp99SourceGeneratedFlatPhysicalAmbientPrecision_eq_reindex]
  exact finitePiLpTypedKernelReindex_comp_eq_id
    (cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth)
    (cmp99SourceGeneratedFlatPhysicalPrecision
      (d := 4) (M := M) (N := 2 * (M * Q)) (Nc := Nc)
      (by norm_num) hM
      (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth
      (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)))
    (cmp99SourceGeneratedFlatPhysicalGreen
      (d := 4) (M := M) (N := 2 * (M * Q)) (Nc := Nc)
      (by norm_num) hM
      (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth)
    (cmp99SourceGeneratedFlatPhysicalPrecision_comp_green
      (d := 4) (M := M) (N := 2 * (M * Q)) (Nc := Nc)
      (by norm_num) hM
      (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth)

/-- The reindexed generated Green followed by the same ambient flat precision
is the identity. -/
theorem cmp99SourceGeneratedFlatPhysicalAmbientGreen_comp_precision
    (hM : 2 ≤ M) (depth : ℕ) :
    (cmp99SourceGeneratedFlatPhysicalAmbientGreen
      (M := M) (Q := Q) (Nc := Nc) hM depth).comp
        (cmp99SourceGeneratedFlatPhysicalAmbientPrecision
          (M := M) (Q := Q) (Nc := Nc) hM depth) =
      ContinuousLinearMap.id ℝ
        (GaugeZeroCochain 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
          (SUNLieCoord Nc)) := by
  rw [cmp99SourceGeneratedFlatPhysicalAmbientPrecision_eq_reindex]
  exact finitePiLpTypedKernelReindex_comp_eq_id
    (cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth)
    (cmp99SourceGeneratedFlatPhysicalGreen
      (d := 4) (M := M) (N := 2 * (M * Q)) (Nc := Nc)
      (by norm_num) hM
      (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth)
    (cmp99SourceGeneratedFlatPhysicalPrecision
      (d := 4) (M := M) (N := 2 * (M * Q)) (Nc := Nc)
      (by norm_num) hM
      (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth
      (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)))
    (cmp99SourceGeneratedFlatPhysicalGreen_comp_precision
      (d := 4) (M := M) (N := 2 * (M * Q)) (Nc := Nc)
      (by norm_num) hM
      (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth)

end

end YangMills.RG
