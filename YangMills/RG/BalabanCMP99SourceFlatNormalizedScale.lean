/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatUbarPreservation

/-!
# The canonical normalized CMP99 scale at the flat background

This file installs the sealed flat-Ubar preservation theorem in the canonical
source-normalized one-scale constructor.  The fine radius is literally zero,
so fine-link smallness and no winding are derived internally.  In particular,
neither a normalized scale nor its next background is caller data.

Honest scope: this is one source-normalized scale over an arbitrary saturated
active region.  It does not yet prove recursive flatness of the retained
physical tower, identify its iterated `Q'`, or compare the counting adjoint
with the printed weighted adjoint.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {d M N' Nc : ℕ}
variable [hd0 : NeZero d] [hM0 : NeZero M] [hN'0 : NeZero N']
variable [hNc0 : NeZero Nc]

/-- The explicit Mercator no-winding threshold is strictly positive for every
nontrivial special-unitary rank. -/
theorem cmp99UbarNoWindingThreshold_pos :
    0 < cmp99UbarNoWindingThreshold Nc := by
  have hNc : 0 < (Nc : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Nc)
  unfold cmp99UbarNoWindingThreshold
  positivity

/-- The canonical source-normalized scale on the literal flat fine
background.  Radius zero, linkwise smallness, and no winding are all generated
inside the definition. -/
noncomputable def cmp99SourceFlatNormalizedRegionalScale
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (blockSaturated : Omega.BlockSaturated) :
    CMP99SourceNormalizedRegionalScale Omega
      (cmp99SourceFlatGaugeConfig d (M * N') Nc) :=
  CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega
    (cmp99SourceFlatGaugeConfig d (M * N') Nc) blockSaturated
    0 (by positivity)
    (by
      simpa [cmp99SourceUbarFineDeviationRadius] using
        (cmp99UbarNoWindingThreshold_pos (Nc := Nc)))
    (by
      intro e
      simp)

/-- The next background of the canonical zero-radius normalized scale is
definitionally fed by physical Ubar and propositionally equals the literal
flat coarse gauge configuration. -/
@[simp] theorem cmp99SourceFlatNormalizedRegionalScale_nextBackground
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (blockSaturated : Omega.BlockSaturated) :
    (cmp99SourceFlatNormalizedRegionalScale hd hM Omega blockSaturated).toSourceScale.data.nextBackground =
      cmp99SourceFlatGaugeConfig d N' Nc := by
  change
    cmp99PhysicalUbarGaugeConfigOfDeviationBudget
        (cmp99SourceFlatGaugeConfig d (M * N') Nc)
        (cmp99SourceBaseCoarseBackground
          (cmp99SourceFlatGaugeConfig d (M * N') Nc))
        _ _ _ _ _ =
      cmp99SourceFlatGaugeConfig d N' Nc
  exact cmp99PhysicalUbarGaugeConfigOfDeviationBudget_flat _ _ _ _ _

end

end YangMills.RG
