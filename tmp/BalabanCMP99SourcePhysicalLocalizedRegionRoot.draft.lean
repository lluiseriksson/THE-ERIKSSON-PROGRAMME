import YangMills.RG.BalabanCMP99SourcePhysicalLocalizedRegionNonempty

/-!
# Draft: canonical root of a literal physical localization region

PRE-VALIDATION DRAFT: this file is outside the project import graph; its
`.olean` has not been materialized and no compiler or axiom verdict is
claimed.

The root is selected internally from the localized-coordinate witness stored
by `CMP116SourcePhysicalLocalizedRegion`.  It is not caller-supplied data.
-/

namespace YangMills.RG

noncomputable section

/-- The exact fine-site active region induced by a proof-carrying physical
localization carrier. -/
noncomputable def cmp99SourcePhysicalLocalizedActiveRegion
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : CMP116SourcePhysicalLocalizedRegion Dict) :
    ActiveGaugeRegion d (M * N') :=
  { sites := cmp116RegionSites (d := d) (M := M) (N' := N') Z0.1 }

/-- A canonical regional site obtained from the literal localized-coordinate
witness.  No arbitrary root or independent nonemptiness hypothesis enters the
public signature. -/
noncomputable def cmp99SourcePhysicalLocalizedRoot
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : CMP116SourcePhysicalLocalizedRegion Dict) :
    ActiveGaugeRegion.Site
      (cmp99SourcePhysicalLocalizedActiveRegion Dict Z0) :=
  Classical.choice (by
    simpa [cmp99SourcePhysicalLocalizedActiveRegion] using
      nonempty_cmp116SourcePhysicalLocalizedActiveRegion
        Dict Z0.1 Z0.2)

theorem cmp99SourcePhysicalLocalizedRoot_mem
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : CMP116SourcePhysicalLocalizedRegion Dict) :
    (cmp99SourcePhysicalLocalizedRoot Dict Z0).1 ∈
      (cmp99SourcePhysicalLocalizedActiveRegion Dict Z0).sites :=
  (cmp99SourcePhysicalLocalizedRoot Dict Z0).2

end

end YangMills.RG
