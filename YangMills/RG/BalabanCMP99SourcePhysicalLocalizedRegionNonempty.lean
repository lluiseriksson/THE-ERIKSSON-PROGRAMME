import YangMills.RG.BalabanCMP116SourcePhysicalCoordinateDictionary
import YangMills.RG.BalabanCMP99SourceDirichletProblem

/-!
# Scratch: localized CMP116 coordinates give a literal CMP99 regional site

PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

This leaf removes the free `root : ActiveGaugeRegion.Site Omega` used by the
prepared owner/action prefix when `Omega` is the literal fine-site realization
of a proof-carrying physical localization region.  It uses the source endpoint
of the interior physical bond already carried by a localized Lie coordinate;
it does not assume a nonempty region, selected bond set or regional Green.
-/

namespace YangMills.RG

open Finset

noncomputable section

/-- A literal localized Lie coordinate supplies a fine site in the physical
region induced by the same coarse block carrier. -/
theorem cmp116RegionSites_nonempty_of_sourcePhysicalLocalizedCoordinates
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (hZ0 : (cmp116SourcePhysicalLocalizedCoordinates Dict Z0).Nonempty) :
    (cmp116RegionSites (d := d) (M := M) (N' := N') Z0).Nonempty := by
  rcases hZ0 with ⟨ba, hba⟩
  have hinterior : cmp116BondInterior Z0 ba.1 :=
    (mem_cmp116SourcePhysicalLocalizedCoordinates_iff Dict Z0 ba).mp hba
  exact ⟨cmp116BondSource ba.1, hinterior.1.1⟩

/-- The previous witness inhabits the exact active zero-cochain carrier; no
new nonemptiness premise is introduced at the subtype boundary. -/
theorem nonempty_cmp116SourcePhysicalLocalizedActiveRegion
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Z0 : Finset (FinBox d N'))
    (hZ0 : (cmp116SourcePhysicalLocalizedCoordinates Dict Z0).Nonempty) :
    Nonempty (ActiveGaugeRegion.Site
      ({ sites := cmp116RegionSites (d := d) (M := M) (N' := N') Z0 } :
        ActiveGaugeRegion d (M * N'))) := by
  rcases cmp116RegionSites_nonempty_of_sourcePhysicalLocalizedCoordinates
      Dict Z0 hZ0 with ⟨x, hx⟩
  exact ⟨⟨x, hx⟩⟩

/-- Source-region specialization for the literal CMP99 Dirichlet carrier.
The only input is nonemptiness of the corresponding localized coordinate
carrier; the regional site witness is constructed internally. -/
theorem nonempty_cmp99OmegaActiveGaugeRegion_of_sourcePhysicalLocalizedCoordinates
    {Q M j Nc L lieDim : ℕ}
    [NeZero Q] [NeZero M] [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {cell : FinBox 4 Q}
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (hregion : (cmp116SourcePhysicalLocalizedCoordinates
      Dict (Seq.regions r)).Nonempty) :
    Nonempty (ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r)) := by
  simpa [cmp99OmegaActiveGaugeRegion] using
    (nonempty_cmp116SourcePhysicalLocalizedActiveRegion
      Dict (Seq.regions r) hregion)

end

end YangMills.RG
