/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ConnectedLocalizationRegrouping

/-!
# Connected localization anchored by a finite physical carrier

CMP116 equation (1.10) does not root the connected component at an arbitrarily
chosen weakening derivative.  It roots it at the distinguished physical cube
`Pi^4`, which is itself a finite carrier of large blocks.

This module upgrades the earlier single-vertex regrouping to that source
shape.  The canonical domain is the union of precisely those confined
components of `anchorCarrier ∪ active a` which meet `anchorCarrier`.  Hence a
disconnected component made only of weakening cubes is discarded
definitionally.

If the anchor carrier is nonempty and walk-connected, the union is one
confined component and is therefore walk-connected.  The final theorem is an
exact finite fiber regrouping; it introduces no domain label chosen after the
fact and no decay or summability hypothesis.
-/

namespace YangMills.RG

noncomputable section

universe u v w

variable {ι : Type u} {α : Type v} {E : Type w}
variable [DecidableEq ι] [AddCommMonoid E]

/-- The union of the confined components which touch the distinguished
finite anchor carrier. -/
noncomputable def cmp116CarrierAnchoredLocalizationDomain
    (G : SimpleGraph ι) (anchorCarrier : Finset ι)
    (active : α → Finset ι) (a : α) : Finset ι :=
  anchorCarrier.biUnion fun root =>
    confinedComponent G (anchorCarrier ∪ active a) root

/-- Every point of the physical anchor carrier belongs to the carrier-anchored
domain. -/
theorem cmp116Carrier_subset_carrierAnchoredLocalizationDomain
    (G : SimpleGraph ι) (anchorCarrier : Finset ι)
    (active : α → Finset ι) (a : α) :
    anchorCarrier ⊆
      cmp116CarrierAnchoredLocalizationDomain
        G anchorCarrier active a := by
  intro root hroot
  rw [cmp116CarrierAnchoredLocalizationDomain, Finset.mem_biUnion]
  exact ⟨root, hroot,
    root_mem_confinedComponent G _
      (Finset.mem_union_left _ hroot)⟩

/-- The canonical domain contains nothing outside the anchor carrier and the
literal active weakening carrier. -/
theorem cmp116CarrierAnchoredLocalizationDomain_subset
    (G : SimpleGraph ι) (anchorCarrier : Finset ι)
    (active : α → Finset ι) (a : α) :
    cmp116CarrierAnchoredLocalizationDomain
        G anchorCarrier active a ⊆
      anchorCarrier ∪ active a := by
  intro x hx
  rw [cmp116CarrierAnchoredLocalizationDomain, Finset.mem_biUnion] at hx
  obtain ⟨root, _hroot, hx⟩ := hx
  exact confinedComponent_subset G _ root hx

/-- When the physical anchor carrier is connected, all of its rooted
components coincide.  Thus the carrier-anchored union is literally a single
confined component. -/
theorem cmp116CarrierAnchoredLocalizationDomain_eq_confinedComponent
    (G : SimpleGraph ι) (anchorCarrier : Finset ι)
    (active : α → Finset ι) (a : α)
    {root : ι} (hroot : root ∈ anchorCarrier)
    (hconnected : walkConnected G anchorCarrier) :
    cmp116CarrierAnchoredLocalizationDomain
        G anchorCarrier active a =
      confinedComponent G (anchorCarrier ∪ active a) root := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    rw [cmp116CarrierAnchoredLocalizationDomain,
      Finset.mem_biUnion] at hx
    obtain ⟨other, hother, hx⟩ := hx
    obtain ⟨walk, hwalk⟩ :=
      hconnected root hroot other hother
    have hotherComponent :
        other ∈ confinedComponent
          G (anchorCarrier ∪ active a) root := by
      rw [mem_confinedComponent_iff]
      exact ⟨Finset.mem_union_left _ hother,
        ⟨walk, fun z hz =>
          Finset.mem_union_left _ (hwalk z hz)⟩⟩
    have heq :=
      confinedComponent_eq_of_mem
        G (anchorCarrier ∪ active a) hotherComponent
    simpa [heq] using hx
  · intro x hx
    rw [cmp116CarrierAnchoredLocalizationDomain,
      Finset.mem_biUnion]
    exact ⟨root, hroot, hx⟩

/-- A nonempty connected physical anchor carrier therefore produces a
walk-connected canonical localization domain. -/
theorem cmp116CarrierAnchoredLocalizationDomain_walkConnected
    (G : SimpleGraph ι) (anchorCarrier : Finset ι)
    (active : α → Finset ι) (a : α)
    (hne : anchorCarrier.Nonempty)
    (hconnected : walkConnected G anchorCarrier) :
    walkConnected G
      (cmp116CarrierAnchoredLocalizationDomain
        G anchorCarrier active a) := by
  classical
  obtain ⟨root, hroot⟩ := hne
  rw [cmp116CarrierAnchoredLocalizationDomain_eq_confinedComponent
    G anchorCarrier active a hroot hconnected]
  exact confinedComponent_walkConnected G _ root

/-- The finite image of the canonical carrier-anchored domains. -/
noncomputable def cmp116CarrierAnchoredLocalizationDomains
    (G : SimpleGraph ι) (source : Finset α)
    (anchorCarrier : Finset ι) (active : α → Finset ι) :
    Finset (Finset ι) :=
  source.image
    (cmp116CarrierAnchoredLocalizationDomain
      G anchorCarrier active)

/-- Sum of exactly the raw terms whose canonical carrier-anchored domain is
`Y`. -/
noncomputable def cmp116CarrierAnchoredFiberCoefficient
    (G : SimpleGraph ι) (source : Finset α)
    (anchorCarrier : Finset ι) (active : α → Finset ι)
    (term : α → E) (Y : Finset ι) : E :=
  ∑ a ∈ source.filter fun a =>
    cmp116CarrierAnchoredLocalizationDomain
      G anchorCarrier active a = Y, term a

/-- Exact finite regrouping by the physical carrier-anchored domain. -/
theorem cmp116_sum_eq_sum_carrierAnchoredFiberCoefficient
    (G : SimpleGraph ι) (source : Finset α)
    (anchorCarrier : Finset ι) (active : α → Finset ι)
    (term : α → E) :
    (∑ a ∈ source, term a) =
      ∑ Y ∈ cmp116CarrierAnchoredLocalizationDomains
          G source anchorCarrier active,
        cmp116CarrierAnchoredFiberCoefficient
          G source anchorCarrier active term Y := by
  classical
  simp only [cmp116CarrierAnchoredFiberCoefficient]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) term).symm

end

end YangMills.RG
