import YangMills.RG.BalabanCMP116FTCInterpolation
import YangMills.RG.MayerCoverFactorization

/-!
# CMP116 equation (1.10): regrouping by an anchored connected domain

After the repeated-FTC expansion, Balaban groups terms by the connected
localization domain containing the distinguished plaquette cube.  This file
formalizes that exact finite regrouping without allowing an arbitrary unconstrained
"domain key".

For every raw term, `cmp116AnchoredLocalizationDomain` is literally the
component, inside the active weakening cubes plus the anchor, that contains the
anchor.  The domain is therefore connected, contains its anchor, and is
contained in the active carrier by construction.  Terms are then grouped by
equality of these canonical domains, and the total finite sum is unchanged.

Honest scope: `active` and `anchor` remain source data.  The file does not yet
construct them from the random-walk support of the physical `s`-dependent
propagators, and it does not identify a fiber coefficient with Balaban's
`V_k(Y, ·)`.  It supplies the exact connected reindexing that the physical
producer must instantiate after building those propagators and their FTC tree.
-/

open scoped BigOperators

namespace YangMills.RG

universe u v w

variable {ι : Type u} {α : Type v} {E : Type w}
variable [DecidableEq ι] [AddCommMonoid E]

/-- The canonical component of the active weakening carrier containing the
distinguished plaquette cube. -/
noncomputable def cmp116AnchoredLocalizationDomain
    (G : SimpleGraph ι) (anchor : α → ι)
    (active : α → Finset ι) (a : α) : Finset ι :=
  confinedComponent G (insert (anchor a) (active a)) (anchor a)

/-- The distinguished plaquette cube belongs to its anchored domain. -/
theorem cmp116Anchor_mem_anchoredLocalizationDomain
    (G : SimpleGraph ι) (anchor : α → ι)
    (active : α → Finset ι) (a : α) :
    anchor a ∈ cmp116AnchoredLocalizationDomain G anchor active a := by
  exact root_mem_confinedComponent G _ (Finset.mem_insert_self _ _)

/-- An anchored domain contains no cube outside the active carrier and its
distinguished anchor. -/
theorem cmp116AnchoredLocalizationDomain_subset
    (G : SimpleGraph ι) (anchor : α → ι)
    (active : α → Finset ι) (a : α) :
    cmp116AnchoredLocalizationDomain G anchor active a ⊆
      insert (anchor a) (active a) := by
  exact confinedComponent_subset G _ _

/-- The canonical anchored domain is walk-connected in the physical adjacency
graph. -/
theorem cmp116AnchoredLocalizationDomain_walkConnected
    (G : SimpleGraph ι) (anchor : α → ι)
    (active : α → Finset ι) (a : α) :
    walkConnected G (cmp116AnchoredLocalizationDomain G anchor active a) := by
  exact confinedComponent_walkConnected G _ _

/-- The finite family of canonical domains appearing among the raw terms. -/
noncomputable def cmp116AnchoredLocalizationDomains
    (G : SimpleGraph ι) (source : Finset α)
    (anchor : α → ι) (active : α → Finset ι) :
    Finset (Finset ι) :=
  source.image (cmp116AnchoredLocalizationDomain G anchor active)

/-- The coefficient obtained by summing exactly the raw terms whose canonical
anchored domain is `Y`.  This is a finite fiber sum, not yet the physical CMP116
localized activity. -/
noncomputable def cmp116AnchoredFiberCoefficient
    (G : SimpleGraph ι) (source : Finset α)
    (anchor : α → ι) (active : α → Finset ι)
    (term : α → E) (Y : Finset ι) : E :=
  ∑ a ∈ source.filter fun a =>
    cmp116AnchoredLocalizationDomain G anchor active a = Y, term a

/-- Exact regrouping of a finite family by the anchored connected domain from
equation (1.10). -/
theorem cmp116_sum_eq_sum_anchoredFiberCoefficient
    (G : SimpleGraph ι) (source : Finset α)
    (anchor : α → ι) (active : α → Finset ι)
    (term : α → E) :
    (∑ a ∈ source, term a) =
      ∑ Y ∈ cmp116AnchoredLocalizationDomains G source anchor active,
        cmp116AnchoredFiberCoefficient G source anchor active term Y := by
  classical
  simp only [cmp116AnchoredFiberCoefficient]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) term).symm

end YangMills.RG
