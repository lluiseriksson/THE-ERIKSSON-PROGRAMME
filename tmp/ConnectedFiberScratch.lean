import YangMills.RG.BalabanCMP116FTCInterpolation
import YangMills.RG.MayerCoverFactorization

open scoped BigOperators

namespace YangMills.RG

universe u v w

variable {ι : Type u} {α : Type v} {E : Type w}
variable [DecidableEq ι] [DecidableEq α] [AddCommMonoid E]

noncomputable def anchoredDomain (G : SimpleGraph ι)
    (anchor : α → ι) (active : α → Finset ι) (a : α) : Finset ι :=
  confinedComponent G (insert (anchor a) (active a)) (anchor a)

theorem anchor_mem_anchoredDomain (G : SimpleGraph ι)
    (anchor : α → ι) (active : α → Finset ι) (a : α) :
    anchor a ∈ anchoredDomain G anchor active a := by
  exact root_mem_confinedComponent G _ (Finset.mem_insert_self _ _)

theorem anchoredDomain_subset (G : SimpleGraph ι)
    (anchor : α → ι) (active : α → Finset ι) (a : α) :
    anchoredDomain G anchor active a ⊆ insert (anchor a) (active a) := by
  exact confinedComponent_subset G _ _

theorem anchoredDomain_walkConnected (G : SimpleGraph ι)
    (anchor : α → ι) (active : α → Finset ι) (a : α) :
    walkConnected G (anchoredDomain G anchor active a) := by
  exact confinedComponent_walkConnected G _ _

noncomputable def anchoredDomains (G : SimpleGraph ι)
    (source : Finset α) (anchor : α → ι) (active : α → Finset ι) :
    Finset (Finset ι) :=
  source.image (anchoredDomain G anchor active)

noncomputable def anchoredFiberCoefficient (G : SimpleGraph ι)
    (source : Finset α) (anchor : α → ι) (active : α → Finset ι)
    (term : α → E) (Y : Finset ι) : E :=
  ∑ a ∈ source.filter fun a => anchoredDomain G anchor active a = Y, term a

theorem sum_eq_sum_anchoredFiberCoefficient (G : SimpleGraph ι)
    (source : Finset α) (anchor : α → ι) (active : α → Finset ι)
    (term : α → E) :
    (∑ a ∈ source, term a) =
      ∑ Y ∈ anchoredDomains G source anchor active,
        anchoredFiberCoefficient G source anchor active term Y := by
  classical
  simp only [anchoredFiberCoefficient]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) term).symm

end YangMills.RG
