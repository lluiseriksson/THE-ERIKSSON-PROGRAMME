import YangMills.RG.BalabanCMP116FTCInterpolation

open scoped BigOperators

namespace YangMills.RG

universe u v w

variable {α : Type u} {κ : Type v} {E : Type w}
variable [DecidableEq α] [DecidableEq κ] [AddCommMonoid E]

def fiberCoeff (source : Finset α) (key : α → κ) (term : α → E) (y : κ) : E :=
  ∑ a ∈ source.filter fun a => key a = y, term a

theorem sum_eq_sum_fiberCoeff
    (source : Finset α) (targets : Finset κ)
    (key : α → κ) (term : α → E)
    (hmap : ∀ a ∈ source, key a ∈ targets) :
    (∑ a ∈ source, term a) = ∑ y ∈ targets, fiberCoeff source key term y := by
  simp only [fiberCoeff]
  exact (Finset.sum_fiberwise_of_maps_to hmap term).symm

end YangMills.RG
