import YangMills.RG.NeumannMixedFixedSource
import Mathlib.Data.Fintype.BigOperators

/-!
PRE-VALIDATION: source present; .olean not materialized; compiler result
not verified. Global translation/branch packaging of the same fixed-source
images. FULL has Unit, not a redundant Bool; PROPER has the reflected pair.
Branch bound contains no block scale or volume. Physical classification,
owner dictionary, Green equation and uniform B0 remain separate obligations.
-/

namespace YangMills.RG

def neumannMixedBranch (full : Bool) : Type :=
  match full with
  | true => Unit
  | false => Bool

instance neumannMixedBranchFintype (full : Bool) : Fintype (neumannMixedBranch full) := by
  cases full <;> exact inferInstance

def neumannMixedBranchCode (full : Bool) : neumannMixedBranch full → Bool :=
  match full with
  | true => fun _ => false
  | false => id

theorem neumannMixedBranchCode_injective (full : Bool) :
    Function.Injective (neumannMixedBranchCode full) := by
  cases full
  · exact Function.injective_id
  · intro x y _
    exact Subsingleton.elim x y

theorem neumannMixedBranchFamily_card_le {d : ℕ} (full : Fin d → Bool) :
    Fintype.card (∀ mu : Fin d, neumannMixedBranch (full mu)) ≤ 2 ^ d := by
  have hi : Function.Injective (fun b : ∀ mu : Fin d,
      neumannMixedBranch (full mu) => fun mu : Fin d =>
        neumannMixedBranchCode (full mu) (b mu)) := by
    intro b c he
    funext mu
    exact neumannMixedBranchCode_injective (full mu) (congrFun he mu)
  have hc : Fintype.card (∀ mu : Fin d, neumannMixedBranch (full mu)) ≤
      Fintype.card (Fin d → Bool) := Fintype.card_le_of_injective _ hi
  simpa using hc

theorem neumannMixedBranchFamily_card_le_sixteen (full : Fin 4 → Bool) :
    Fintype.card (∀ mu : Fin 4, neumannMixedBranch (full mu)) ≤ 16 := by
  simpa using neumannMixedBranchFamily_card_le full

def neumannMixedFixedCoordinatePack (full : Bool) :
    (ℤ × neumannMixedBranch full) ≃ neumannMixedFixedCoordinateIndex full :=
  match full with
  | false => Equiv.refl (ℤ × Bool)
  | true =>
    { toFun := fun p => p.1
      invFun := fun k => (k, ())
      left_inv := by rintro ⟨k, u⟩; cases u; rfl
      right_inv := fun _ => rfl }

def neumannMixedGlobalFixedIndexEquiv {d : ℕ} (full : Fin d → Bool) :
    ((Fin d → ℤ) × (∀ mu : Fin d, neumannMixedBranch (full mu))) ≃
      (∀ mu : Fin d, neumannMixedFixedCoordinateIndex (full mu)) :=
  (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => ℤ)
    (fun mu => neumannMixedBranch (full mu))).symm.trans
      (Equiv.piCongrRight (fun mu : Fin d => neumannMixedFixedCoordinatePack (full mu)))

theorem neumannMixedGlobalFixedIndexEquiv_apply {d : ℕ}
    (full : Fin d → Bool)
    (p : (Fin d → ℤ) × (∀ mu : Fin d, neumannMixedBranch (full mu))) (mu : Fin d) :
    neumannMixedGlobalFixedIndexEquiv full p mu =
      neumannMixedFixedCoordinatePack (full mu) (p.1 mu, p.2 mu) := rfl

theorem neumannMixedGlobalFixedSource_injective {d : ℕ}
    (full : Fin d → Bool) (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu)
    (n : ∀ mu : Fin d, neumannImageIntervalPoint (m mu)) :
    Function.Injective (fun p => neumannMixedFixedSourceImage full m n
      (neumannMixedGlobalFixedIndexEquiv full p)) :=
  (neumannMixedFixedSourceImage_injective full m hm n).comp
    (neumannMixedGlobalFixedIndexEquiv full).injective

end YangMills.RG

#print axioms YangMills.RG.neumannMixedBranchCode_injective
#print axioms YangMills.RG.neumannMixedBranchFamily_card_le
#print axioms YangMills.RG.neumannMixedBranchFamily_card_le_sixteen
#print axioms YangMills.RG.neumannMixedFixedCoordinatePack
#print axioms YangMills.RG.neumannMixedGlobalFixedIndexEquiv
#print axioms YangMills.RG.neumannMixedGlobalFixedIndexEquiv_apply
#print axioms YangMills.RG.neumannMixedGlobalFixedSource_injective
