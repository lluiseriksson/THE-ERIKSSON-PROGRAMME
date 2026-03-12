import Mathlib

namespace YangMills

abbrev FinBox (d N : ℕ) := Fin d → Fin N

theorem card_finBox (d N : ℕ) : Fintype.card (FinBox d N) = N ^ d := by
  simp [FinBox, Fintype.card_pi, Finset.prod_const, Fintype.card_fin]

instance instInhabitedFinBox (d N : ℕ) [NeZero N] : Inhabited (FinBox d N) :=
  ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩

end YangMills
