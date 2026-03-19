import Mathlib
import YangMills.ClayCore.BalabanRG.BlockSpin
import YangMills.ClayCore.BalabanRG.BalabanFieldSpace

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# LatticeSiteAdapter — (v1.0.2-alpha)

Adapter: LatticeSite d (= Fin d → ℤ) → BalabanLatticeSite d k (= Fin(2^k) × Fin d)

Requires [NeZero d]: BalabanLatticeSite d k = Fin(2^k) × Fin d needs Fin d ≠ Fin 0.
Encoding: uses coordinate 0 of LatticeSite, reduced mod 2^k.
-/

noncomputable section

/-- Project an integer to Fin(2^k) by taking natAbs mod 2^k. -/
def intToFin (k : ℕ) (z : ℤ) : Fin (2 ^ k) :=
  ⟨z.natAbs % (2 ^ k), Nat.mod_lt _ (pow_pos (by decide : 0 < 2) k)⟩

/-- Project LatticeSite d to BalabanLatticeSite d k.
    Uses coordinate 0 (requires d > 0 via [NeZero d]). -/
def toBalabanSite (d k : ℕ) [NeZero d] (x : LatticeSite d) :
    BalabanLatticeSite d k :=
  let h : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  (intToFin k (x ⟨0, h⟩), ⟨0, h⟩)

/-- toBalabanSite is total. 0 sorrys. -/
theorem toBalabanSite_total (d k : ℕ) [NeZero d] (x : LatticeSite d) :
    ∃ y : BalabanLatticeSite d k, y = toBalabanSite d k x :=
  ⟨toBalabanSite d k x, rfl⟩

/-- Zero coordinate maps to intToFin k 0. 0 sorrys. -/
theorem toBalabanSite_zero_coord (k d : ℕ) [NeZero d] :
    (toBalabanSite d k (fun _ => 0)).1 = intToFin k 0 := by
  simp [toBalabanSite]

end

end YangMills.ClayCore
