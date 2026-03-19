import Mathlib
import YangMills.ClayCore.BalabanRG.BlockSpin
import YangMills.ClayCore.BalabanRG.BalabanFiniteLattice

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# LatticeSiteAdapterFull — (v1.0.3-alpha)

Full adapter: LatticeSite d (= Fin d → ℤ) → BalabanFiniteSite d k (= Fin d → Fin(2^k))

Each coordinate is reduced mod 2^k using Int.natAbs % 2^k.
This is the full (ℤ/2^k ℤ)^d projection, unlike the simplified version
in LatticeSiteAdapter which only uses coordinate 0.
-/

noncomputable section

/-- Project integer coordinate to Fin(2^k) via natAbs mod 2^k. -/
def intToFinCoord (k : ℕ) (z : ℤ) : BalabanFiniteCoord k :=
  ⟨z.natAbs % (2 ^ k), Nat.mod_lt _ (pow_pos (by decide : 0 < 2) k)⟩

/-- Project LatticeSite d to BalabanFiniteSite d k coordinate-wise. -/
def toBalabanFiniteSite (d k : ℕ) (x : LatticeSite d) : BalabanFiniteSite d k :=
  fun i => intToFinCoord k (x i)

/-- toBalabanFiniteSite is total. 0 sorrys. -/
theorem toBalabanFiniteSite_total (d k : ℕ) (x : LatticeSite d) :
    ∃ y : BalabanFiniteSite d k, y = toBalabanFiniteSite d k x :=
  ⟨toBalabanFiniteSite d k x, rfl⟩

/-- The zero LatticeSite maps to the zero BalabanFiniteSite. -/
theorem toBalabanFiniteSite_zero (d k : ℕ) :
    toBalabanFiniteSite d k (fun _ => 0) = BalabanFiniteSite.zero d k := by
  funext i
  simp [toBalabanFiniteSite, intToFinCoord, BalabanFiniteSite.zero]

/-- Extensionality for adapter: equal if same projection on all coords. -/
theorem toBalabanFiniteSite_ext {d k : ℕ} {x y : LatticeSite d}
    (h : ∀ i, x i = y i) :
    toBalabanFiniteSite d k x = toBalabanFiniteSite d k y := by
  funext i; simp [toBalabanFiniteSite, h i]

end

end YangMills.ClayCore
