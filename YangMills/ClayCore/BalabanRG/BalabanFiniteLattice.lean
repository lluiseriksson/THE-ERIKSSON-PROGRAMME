import Mathlib

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# BalabanFiniteLattice — (v1.0.3-alpha)

Full finite lattice geometry for Bałaban's RG program.
Replaces the simplified BalabanLatticeSite (Fin(2^k)×Fin d) with
the physically faithful (Fin(2^k))^d — a full d-dimensional torus.

## Design

- `BalabanFiniteCoord k = Fin (2^k)`: one coordinate mod 2^k
- `BalabanFiniteSite d k = Fin d → BalabanFiniteCoord k`: full lattice site
- This is (ℤ/2^k ℤ)^d as a type, without the group structure for now.

## Relationship to existing types
- `BalabanLatticeSite d k = Fin(2^k) × Fin d`: simplified (v0.9.x)
- `BalabanFiniteSite d k = Fin d → Fin(2^k)`: full (v1.0.3)
-/

noncomputable section

/-- One coordinate on the scale-k lattice: an integer mod 2^k. -/
abbrev BalabanFiniteCoord (k : ℕ) : Type := Fin (2 ^ k)

/-- A full lattice site: d coordinates, each in Fin(2^k). -/
abbrev BalabanFiniteSite (d k : ℕ) : Type := Fin d → BalabanFiniteCoord k

instance (d k : ℕ) : Fintype (BalabanFiniteSite d k) := inferInstance
instance (d k : ℕ) : DecidableEq (BalabanFiniteSite d k) := inferInstance

/-- Extensionality: two sites are equal iff all coordinates are equal. -/
theorem BalabanFiniteSite.ext {d k : ℕ} {x y : BalabanFiniteSite d k}
    (h : ∀ i, x i = y i) : x = y :=
  funext h

/-- The zero site: all coordinates are 0. -/
def BalabanFiniteSite.zero (d k : ℕ) : BalabanFiniteSite d k :=
  fun _ => ⟨0, pow_pos (by decide : 0 < 2) k⟩

/-- A singleton region containing just the zero site. -/
def BalabanFiniteSite.singletonRegion (d k : ℕ) :
    Finset (BalabanFiniteSite d k) :=
  {BalabanFiniteSite.zero d k}

end

end YangMills.ClayCore
