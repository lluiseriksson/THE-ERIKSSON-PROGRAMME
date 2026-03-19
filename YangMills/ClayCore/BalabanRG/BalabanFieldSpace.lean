import Mathlib

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# BalabanFieldSpace — Layer 15A (v0.9.0)

Geometric foundation for Bałaban's RG program.
Leaf file. No imports from analytic chain.
-/

noncomputable section

/-- A site in the d-dimensional lattice at scale k. -/
abbrev LatticeSite (d k : ℕ) : Type := Fin (2 ^ k) × Fin d

instance (d k : ℕ) : Fintype (LatticeSite d k) := by
  dsimp [LatticeSite]; infer_instance

instance (d k : ℕ) : DecidableEq (LatticeSite d k) := by
  dsimp [LatticeSite]; infer_instance

/-- A region at scale k is a finite set of sites. -/
abbrev Region (d k : ℕ) : Type := Finset (LatticeSite d k)

/-- A Bałaban block at scale k. -/
structure Block (d k : ℕ) where
  center : LatticeSite d k
  sites  : Region d k
deriving DecidableEq

/-- Support of a field: sites where f x ≠ 0. -/
def fieldSupport {d k : ℕ} (f : LatticeSite d k → ℝ) : Finset (LatticeSite d k) :=
  Finset.univ.filter (fun x => f x ≠ 0)

theorem fieldSupport_empty_iff {d k : ℕ} (f : LatticeSite d k → ℝ) :
    fieldSupport f = ∅ ↔ ∀ x, f x = 0 := by
  constructor
  · intro h x
    by_contra hx
    have hxmem : x ∈ fieldSupport f :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
    simpa [h] using hxmem
  · intro h
    ext x
    simp [fieldSupport, h x]

/-- Monotonicity of support. -/
theorem fieldSupport_mono {d k : ℕ} {f g : LatticeSite d k → ℝ}
    (h : ∀ x, f x ≠ 0 → g x ≠ 0) :
    fieldSupport f ⊆ fieldSupport g := by
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxU, hfx⟩
  exact Finset.mem_filter.mpr ⟨hxU, h x hfx⟩

/-- A field is supported in a region R. -/
def supportedIn {d k : ℕ} (f : LatticeSite d k → ℝ) (R : Region d k) : Prop :=
  fieldSupport f ⊆ R

/-- Block partition placeholder. -/
def isBlockPartition (d k : ℕ) (blocks : Finset (Block d k)) : Prop :=
  ∀ x : LatticeSite d k, ∃ B, B ∈ blocks ∧ x ∈ B.sites

/-- Large-field region at threshold t. -/
def largeFieldRegion {d k : ℕ} (f : LatticeSite d k → ℝ) (t : ℝ) :
    Finset (LatticeSite d k) :=
  Finset.univ.filter (fun x => t ≤ |f x|)

/-- Small-field region at threshold t. -/
def smallFieldRegion {d k : ℕ} (f : LatticeSite d k → ℝ) (t : ℝ) :
    Finset (LatticeSite d k) :=
  Finset.univ.filter (fun x => |f x| < t)

theorem largeSmallPartition {d k : ℕ} (f : LatticeSite d k → ℝ) (t : ℝ) :
    largeFieldRegion f t ∪ smallFieldRegion f t = Finset.univ := by
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    largeFieldRegion, smallFieldRegion]
  constructor
  · rintro (_ | _) <;> trivial
  · intro _
    by_cases h : t ≤ |f x|
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge h)

theorem largeSmallDisjoint {d k : ℕ} (f : LatticeSite d k → ℝ) (t : ℝ) :
    Disjoint (largeFieldRegion f t) (smallFieldRegion f t) := by
  apply Finset.disjoint_left.mpr
  intro x hxL hxS
  simp [largeFieldRegion, smallFieldRegion] at hxL hxS
  linarith

end

end YangMills.ClayCore
