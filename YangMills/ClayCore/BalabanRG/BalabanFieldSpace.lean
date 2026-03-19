import Mathlib

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# BalabanFieldSpace — Layer 15A (v0.9.1)

Geometric foundation for Bałaban's RG program.
All names prefixed with 'Balaban' to avoid DAG collisions.
Leaf file. No imports from analytic chain.
-/

noncomputable section

/-- A site in the d-dimensional lattice at scale k. -/
abbrev BalabanLatticeSite (d k : ℕ) : Type := Fin (2 ^ k) × Fin d

instance (d k : ℕ) : Fintype (BalabanLatticeSite d k) := by
  dsimp [BalabanLatticeSite]; infer_instance

instance (d k : ℕ) : DecidableEq (BalabanLatticeSite d k) := by
  dsimp [BalabanLatticeSite]; infer_instance

/-- A region at scale k is a finite set of sites. -/
abbrev BalabanRegion (d k : ℕ) : Type := Finset (BalabanLatticeSite d k)

/-- A Bałaban block at scale k. -/
structure BalabanBlock (d k : ℕ) where
  center : BalabanLatticeSite d k
  sites  : BalabanRegion d k
deriving DecidableEq

/-- Support of a field f : BalabanLatticeSite d k → ℝ. -/
def balabanFieldSupport {d k : ℕ} (f : BalabanLatticeSite d k → ℝ) :
    Finset (BalabanLatticeSite d k) :=
  Finset.univ.filter (fun x => f x ≠ 0)

theorem balabanFieldSupport_empty_iff {d k : ℕ} (f : BalabanLatticeSite d k → ℝ) :
    balabanFieldSupport f = ∅ ↔ ∀ x, f x = 0 := by
  constructor
  · intro h x
    by_contra hx
    have hxmem : x ∈ balabanFieldSupport f :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
    simpa [h] using hxmem
  · intro h; ext x; simp [balabanFieldSupport, h x]

/-- A field is supported in R. -/
def balabanSupportedIn {d k : ℕ} (f : BalabanLatticeSite d k → ℝ)
    (R : BalabanRegion d k) : Prop :=
  balabanFieldSupport f ⊆ R

/-- Block partition placeholder. -/
def isBalabanBlockPartition (d k : ℕ) (blocks : Finset (BalabanBlock d k)) : Prop :=
  ∀ x : BalabanLatticeSite d k, ∃ B, B ∈ blocks ∧ x ∈ B.sites

/-- Large-field region at threshold t. -/
def balabanLargeFieldRegion {d k : ℕ} (f : BalabanLatticeSite d k → ℝ) (t : ℝ) :
    Finset (BalabanLatticeSite d k) :=
  Finset.univ.filter (fun x => t ≤ |f x|)

/-- Small-field region at threshold t. -/
def balabanSmallFieldRegion {d k : ℕ} (f : BalabanLatticeSite d k → ℝ) (t : ℝ) :
    Finset (BalabanLatticeSite d k) :=
  Finset.univ.filter (fun x => |f x| < t)

theorem balabanLargeSmallPartition {d k : ℕ} (f : BalabanLatticeSite d k → ℝ) (t : ℝ) :
    balabanLargeFieldRegion f t ∪ balabanSmallFieldRegion f t = Finset.univ := by
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    balabanLargeFieldRegion, balabanSmallFieldRegion]
  constructor
  · rintro (_ | _) <;> trivial
  · intro _
    by_cases h : t ≤ |f x|
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge h)

theorem balabanLargeSmallDisjoint {d k : ℕ} (f : BalabanLatticeSite d k → ℝ) (t : ℝ) :
    Disjoint (balabanLargeFieldRegion f t) (balabanSmallFieldRegion f t) := by
  apply Finset.disjoint_left.mpr
  intro x hxL hxS
  simp [balabanLargeFieldRegion, balabanSmallFieldRegion] at hxL hxS
  linarith

end

end YangMills.ClayCore
