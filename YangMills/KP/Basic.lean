/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# KP0 — polymer substrate and partition function

First milestone (KP0) of the Kotecký–Preiss cluster-expansion layer planned in
`docs/kp-cluster-expansion-plan.md`.  This is the foundation the whole layer (and,
through it, §5/§6.2 of the Eriksson paper) is built on.

We fix an **abstract hard-core polymer system**: a type of polymers with a
symmetric, reflexive *incompatibility* relation and complex *activities*.  A finite
family of polymers is *admissible* when its members are pairwise compatible, and the
finite-volume **partition function** sums the product of activities over admissible
subfamilies of a region.

Everything here is elementary `Finset` bookkeeping (KP0 = "low difficulty" in the
plan), but it is real, compiler-checked infrastructure, not a sketch.  The hard
parts — the cluster expansion and its KP convergence (KP2) and the exponential
clustering corollary (KP3) — come later and are the genuine work.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped Classical BigOperators

/-- An abstract hard-core polymer system with complex activities. -/
structure PolymerSystem where
  /-- The type of polymers (e.g. connected finite subsets of a lattice). -/
  Polymer : Type*
  /-- Incompatibility relation (e.g. polymers overlap or touch). -/
  incomp : Polymer → Polymer → Prop
  /-- Incompatibility is symmetric. -/
  incomp_symm : ∀ X Y, incomp X Y → incomp Y X
  /-- Hard core: every polymer is incompatible with itself. -/
  incomp_self : ∀ X, incomp X X
  /-- The activity `z(X)` of a polymer. -/
  activity : Polymer → ℂ

variable (P : PolymerSystem)

/-- A finite family of polymers is **admissible** if its members are pairwise
compatible (no two distinct members are incompatible). -/
def Admissible (S : Finset P.Polymer) : Prop :=
  ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → ¬ P.incomp X Y

/-- The empty family is admissible. -/
theorem admissible_empty : Admissible P (∅ : Finset P.Polymer) := by
  intro X hX
  simp at hX

/-- Admissibility is inherited by subfamilies. -/
theorem admissible_mono {S T : Finset P.Polymer} (h : S ⊆ T)
    (hT : Admissible P T) : Admissible P S :=
  fun X hX Y hY hne => hT X (h hX) Y (h hY) hne

/-- A singleton family is always admissible (hard core only forbids *distinct*
incompatible members). -/
theorem admissible_singleton (X : P.Polymer) :
    Admissible P ({X} : Finset P.Polymer) := by
  intro A hA B hB hne
  rw [Finset.mem_singleton] at hA hB
  exact absurd (hA.trans hB.symm) hne

/-- **Finite-volume partition function** `Ξ(Λ) = ∑_{S ⊆ Λ admissible} ∏_{X ∈ S} z(X)`. -/
noncomputable def partition (Λ : Finset P.Polymer) : ℂ :=
  ∑ S ∈ Λ.powerset.filter (Admissible P), ∏ X ∈ S, P.activity X

/-- The partition function of the empty region is `1` (the empty family contributes
the empty product). -/
theorem partition_empty : partition P ∅ = 1 := by
  rw [partition, Finset.powerset_empty]
  have hfilter : ({∅} : Finset (Finset P.Polymer)).filter (Admissible P) = {∅} := by
    apply Finset.filter_eq_self.mpr
    intro S hS
    rw [Finset.mem_singleton] at hS
    subst hS
    exact admissible_empty P
  rw [hfilter, Finset.sum_singleton, Finset.prod_empty]

/-- Single-polymer partition function: `Ξ({X}) = 1 + z(X)`.  The two admissible
subfamilies of `{X}` are `∅` (contributing `1`) and `{X}` (contributing `z(X)`).
This is the `n = 1` base case of the cluster expansion. -/
theorem partition_singleton (X : P.Polymer) :
    partition P ({X} : Finset P.Polymer) = 1 + P.activity X := by
  rw [partition]
  have hpow : ({X} : Finset P.Polymer).powerset = {∅, {X}} := by
    ext S
    rw [Finset.mem_powerset, Finset.subset_singleton_iff, Finset.mem_insert,
        Finset.mem_singleton]
  rw [hpow]
  have hfilter :
      ({∅, {X}} : Finset (Finset P.Polymer)).filter (Admissible P) = {∅, {X}} := by
    apply Finset.filter_eq_self.mpr
    intro S hS
    rw [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with h | h
    · subst h; exact admissible_empty P
    · subst h; exact admissible_singleton P X
  rw [hfilter, Finset.sum_pair (by simp), Finset.prod_empty, Finset.prod_singleton]

/-- **Admissibility splits over compatible blocks.**  If no polymer of `Λ₁` is
incompatible with any polymer of `Λ₂`, then a family drawn from `S₁ ⊆ Λ₁` and
`S₂ ⊆ Λ₂` is admissible iff each part is.  This is the combinatorial linchpin of
the partition-function factorization `Ξ(Λ₁ ∪ Λ₂) = Ξ(Λ₁)·Ξ(Λ₂)` (KP1). -/
theorem admissible_union_iff {Λ₁ Λ₂ : Finset P.Polymer}
    (hcross : ∀ X ∈ Λ₁, ∀ Y ∈ Λ₂, ¬ P.incomp X Y)
    {S₁ S₂ : Finset P.Polymer} (h1 : S₁ ⊆ Λ₁) (h2 : S₂ ⊆ Λ₂) :
    Admissible P (S₁ ∪ S₂) ↔ Admissible P S₁ ∧ Admissible P S₂ := by
  constructor
  · intro h
    exact ⟨admissible_mono P Finset.subset_union_left h,
           admissible_mono P Finset.subset_union_right h⟩
  · rintro ⟨hS1, hS2⟩ X hX Y hY hne
    rw [Finset.mem_union] at hX hY
    rcases hX with hX1 | hX2 <;> rcases hY with hY1 | hY2
    · exact hS1 X hX1 Y hY1 hne
    · exact hcross X (h1 hX1) Y (h2 hY2)
    · exact fun hc => hcross Y (h1 hY1) X (h2 hX2) (P.incomp_symm X Y hc)
    · exact hS2 X hX2 Y hY2 hne

end YangMills.KP
