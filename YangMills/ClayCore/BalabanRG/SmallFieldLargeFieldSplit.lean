import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanBlockingMap
import YangMills.ClayCore.BalabanRG.BalabanFieldSpace

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# SmallFieldLargeFieldSplit — Layer 11D (v0.9.1)

Structural decomposition of the Balaban RG blocking map.
Now includes geometric field predicates from Layer 15A (BalabanFieldSpace).

## Two-tier design
- ActivityFamily tier: RGFieldSplit, trivialRGFieldSplit (skeleton)
- Field configuration tier: SmallFieldPredicateField, LargeFieldPredicateField (15B)
-/

noncomputable section

-- v0.8.x compatibility: abstract predicates (True placeholders)
def SmallFieldPredicate (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ) : Prop := True
def LargeFieldPredicate (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ) : Prop := True

/-- Decomposition of the RG blocking map into small-field and large-field parts. -/
structure RGFieldSplit (d N_c : ℕ) [NeZero N_c] (k : ℕ) where
  smallPart : ActivityFamily d k → ActivityFamily d (k + 1)
  largePart : ActivityFamily d k → ActivityFamily d (k + 1)
  split_eq  : ∀ K, RGBlockingMap d N_c k K = fun p => smallPart K p + largePart K p

/-- Canonical trivial split: all in small part, large part zero. -/
def trivialRGFieldSplit (d N_c : ℕ) [NeZero N_c] (k : ℕ) : RGFieldSplit d N_c k where
  smallPart := RGBlockingMap d N_c k
  largePart := fun _ _ => 0
  split_eq  := fun K => by funext p; simp

theorem trivialRGFieldSplit_large_zero {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (K : ActivityFamily d k) :
    (trivialRGFieldSplit d N_c k).largePart K = fun _ => 0 := rfl

theorem trivialRGFieldSplit_small_eq {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (K : ActivityFamily d k) :
    (trivialRGFieldSplit d N_c k).smallPart K = RGBlockingMap d N_c k K := rfl

theorem rg_blocking_map_eq_small_add_large {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (hsplit : RGFieldSplit d N_c k) (K : ActivityFamily d k) :
    RGBlockingMap d N_c k K = fun p => hsplit.smallPart K p + hsplit.largePart K p :=
  hsplit.split_eq K

/-!
## Layer 15B: Geometric field predicates

Operating on φ : BalabanLatticeSite d k → ℝ (distinct from ActivityFamily).
-/

/-- Threshold for small/large field classification. Placeholder: 1. -/
def fieldThreshold (β : ℝ) : ℝ := 1

/-- φ is small if all sites are below threshold. -/
def SmallFieldPredicateField (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ) : Prop :=
  balabanLargeFieldRegion φ (fieldThreshold β) = ∅

/-- φ is large if some site exceeds threshold. -/
def LargeFieldPredicateField (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ) : Prop :=
  balabanLargeFieldRegion φ (fieldThreshold β) ≠ ∅

/-- Every field is either small or large. 0 sorrys. -/
theorem small_or_large_field (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ) :
    SmallFieldPredicateField d N_c k β φ ∨
    LargeFieldPredicateField d N_c k β φ := by
  unfold SmallFieldPredicateField LargeFieldPredicateField
  by_cases h : balabanLargeFieldRegion φ (fieldThreshold β) = ∅
  · exact Or.inl h
  · exact Or.inr h

/-- Large implies not small. 0 sorrys. -/
theorem not_small_of_large_field (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ)
    (hL : LargeFieldPredicateField d N_c k β φ) :
    ¬ SmallFieldPredicateField d N_c k β φ := by
  unfold SmallFieldPredicateField LargeFieldPredicateField at *; simpa using hL

/-- Not small implies large. 0 sorrys. -/
theorem large_of_not_small_field (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ)
    (hS : ¬ SmallFieldPredicateField d N_c k β φ) :
    LargeFieldPredicateField d N_c k β φ := by
  unfold SmallFieldPredicateField LargeFieldPredicateField at *; simpa using hS

/-- Small field iff all sites below threshold. 0 sorrys. -/
theorem smallField_iff {d N_c : ℕ} [NeZero N_c] {k : ℕ} {β : ℝ}
    (φ : BalabanLatticeSite d k → ℝ) :
    SmallFieldPredicateField d N_c k β φ ↔
      ∀ x : BalabanLatticeSite d k, |φ x| < fieldThreshold β := by
  unfold SmallFieldPredicateField
  constructor
  · intro h x
    by_contra hx
    have hxmem : x ∈ balabanLargeFieldRegion φ (fieldThreshold β) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, not_lt.mp hx⟩
    simpa [h] using hxmem
  · intro h
    ext x
    simp [balabanLargeFieldRegion, h x, not_le]

end

end YangMills.ClayCore
