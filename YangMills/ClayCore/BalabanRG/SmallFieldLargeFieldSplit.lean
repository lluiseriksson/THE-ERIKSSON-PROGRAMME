import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanBlockingMap
import YangMills.ClayCore.BalabanRG.BalabanFieldSpace

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# SmallFieldLargeFieldSplit — Layer 11D (v0.9.2)

Structural decomposition of the Balaban RG blocking map.
Physical threshold exp(-β/2) + parallel RGFieldSplitOnField.
-/

noncomputable section

-- v0.8.x compatibility
def SmallFieldPredicate (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ) : Prop := True
def LargeFieldPredicate (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ) : Prop := True

/-- Physical threshold: exp(-β/2). -/
def fieldThreshold (β : ℝ) : ℝ := Real.exp (-(β / 2))

theorem fieldThreshold_pos (β : ℝ) : 0 < fieldThreshold β := by
  unfold fieldThreshold; positivity

theorem fieldThreshold_nonneg (β : ℝ) : 0 ≤ fieldThreshold β :=
  le_of_lt (fieldThreshold_pos β)

theorem fieldThreshold_lt_one (β : ℝ) (hβ : 0 < β) :
    fieldThreshold β < 1 := by
  unfold fieldThreshold
  have hexp : Real.exp (-(β / 2)) < Real.exp 0 := by
    apply Real.exp_lt_exp.mpr; linarith
  simpa using hexp

/-- RG blocking map decomposition structure. -/
structure RGFieldSplit (d N_c : ℕ) [NeZero N_c] (k : ℕ) where
  smallPart : ActivityFamily d k → ActivityFamily d (k + 1)
  largePart : ActivityFamily d k → ActivityFamily d (k + 1)
  split_eq  : ∀ K, RGBlockingMap d N_c k K = fun p => smallPart K p + largePart K p

/-- Trivial split: large part zero. -/
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

/-! ## Layer 15B: Geometric field predicates -/

/-- φ is small if all sites are below threshold. -/
def SmallFieldPredicateField (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ) : Prop :=
  balabanLargeFieldRegion φ (fieldThreshold β) = ∅

/-- φ is large if some site exceeds threshold. -/
def LargeFieldPredicateField (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ) : Prop :=
  balabanLargeFieldRegion φ (fieldThreshold β) ≠ ∅

theorem small_or_large_field (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ) :
    SmallFieldPredicateField d N_c k β φ ∨
    LargeFieldPredicateField d N_c k β φ := by
  unfold SmallFieldPredicateField LargeFieldPredicateField
  by_cases h : balabanLargeFieldRegion φ (fieldThreshold β) = ∅
  · exact Or.inl h
  · exact Or.inr h

theorem not_small_of_large_field (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ)
    (hL : LargeFieldPredicateField d N_c k β φ) :
    ¬ SmallFieldPredicateField d N_c k β φ := by
  unfold SmallFieldPredicateField LargeFieldPredicateField at *; simpa using hL

theorem large_of_not_small_field (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ)
    (hS : ¬ SmallFieldPredicateField d N_c k β φ) :
    LargeFieldPredicateField d N_c k β φ := by
  unfold SmallFieldPredicateField LargeFieldPredicateField at *; simpa using hS

theorem smallField_iff {d N_c : ℕ} [NeZero N_c] {k : ℕ} {β : ℝ}
    (φ : BalabanLatticeSite d k → ℝ) :
    SmallFieldPredicateField d N_c k β φ ↔
      ∀ x : BalabanLatticeSite d k, |φ x| < fieldThreshold β := by
  unfold SmallFieldPredicateField balabanLargeFieldRegion
  constructor
  · intro h x
    by_contra hx
    have hxmem : x ∈ Finset.filter (fun x => fieldThreshold β ≤ |φ x|) Finset.univ := by
      simp
      exact not_lt.mp hx
    simpa [h] using hxmem
  · intro h; ext x; simp [h x]

/-! ## Layer 15B+: RGFieldSplitOnField -/

/-- Field-configuration-dependent RG split (parallel to skeleton). -/
structure RGFieldSplitOnField (d N_c : ℕ) [NeZero N_c] (k : ℕ) where
  smallPart :
    (BalabanLatticeSite d k → ℝ) → ActivityFamily d k → ActivityFamily d (k + 1)
  largePart :
    (BalabanLatticeSite d k → ℝ) → ActivityFamily d k → ActivityFamily d (k + 1)
  split_eq :
    ∀ φ K, RGBlockingMap d N_c k K = fun p =>
      smallPart φ K p + largePart φ K p

/-- Trivial field split: large part zero. -/
def trivialRGFieldSplitOnField (d N_c : ℕ) [NeZero N_c] (k : ℕ) :
    RGFieldSplitOnField d N_c k where
  smallPart := fun _ => RGBlockingMap d N_c k
  largePart := fun _ _ _ => 0
  split_eq := fun _ K => by funext p; simp

theorem small_field_large_part_trivial {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (β : ℝ) (φ : BalabanLatticeSite d k → ℝ) (K : ActivityFamily d k)
    (_ : SmallFieldPredicateField d N_c k β φ) :
    (trivialRGFieldSplitOnField d N_c k).largePart φ K = fun _ => 0 := rfl


/-! ## Layer 15C: Field selector and large-field norm -/

/-- Selector: returns the trivial split for now.
    API fixed for future non-trivial φ-dependent splits. -/
def selectFieldSplit (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ)
    (φ : BalabanLatticeSite d k → ℝ) :
    RGFieldSplitOnField d N_c k :=
  trivialRGFieldSplitOnField d N_c k

theorem selectFieldSplit_small_eq_trivial {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (β : ℝ) (φ : BalabanLatticeSite d k → ℝ)
    (_ : SmallFieldPredicateField d N_c k β φ) :
    selectFieldSplit d N_c k β φ = trivialRGFieldSplitOnField d N_c k := rfl

theorem selectFieldSplit_large_eq_trivial {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (β : ℝ) (φ : BalabanLatticeSite d k → ℝ)
    (_ : LargeFieldPredicateField d N_c k β φ) :
    selectFieldSplit d N_c k β φ = trivialRGFieldSplitOnField d N_c k := rfl

theorem selectFieldSplit_largePart_zero {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (β : ℝ) (φ : BalabanLatticeSite d k → ℝ) (K : ActivityFamily d k) :
    (selectFieldSplit d N_c k β φ).largePart φ K = fun _ => 0 := rfl

theorem selectFieldSplit_smallPart_eq_rg {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (β : ℝ) (φ : BalabanLatticeSite d k → ℝ) (K : ActivityFamily d k) :
    (selectFieldSplit d N_c k β φ).smallPart φ K = RGBlockingMap d N_c k K := rfl

/-- Discrete large-field norm: number of sites exceeding the threshold. -/
def largeFieldNorm {d k : ℕ} (φ : BalabanLatticeSite d k → ℝ) (β : ℝ) : ℝ :=
  ((balabanLargeFieldRegion φ (fieldThreshold β)).card : ℝ)

theorem largeFieldNorm_nonneg {d k : ℕ}
    (φ : BalabanLatticeSite d k → ℝ) (β : ℝ) :
    0 ≤ largeFieldNorm φ β := by
  unfold largeFieldNorm; positivity

theorem largeFieldNorm_eq_zero_iff {d k : ℕ}
    (φ : BalabanLatticeSite d k → ℝ) (β : ℝ) :
    largeFieldNorm φ β = 0 ↔
      balabanLargeFieldRegion φ (fieldThreshold β) = ∅ := by
  unfold largeFieldNorm
  simp [Finset.card_eq_zero]

theorem largeFieldNorm_zero_of_small {d N_c : ℕ} [NeZero N_c] {k : ℕ} {β : ℝ}
    (φ : BalabanLatticeSite d k → ℝ)
    (hS : SmallFieldPredicateField d N_c k β φ) :
    largeFieldNorm φ β = 0 := by
  rw [largeFieldNorm_eq_zero_iff]
  exact hS

theorem largeFieldNorm_pos_of_large {d N_c : ℕ} [NeZero N_c] {k : ℕ} {β : ℝ}
    (φ : BalabanLatticeSite d k → ℝ)
    (hL : LargeFieldPredicateField d N_c k β φ) :
    0 < largeFieldNorm φ β := by
  unfold largeFieldNorm LargeFieldPredicateField at *
  have hne : (balabanLargeFieldRegion φ (fieldThreshold β)).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hL
  exact_mod_cast Finset.card_pos.mpr hne



end

end YangMills.ClayCore
