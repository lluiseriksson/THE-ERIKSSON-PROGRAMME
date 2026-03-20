import Mathlib
import YangMills.ClayCore.BalabanRG.ExpPolymerSizeWeightKPActivity

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPWeightedActivityInterface — (v1.0.16-alpha Phase 1)

Abstract KP-facing interface for polymer weights on the native
polymer combinatorics side.

This phase is conservative:
- it does not modify the existing KP chain,
- it does not refactor `KPFiniteTailBound` yet,
- it only introduces a reusable interface layer and shows that the
  exponential size weight fits it exactly.
-/

noncomputable section

/-- Native KP-side polymer weight at lattice scale `L : ℤ`. -/
abbrev KPPolymerWeight (d : ℕ) (L : ℤ) :=
  Polymer d L → ℝ

/-- Nonnegativity for a KP-side polymer weight. -/
def KPWeightNonneg (d : ℕ) (L : ℤ)
    (w : KPPolymerWeight d L) : Prop :=
  ∀ X, 0 ≤ w X

/-- Strict positivity for a KP-side polymer weight. -/
def KPWeightPos (d : ℕ) (L : ℤ)
    (w : KPPolymerWeight d L) : Prop :=
  ∀ X, 0 < w X

/-- Lower bound `1 ≤ w(X)` for every polymer. -/
def KPWeightGeOne (d : ℕ) (L : ℤ)
    (w : KPPolymerWeight d L) : Prop :=
  ∀ X, 1 ≤ w X

/-- Native KP weighted activity attached to an abstract polymer weight. -/
def KPWeightedActivity {d : ℕ} {L : ℤ}
    (K : Activity d L) (w : KPPolymerWeight d L)
    (X : Polymer d L) : ℝ :=
  |K X| * w X

/-- Nonnegativity of the weighted activity under a nonnegative weight.
0 sorrys. -/
theorem kpWeightedActivity_nonneg
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (w : KPPolymerWeight d L)
    (hw : KPWeightNonneg d L w) (X : Polymer d L) :
    0 ≤ KPWeightedActivity K w X := by
  unfold KPWeightedActivity
  exact mul_nonneg (abs_nonneg _) (hw X)

/-- Monotonicity in the weight. 0 sorrys. -/
theorem kpWeightedActivity_mono_right
    {d : ℕ} {L : ℤ}
    (K : Activity d L)
    {w₁ w₂ : KPPolymerWeight d L}
    (hmono : ∀ X, w₁ X ≤ w₂ X)
    (X : Polymer d L) :
    KPWeightedActivity K w₁ X ≤ KPWeightedActivity K w₂ X := by
  unfold KPWeightedActivity
  exact mul_le_mul_of_nonneg_left (hmono X) (abs_nonneg _)

/-- If `|K X| ≤ a / w(X)` and `w(X) > 0`, then the weighted activity
is bounded by `a`. 0 sorrys. -/
theorem kpWeightedActivity_le_of_activity_bound_div
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (w : KPPolymerWeight d L)
    (hwpos : KPWeightPos d L w)
    {a : ℝ} {X : Polymer d L}
    (hbound : |K X| ≤ a / w X) :
    KPWeightedActivity K w X ≤ a := by
  have hw0 : 0 < w X := hwpos X
  unfold KPWeightedActivity
  have hmul :
      |K X| * w X ≤ (a / w X) * w X :=
    mul_le_mul_of_nonneg_right hbound hw0.le
  have hsimp : (a / w X) * w X = a := by
    field_simp [hw0.ne']
  exact hmul.trans_eq hsimp

/-! ## Exponential size weight as a KP-side weight -/

/-- KP-side exponential size weight:
`w_a(X) = exp(a * |X|)`. -/
abbrev kpExpSizeWeight (a : ℝ) (d : ℕ) (L : ℤ) :
    KPPolymerWeight d L :=
  fun X => Real.exp (a * (X.size : ℝ))

/-- The KP exponential size weight is strictly positive. 0 sorrys. -/
theorem kpExpSizeWeight_pos
    {d : ℕ} {L : ℤ} (a : ℝ) :
    KPWeightPos d L (kpExpSizeWeight a d L) := by
  intro X
  exact Real.exp_pos _

/-- The KP exponential size weight is nonnegative. 0 sorrys. -/
theorem kpExpSizeWeight_nonneg
    {d : ℕ} {L : ℤ} (a : ℝ) :
    KPWeightNonneg d L (kpExpSizeWeight a d L) := by
  intro X
  exact le_of_lt (Real.exp_pos _)

/-- For `a ≥ 0`, the KP exponential size weight satisfies `1 ≤ w_a(X)`.
0 sorrys. -/
theorem kpExpSizeWeight_ge_one
    {d : ℕ} {L : ℤ} {a : ℝ} (ha : 0 ≤ a) :
    KPWeightGeOne d L (kpExpSizeWeight a d L) := by
  intro X
  have hsize : 0 ≤ (X.size : ℝ) := by
    exact_mod_cast (Nat.zero_le X.size)
  have harg : 0 ≤ a * (X.size : ℝ) := mul_nonneg ha hsize
  have hone : 1 ≤ Real.exp (a * (X.size : ℝ)) := by
    nlinarith [Real.add_one_le_exp (a * (X.size : ℝ))]
  simpa [kpExpSizeWeight] using hone

/-- The nat-scale `expSizeWeight` is exactly the KP exponential size weight
at `L = Int.ofNat k`. 0 sorrys. -/
theorem kpExpSizeWeight_eq_expSizeWeight
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    kpExpSizeWeight a d (Int.ofNat k) X = expSizeWeight a d k X := rfl

/-- The native KP pointwise activity bound rewritten through the abstract
KP weight interface. 0 sorrys. -/
theorem kp_activity_bound_via_kpExpSizeWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ)
    (hKP : KoteckyPreiss K a) (X : Polymer d L) :
    |K X| ≤ a / kpExpSizeWeight a d L X := by
  simpa [kpExpSizeWeight] using
    (kp_activity_bound_via_expSizeWeight_native
      (d := d) (L := L) K a hKP X)

/-- The native KP weighted smallness form rewritten through the abstract
KP weight interface. 0 sorrys. -/
theorem kp_weightedActivity_bound_via_kpExpSizeWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ)
    (hKP : KoteckyPreiss K a) (X : Polymer d L) :
    KPWeightedActivity K (kpExpSizeWeight a d L) X ≤ a := by
  simpa [KPWeightedActivity, kpExpSizeWeight] using
    (kp_activity_bound_weighted_native
      (d := d) (L := L) K a hKP X)

/-- A one-line abstract recovery of the weighted bound from the quotient form.
0 sorrys. -/
theorem kp_weightedActivity_bound_from_div_form
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ)
    (hKP : KoteckyPreiss K a) (X : Polymer d L) :
    KPWeightedActivity K (kpExpSizeWeight a d L) X ≤ a := by
  apply kpWeightedActivity_le_of_activity_bound_div
    (K := K) (w := kpExpSizeWeight a d L)
    (hwpos := kpExpSizeWeight_pos (d := d) (L := L) a)
  exact kp_activity_bound_via_kpExpSizeWeight K a hKP X

end

end YangMills.ClayCore
