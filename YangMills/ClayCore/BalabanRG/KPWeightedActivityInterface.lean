import Mathlib
import YangMills.ClayCore.BalabanRG.ExpPolymerSizeWeightKPActivity

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPWeightedActivityInterface — (v1.0.17-alpha repair)

Abstract KP-side weighted-activity interface.

Conservative design:
- define the abstract KP weight API on `Polymer d L`,
- define the two abstract weighted activity statements we use,
- specialize the API to the exponential polymer-size weight,
- provide compatibility aliases for the old native exp-size-weight names.

This file does **not** redeclare `kpExpSizeWeight` or its structural lemmas;
those live in `ExpPolymerSizeWeightKP.lean`.
-/

noncomputable section

/-- Abstract KP-side polymer weight. -/
abbrev KPWeight (d : ℕ) (L : ℤ) :=
  Polymer d L → ℝ

/-- Pointwise nonnegativity of a KP weight. -/
def KPWeightNonneg (d : ℕ) (L : ℤ) (w : KPWeight d L) : Prop :=
  ∀ X, 0 ≤ w X

/-- Pointwise lower bound `1 ≤ w(X)`. -/
def KPWeightGeOne (d : ℕ) (L : ℤ) (w : KPWeight d L) : Prop :=
  ∀ X, 1 ≤ w X

/-- Abstract KP pointwise decay through a weight. -/
def KPPointwiseWeightBound
    (d : ℕ) (L : ℤ)
    (K : Activity d L) (a : ℝ) (w : KPWeight d L) : Prop :=
  ∀ X, |K X| ≤ a / w X

/-- Abstract KP weighted-activity smallness statement. -/
def KPWeightedActivityBound
    (d : ℕ) (L : ℤ)
    (K : Activity d L) (a : ℝ) (w : KPWeight d L) : Prop :=
  ∀ X, |K X| * w X ≤ a

/-! ## First concrete instance: exponential polymer-size weight -/

/-- The KP exponential polymer-size weight is nonnegative. -/
theorem kpExpSizeWeight_nonneg_interface
    {d : ℕ} {L : ℤ} (a : ℝ) :
    KPWeightNonneg d L (kpExpSizeWeight a d L) := by
  intro X
  exact kpExpSizeWeight_nonneg (d := d) (L := L) a X

/-- The KP exponential polymer-size weight satisfies `1 ≤ w` for `a ≥ 0`. -/
theorem kpExpSizeWeight_ge_one_interface
    {d : ℕ} {L : ℤ} (a : ℝ) (ha : 0 ≤ a) :
    KPWeightGeOne d L (kpExpSizeWeight a d L) := by
  intro X
  exact kpExpSizeWeight_ge_one (d := d) (L := L) a ha X

/-- Native KP pointwise bound, packaged through the abstract interface. -/
theorem kpPointwiseWeightBound_expSizeWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ)
    (hKP : KoteckyPreiss K a) :
    KPPointwiseWeightBound d L K a (kpExpSizeWeight a d L) := by
  intro X
  exact kp_activity_bound_via_expSizeWeight K a hKP X

/-- Native KP weighted smallness, packaged through the abstract interface. -/
theorem kpWeightedActivityBound_expSizeWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ)
    (hKP : KoteckyPreiss K a) :
    KPWeightedActivityBound d L K a (kpExpSizeWeight a d L) := by
  intro X
  exact kp_weighted_activity_bound_via_expSizeWeight K a hKP X

/-! ## Compatibility aliases for the old native names -/

/-- Old native alias: scale-specialized pointwise exp-size-weight KP bound. -/
theorem kp_activity_bound_via_expSizeWeight_native
    {d k : ℕ}
    (K : Activity d (Int.ofNat k)) (a : ℝ)
    (hKP : KoteckyPreiss K a)
    (X : Polymer d (Int.ofNat k)) :
    |K X| ≤ a / expSizeWeight a d k X := by
  exact kp_activity_bound_div_expSizeWeight_nat K a hKP X

/-- Old native alias: scale-specialized weighted exp-size-weight KP bound. -/
theorem kp_activity_bound_weighted_native
    {d k : ℕ}
    (K : Activity d (Int.ofNat k)) (a : ℝ)
    (hKP : KoteckyPreiss K a)
    (X : Polymer d (Int.ofNat k)) :
    |K X| * expSizeWeight a d k X ≤ a := by
  exact kp_weighted_activity_bound_expSizeWeight_nat K a hKP X

end

end YangMills.ClayCore
