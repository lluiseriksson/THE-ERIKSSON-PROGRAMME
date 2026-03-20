import Mathlib
import YangMills.ClayCore.BalabanRG.ExpPolymerSizeWeightKP
import YangMills.ClayCore.BalabanRG.PolymerCombinatorics

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ExpPolymerSizeWeightKPActivity — (v1.0.17-alpha repair)

Conservative KP-activity rewrite through the exponential polymer-size weight.

This file intentionally depends only on:
- `PolymerCombinatorics` for the native KP pointwise bound, and
- `ExpPolymerSizeWeightKP` for the structural exponential-weight lemmas.

No abstract KP interface is imported here. This keeps the dependency graph acyclic.
-/

noncomputable section

/-- Native KP pointwise bound rewritten as division by the KP-side exponential
size weight. -/
theorem kp_activity_bound_div_expSizeWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ)
    (hKP : KoteckyPreiss K a)
    (X : Polymer d L) :
    |K X| ≤ a / kpExpSizeWeight a d L X := by
  calc
    |K X| ≤ a * Real.exp (-a * (X.size : ℝ)) := kp_activity_bound K a hKP X
    _ = a / kpExpSizeWeight a d L X := by
      rw [kpExpSizeWeight, div_eq_mul_inv, ← Real.exp_neg]
      congr 1
      ring

/-- Same pointwise KP bound, exposed under a shorter name. -/
theorem kp_activity_bound_via_expSizeWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ)
    (hKP : KoteckyPreiss K a)
    (X : Polymer d L) :
    |K X| ≤ a / kpExpSizeWeight a d L X :=
  kp_activity_bound_div_expSizeWeight K a hKP X

/-- Weighted smallness form of the native KP pointwise bound:
`|K X| * w_a(X) ≤ a`. -/
theorem kp_weighted_activity_bound_expSizeWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ)
    (hKP : KoteckyPreiss K a)
    (X : Polymer d L) :
    |K X| * kpExpSizeWeight a d L X ≤ a := by
  have hdiv :
      |K X| ≤ a / kpExpSizeWeight a d L X :=
    kp_activity_bound_div_expSizeWeight K a hKP X
  have hwpos : 0 < kpExpSizeWeight a d L X :=
    kpExpSizeWeight_pos (d := d) (L := L) a X
  have hm :
      |K X| * kpExpSizeWeight a d L X ≤
        (a / kpExpSizeWeight a d L X) * kpExpSizeWeight a d L X :=
    mul_le_mul_of_nonneg_right hdiv (le_of_lt hwpos)
  have hwne : kpExpSizeWeight a d L X ≠ 0 := ne_of_gt hwpos
  calc
    |K X| * kpExpSizeWeight a d L X
      ≤ (a / kpExpSizeWeight a d L X) * kpExpSizeWeight a d L X := hm
    _ = a := by
      rw [div_eq_mul_inv]
      calc
        (a * (kpExpSizeWeight a d L X)⁻¹) * kpExpSizeWeight a d L X
            = a * ((kpExpSizeWeight a d L X)⁻¹ * kpExpSizeWeight a d L X) := by ring
        _ = a * 1 := by rw [inv_mul_cancel₀ hwne]
        _ = a := by ring

/-- Alias with the same weighted smallness statement. -/
theorem kp_weighted_activity_bound_via_expSizeWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ)
    (hKP : KoteckyPreiss K a)
    (X : Polymer d L) :
    |K X| * kpExpSizeWeight a d L X ≤ a :=
  kp_weighted_activity_bound_expSizeWeight K a hKP X

/-- Scale-specialized version on `L = Int.ofNat k`. -/
theorem kp_activity_bound_div_expSizeWeight_nat
    {d k : ℕ}
    (K : Activity d (Int.ofNat k)) (a : ℝ)
    (hKP : KoteckyPreiss K a)
    (X : Polymer d (Int.ofNat k)) :
    |K X| ≤ a / expSizeWeight a d k X := by
  simpa [kpExpSizeWeight, expSizeWeight] using
    (kp_activity_bound_div_expSizeWeight
      (d := d) (L := Int.ofNat k) K a hKP X)

/-- Scale-specialized weighted smallness form. -/
theorem kp_weighted_activity_bound_expSizeWeight_nat
    {d k : ℕ}
    (K : Activity d (Int.ofNat k)) (a : ℝ)
    (hKP : KoteckyPreiss K a)
    (X : Polymer d (Int.ofNat k)) :
    |K X| * expSizeWeight a d k X ≤ a := by
  simpa [kpExpSizeWeight, expSizeWeight] using
    (kp_weighted_activity_bound_expSizeWeight
      (d := d) (L := Int.ofNat k) K a hKP X)

/-- Native exponential-decay factor rewritten directly in scale language. -/
theorem kp_decay_factor_mul_eq_div_expSizeWeight_nat
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    a * Real.exp (-a * (X.size : ℝ)) = a / expSizeWeight a d k X := by
  exact kp_decay_factor_mul_eq_div_expSizeWeight (d := d) (k := k) a X

end

end YangMills.ClayCore
