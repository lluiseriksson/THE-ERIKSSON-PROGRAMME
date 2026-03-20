import Mathlib
import YangMills.ClayCore.BalabanRG.ExpPolymerSizeWeightKP
import YangMills.ClayCore.BalabanRG.PolymerCombinatorics

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ExpPolymerSizeWeightKPActivity — (v1.0.15-alpha Phase 2)

First KP-facing activity bounds rewritten through the exponential polymer-size weight

  w_a(X) = exp(a * |X|).

This phase stays conservative:
- no bridge API changes,
- no new high-level alias,
- just the direct pointwise KP consequences in the exp-weight language.
-/

noncomputable section

/-- Native KP activity bound rewritten in exponential-weight form.
0 sorrys. -/
theorem kp_activity_bound_via_expSizeWeight_native
    {d : ℕ} {L : ℤ} (K : Activity d L) (a : ℝ)
    (hKP : KoteckyPreiss K a) (X : Polymer d L) :
    |K X| ≤ a * (Real.exp (a * (X.size : ℝ)))⁻¹ := by
  calc
    |K X| ≤ a * Real.exp (-a * (X.size : ℝ)) := kp_activity_bound K a hKP X
    _ = a * (Real.exp (a * (X.size : ℝ)))⁻¹ := by
        exact kp_decay_factor_native_rewrite (a := a) X

/-- Scale-specialized KP activity bound rewritten via `expSizeWeight`.
0 sorrys. -/
theorem kp_activity_bound_via_expSizeWeight
    {d k : ℕ} (K : ActivityFamily d k) (a : ℝ)
    (hKP : KoteckyPreiss K a) (X : Polymer d (Int.ofNat k)) :
    |K X| ≤ a / expSizeWeight a d k X := by
  calc
    |K X| ≤ a * (Real.exp (a * (X.size : ℝ)))⁻¹ := by
      exact kp_activity_bound_via_expSizeWeight_native
        (d := d) (L := Int.ofNat k) K a hKP X
    _ = a / expSizeWeight a d k X := by
      rw [expSizeWeight]
      rw [div_eq_mul_inv]

/-- Native weighted-smallness form of the KP activity bound:
`|K X| * exp(a|X|) ≤ a`. 0 sorrys. -/
theorem kp_activity_bound_weighted_native
    {d : ℕ} {L : ℤ} (K : Activity d L) (a : ℝ)
    (hKP : KoteckyPreiss K a) (X : Polymer d L) :
    |K X| * Real.exp (a * (X.size : ℝ)) ≤ a := by
  have hbase : |K X| ≤ a * Real.exp (-a * (X.size : ℝ)) :=
    kp_activity_bound K a hKP X
  have hexp_nonneg : 0 ≤ Real.exp (a * (X.size : ℝ)) := by
    exact le_of_lt (Real.exp_pos _)
  calc
    |K X| * Real.exp (a * (X.size : ℝ))
      ≤ (a * Real.exp (-a * (X.size : ℝ))) * Real.exp (a * (X.size : ℝ)) :=
        mul_le_mul_of_nonneg_right hbase hexp_nonneg
    _ = a * (Real.exp (-a * (X.size : ℝ)) * Real.exp (a * (X.size : ℝ))) := by
        ring
    _ = a * Real.exp ((-a * (X.size : ℝ)) + (a * (X.size : ℝ))) := by
        rw [← Real.exp_add]
    _ = a * Real.exp 0 := by
        congr 1
        ring
    _ = a := by
        simp

/-- Scale-specialized weighted-smallness form:
`|K X| * w_a(X) ≤ a`. 0 sorrys. -/
theorem kp_activity_bound_weighted
    {d k : ℕ} (K : ActivityFamily d k) (a : ℝ)
    (hKP : KoteckyPreiss K a) (X : Polymer d (Int.ofNat k)) :
    |K X| * expSizeWeight a d k X ≤ a := by
  simpa [expSizeWeight] using
    (kp_activity_bound_weighted_native
      (d := d) (L := Int.ofNat k) K a hKP X)

end

end YangMills.ClayCore
