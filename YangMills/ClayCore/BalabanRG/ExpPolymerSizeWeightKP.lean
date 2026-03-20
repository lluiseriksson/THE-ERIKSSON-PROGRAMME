import Mathlib
import YangMills.ClayCore.BalabanRG.ExpPolymerSizeWeight

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ExpPolymerSizeWeightKP — (v1.0.17-alpha repair)

Purely structural lemmas for the exponential polymer-size weight.

Important design choice:
- this file stays independent of the abstract KP interfaces,
- the bridge to `KPWeightGeOne` lives in a separate file
  `ExpPolymerSizeWeightKPBridge.lean`,
- this prevents import cycles of the form

    KPWeightedActivityInterface
      -> ExpPolymerSizeWeightKPActivity
      -> ExpPolymerSizeWeightKP
      -> KPWeightedActivityInterface.
-/

noncomputable section

theorem expSizeWeight_apply
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    expSizeWeight a d k X = Real.exp (a * (X.size : ℝ)) := rfl

theorem expSizeWeight_pos
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    0 < expSizeWeight a d k X := by
  simpa [expSizeWeight] using (Real.exp_pos (a * (X.size : ℝ)))

theorem expSizeWeight_nonneg_at
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    0 ≤ expSizeWeight a d k X := by
  exact le_of_lt (expSizeWeight_pos (d := d) (k := k) a X)

theorem expSizeWeight_zero_param
    {d k : ℕ} (X : Polymer d (Int.ofNat k)) :
    expSizeWeight 0 d k X = 1 := by
  simp [expSizeWeight]

theorem expSizeWeight_ge_one_at
    {d k : ℕ} (a : ℝ) (ha : 0 ≤ a) (X : Polymer d (Int.ofNat k)) :
    1 ≤ expSizeWeight a d k X := by
  have hsize : (0 : ℝ) ≤ (X.size : ℝ) := by
    exact_mod_cast Nat.zero_le X.size
  have hmul : 0 ≤ a * (X.size : ℝ) := mul_nonneg ha hsize
  have hone : Real.exp 0 ≤ Real.exp (a * (X.size : ℝ)) := by
    exact Real.exp_le_exp.mpr hmul
  simpa [expSizeWeight] using hone

theorem one_le_expSizeWeight_of_nonneg
    {d k : ℕ} (a : ℝ) (ha : 0 ≤ a) (X : Polymer d (Int.ofNat k)) :
    1 ≤ expSizeWeight a d k X := by
  simpa using expSizeWeight_ge_one_at (d := d) (k := k) a ha X

theorem expSizeWeight_mono_param
    {d k : ℕ} {a b : ℝ} (hab : a ≤ b) (X : Polymer d (Int.ofNat k)) :
    expSizeWeight a d k X ≤ expSizeWeight b d k X := by
  have hsize : (0 : ℝ) ≤ (X.size : ℝ) := by
    exact_mod_cast Nat.zero_le X.size
  have hmul : a * (X.size : ℝ) ≤ b * (X.size : ℝ) := by
    exact mul_le_mul_of_nonneg_right hab hsize
  simpa [expSizeWeight] using (Real.exp_le_exp.mpr hmul)

theorem expSizeWeight_add_param
    {d k : ℕ} (a b : ℝ) (X : Polymer d (Int.ofNat k)) :
    expSizeWeight (a + b) d k X =
      expSizeWeight a d k X * expSizeWeight b d k X := by
  have hmul : (a + b) * (X.size : ℝ) = a * (X.size : ℝ) + b * (X.size : ℝ) := by
    ring
  rw [expSizeWeight, expSizeWeight, expSizeWeight, hmul, Real.exp_add]

theorem expSizeWeight_neg_param
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    expSizeWeight (-a) d k X = (expSizeWeight a d k X)⁻¹ := by
  have hneg : (-a) * (X.size : ℝ) = -(a * (X.size : ℝ)) := by
    ring
  rw [expSizeWeight, hneg, Real.exp_neg, expSizeWeight]

theorem kp_decay_factor_eq_inv_expSizeWeight
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    Real.exp (-a * (X.size : ℝ)) = (expSizeWeight a d k X)⁻¹ := by
  have hneg : -a * (X.size : ℝ) = -(a * (X.size : ℝ)) := by
    ring
  rw [hneg, Real.exp_neg, expSizeWeight]

theorem kp_decay_factor_mul_eq_div_expSizeWeight
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    a * Real.exp (-a * (X.size : ℝ)) = a / expSizeWeight a d k X := by
  rw [kp_decay_factor_eq_inv_expSizeWeight (d := d) (k := k) a X]
  rw [div_eq_mul_inv]

theorem kp_decay_factor_native_rewrite
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    a * Real.exp (-a * (X.size : ℝ)) = a / expSizeWeight a d k X := by
  exact kp_decay_factor_mul_eq_div_expSizeWeight (d := d) (k := k) a X

/-- KP-side exponential polymer-size weight on `Polymer d L`. -/
abbrev kpExpSizeWeight (a : ℝ) (d : ℕ) (L : ℤ) : Polymer d L → ℝ :=
  fun X => Real.exp (a * (X.size : ℝ))

theorem kpExpSizeWeight_apply
    {d : ℕ} {L : ℤ} (a : ℝ) (X : Polymer d L) :
    kpExpSizeWeight a d L X = Real.exp (a * (X.size : ℝ)) := rfl

theorem kpExpSizeWeight_pos
    {d : ℕ} {L : ℤ} (a : ℝ) (X : Polymer d L) :
    0 < kpExpSizeWeight a d L X := by
  simpa [kpExpSizeWeight] using (Real.exp_pos (a * (X.size : ℝ)))

theorem kpExpSizeWeight_nonneg
    {d : ℕ} {L : ℤ} (a : ℝ) (X : Polymer d L) :
    0 ≤ kpExpSizeWeight a d L X := by
  exact le_of_lt (kpExpSizeWeight_pos (d := d) (L := L) a X)

theorem kpExpSizeWeight_ge_one
    {d : ℕ} {L : ℤ} (a : ℝ) (ha : 0 ≤ a) (X : Polymer d L) :
    1 ≤ kpExpSizeWeight a d L X := by
  have hsize : (0 : ℝ) ≤ (X.size : ℝ) := by
    exact_mod_cast Nat.zero_le X.size
  have hmul : 0 ≤ a * (X.size : ℝ) := mul_nonneg ha hsize
  have hone : Real.exp 0 ≤ Real.exp (a * (X.size : ℝ)) := by
    exact Real.exp_le_exp.mpr hmul
  simpa [kpExpSizeWeight] using hone

end

end YangMills.ClayCore
