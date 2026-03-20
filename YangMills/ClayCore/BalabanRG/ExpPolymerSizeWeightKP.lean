import Mathlib
import YangMills.ClayCore.BalabanRG.ExpPolymerSizeWeight

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ExpPolymerSizeWeightKP — (v1.0.15-alpha Phase 1)

Structural lemmas for the KP-shaped exponential polymer-size weight

  w_a(X) = exp(a * |X|).

This phase is deliberately conservative:
- no new bridge API,
- no new high-level alias,
- just reusable weight algebra for later KP-facing work.
-/

noncomputable section

/-- Unfolded form of the exponential size weight. 0 sorrys. -/
theorem expSizeWeight_apply
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    expSizeWeight a d k X = Real.exp (a * (X.size : ℝ)) := rfl

/-- Positivity of the exponential size weight. 0 sorrys. -/
theorem expSizeWeight_pos
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    0 < expSizeWeight a d k X := by
  simpa [expSizeWeight] using (Real.exp_pos (a * (X.size : ℝ)))

/-- Nonnegativity of the exponential size weight. 0 sorrys. -/
theorem expSizeWeight_nonneg_at
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    0 ≤ expSizeWeight a d k X := by
  exact le_of_lt (expSizeWeight_pos (d := d) (k := k) a X)

/-- At parameter `a = 0`, the exponential size weight is identically `1`.
0 sorrys. -/
theorem expSizeWeight_zero_param
    {d k : ℕ} (X : Polymer d (Int.ofNat k)) :
    expSizeWeight 0 d k X = 1 := by
  simp [expSizeWeight]

/-- For nonnegative `a`, the exponential size weight is at least `1`.
Fixed-scale form. 0 sorrys. -/
theorem expSizeWeight_ge_one_at
    {d k : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (X : Polymer d (Int.ofNat k)) :
    1 ≤ expSizeWeight a d k X := by
  have hsize : 0 ≤ (X.size : ℝ) := by
    exact_mod_cast (Nat.zero_le X.size)
  have harg : 0 ≤ a * (X.size : ℝ) := mul_nonneg ha hsize
  have hone : 1 ≤ Real.exp (a * (X.size : ℝ)) := by
    nlinarith [Real.add_one_le_exp (a * (X.size : ℝ))]
  simpa [expSizeWeight] using hone

/-- Alternate name for the same lower bound. 0 sorrys. -/
theorem one_le_expSizeWeight_of_nonneg
    {d k : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (X : Polymer d (Int.ofNat k)) :
    1 ≤ expSizeWeight a d k X := by
  simpa using expSizeWeight_ge_one_at (d := d) (k := k) ha X

/-- Monotonicity of the exponential size weight in the parameter `a`.
0 sorrys. -/
theorem expSizeWeight_mono_param
    {d k : ℕ} {a b : ℝ}
    (hab : a ≤ b) (X : Polymer d (Int.ofNat k)) :
    expSizeWeight a d k X ≤ expSizeWeight b d k X := by
  have hsize : 0 ≤ (X.size : ℝ) := by
    exact_mod_cast (Nat.zero_le X.size)
  have hmul : a * (X.size : ℝ) ≤ b * (X.size : ℝ) := by
    exact mul_le_mul_of_nonneg_right hab hsize
  simpa [expSizeWeight] using (Real.exp_le_exp.mpr hmul)

/-- Exponential size weights add in the parameter:
`w_(a+b)(X) = w_a(X) * w_b(X)`. 0 sorrys. -/
theorem expSizeWeight_add_param
    {d k : ℕ} (a b : ℝ) (X : Polymer d (Int.ofNat k)) :
    expSizeWeight (a + b) d k X =
      expSizeWeight a d k X * expSizeWeight b d k X := by
  have hmul : (a + b) * (X.size : ℝ) = a * (X.size : ℝ) + b * (X.size : ℝ) := by
    ring
  rw [expSizeWeight, expSizeWeight, expSizeWeight, hmul, Real.exp_add]

/-- Exponential size weight at `-a` is the inverse of the weight at `a`.
0 sorrys. -/
theorem expSizeWeight_neg_param
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    expSizeWeight (-a) d k X = (expSizeWeight a d k X)⁻¹ := by
  have hneg : (-a) * (X.size : ℝ) = -(a * (X.size : ℝ)) := by
    ring
  rw [expSizeWeight, hneg, Real.exp_neg, expSizeWeight]

/-- The KP decay factor is exactly the inverse of the exponential size weight.
0 sorrys. -/
theorem kp_decay_factor_eq_inv_expSizeWeight
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    Real.exp (-a * (X.size : ℝ)) = (expSizeWeight a d k X)⁻¹ := by
  have hneg : -a * (X.size : ℝ) = -(a * (X.size : ℝ)) := by
    ring
  rw [hneg, Real.exp_neg, expSizeWeight]

/-- Equivalent rewrite:
`a * exp(-a|X|) = a / w_a(X)`. 0 sorrys. -/
theorem kp_decay_factor_mul_eq_div_expSizeWeight
    {d k : ℕ} (a : ℝ) (X : Polymer d (Int.ofNat k)) :
    a * Real.exp (-a * (X.size : ℝ)) = a / expSizeWeight a d k X := by
  rw [kp_decay_factor_eq_inv_expSizeWeight (d := d) (k := k) a X]
  rw [div_eq_mul_inv]

/-- Native KP decay-factor rewrite in the exponential-weight shape.
This is the algebraic bridge needed for the next phase. 0 sorrys. -/
theorem kp_decay_factor_native_rewrite
    {d : ℕ} {L : ℤ} (a : ℝ) (X : Polymer d L) :
    a * Real.exp (-a * (X.size : ℝ)) =
      a * (Real.exp (a * (X.size : ℝ)))⁻¹ := by
  have hneg : -a * (X.size : ℝ) = -(a * (X.size : ℝ)) := by
    ring
  rw [hneg, Real.exp_neg]

end

end YangMills.ClayCore
