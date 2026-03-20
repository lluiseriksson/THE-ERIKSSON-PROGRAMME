import Mathlib
import YangMills.ClayCore.BalabanRG.FullLargeFieldSuppressionSingleton

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# FullLargeFieldSingletonBound — (v1.0.8-alpha Phase 1)

Pointwise-to-singleton bridge for the full large-field bound.

This file does **not** claim a full analytic discharge yet.
Instead it factors the singleton P80 hypothesis through a simpler
pointwise bound:

  |K p₀| ≤ C · dist(K, 0)

and then upgrades it to the existing
`SingletonFullLargeFieldBound` when `C ≤ exp(-β)`.

This is the first honest reduction of analytic debt in the singleton path.
-/

noncomputable section

/-! ## Pointwise bridge hypothesis -/

/-- Minimal pointwise bridge: evaluation at `p₀` is controlled by
`C * ActivityNorm.dist K 0`. -/
def SingletonPointwiseBound (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (C : ℝ)
    (p₀ : Polymer d (Int.ofNat k)) : Prop :=
  ∀ (K : ActivityFamily d k),
    |K p₀| ≤ C * ActivityNorm.dist K (fun _ => 0)

/-- Monotonicity in the constant `C`. 0 sorrys. -/
theorem singleton_pointwise_bound_mono
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) {C₁ C₂ : ℝ} (p₀ : Polymer d (Int.ofNat k))
    (h₁ : SingletonPointwiseBound d N_c k C₁ p₀)
    (hmono : C₁ ≤ C₂) :
    SingletonPointwiseBound d N_c k C₂ p₀ := by
  intro K
  calc
    |K p₀|
      ≤ C₁ * ActivityNorm.dist K (fun _ => 0) := h₁ K
    _ ≤ C₂ * ActivityNorm.dist K (fun _ => 0) := by
      have hdist : 0 ≤ ActivityNorm.dist K (fun _ => 0) :=
        ActivityNorm.dist_nonneg _ _
      exact mul_le_mul_of_nonneg_right hmono hdist

/-! ## Upgrade to singleton P80 -/

/-- A pointwise bridge bound upgrades to the singleton full large-field bound
once `C ≤ exp(-β)`. 0 sorrys. -/
theorem singleton_large_field_bound_of_pointwise
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β C : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (hpoint : SingletonPointwiseBound d N_c k C p₀)
    (hC : C ≤ Real.exp (-β)) :
    SingletonFullLargeFieldBound d N_c k β p₀ := by
  intro K
  calc
    |K p₀|
      ≤ C * ActivityNorm.dist K (fun _ => 0) := hpoint K
    _ ≤ Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) := by
      have hdist : 0 ≤ ActivityNorm.dist K (fun _ => 0) :=
        ActivityNorm.dist_nonneg _ _
      exact mul_le_mul_of_nonneg_right hC hdist

/-! ## Automatic singleton control constructor -/

/-- Build the singleton full bridge control from a pointwise large-field bound,
a scalar comparison `C ≤ exp(-β)`, and the singleton Cauchy hypothesis.
0 sorrys. -/
def singletonCanonicalGeometricBridgeControlFull_of_pointwise
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β C : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (hpoint : SingletonPointwiseBound d N_c k C p₀)
    (hC : C ≤ Real.exp (-β))
    (hcauchy : SingletonFullCauchyBound d N_c k β p₀) :
    RGViaBridgeControlFull d N_c k β :=
  singletonCanonicalGeometricBridgeControlFull k β p₀
    (singleton_large_field_bound_of_pointwise k β C p₀ hpoint hC)
    hcauchy

/-- The automatically constructed control has the expected zero-field property.
0 sorrys. -/
theorem singleton_pointwise_control_zero_field
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β C : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (hpoint : SingletonPointwiseBound d N_c k C p₀)
    (hC : C ≤ Real.exp (-β))
    (hcauchy : SingletonFullCauchyBound d N_c k β p₀) :
    (singletonCanonicalGeometricBridgeControlFull_of_pointwise
      k β C p₀ hpoint hC hcauchy).core.bridge.fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  rg_control_full_zero_field
    (singletonCanonicalGeometricBridgeControlFull_of_pointwise
      k β C p₀ hpoint hC hcauchy)

end

end YangMills.ClayCore
