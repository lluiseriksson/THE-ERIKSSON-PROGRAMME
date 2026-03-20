import Mathlib
import YangMills.ClayCore.BalabanRG.FullLargeFieldSingletonBound
import YangMills.ClayCore.BalabanRG.CauchyDecayViaBridgeFiniteFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# FullCauchySingletonBound — (v1.0.8-alpha Phase 2)

Pointwise-to-singleton bridge for the full Cauchy bound.

This mirrors `FullLargeFieldSingletonBound`:
instead of assuming the singleton P81 hypothesis directly, we factor it
through a simpler pointwise difference bound

  |K₁ p₀ - K₂ p₀| ≤ C · dist(K₁, K₂)

and then upgrade it to `SingletonFullCauchyBound` once
`C ≤ physicalContractionRate β`.

This is the natural singleton P81 counterpart to the Phase 1 bridge.
-/

noncomputable section

/-! ## Pointwise bridge hypothesis -/

/-- Minimal pointwise bridge for singleton Cauchy control:
evaluation differences at `p₀` are controlled by
`C * ActivityNorm.dist K₁ K₂`. -/
def SingletonPointwiseCauchyBound (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (C : ℝ)
    (p₀ : Polymer d (Int.ofNat k)) : Prop :=
  ∀ (K₁ K₂ : ActivityFamily d k),
    |K₁ p₀ - K₂ p₀| ≤ C * ActivityNorm.dist K₁ K₂

/-- Monotonicity in the constant `C`. 0 sorrys. -/
theorem singleton_pointwise_cauchy_bound_mono
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) {C₁ C₂ : ℝ} (p₀ : Polymer d (Int.ofNat k))
    (h₁ : SingletonPointwiseCauchyBound d N_c k C₁ p₀)
    (hmono : C₁ ≤ C₂) :
    SingletonPointwiseCauchyBound d N_c k C₂ p₀ := by
  intro K₁ K₂
  calc
    |K₁ p₀ - K₂ p₀|
      ≤ C₁ * ActivityNorm.dist K₁ K₂ := h₁ K₁ K₂
    _ ≤ C₂ * ActivityNorm.dist K₁ K₂ := by
      have hdist : 0 ≤ ActivityNorm.dist K₁ K₂ :=
        ActivityNorm.dist_nonneg _ _
      exact mul_le_mul_of_nonneg_right hmono hdist

/-! ## Upgrade to singleton P81 -/

/-- A pointwise bridge bound upgrades to the singleton full Cauchy bound
once `C ≤ physicalContractionRate β`. 0 sorrys. -/
theorem singleton_cauchy_bound_of_pointwise
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β C : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (hpoint : SingletonPointwiseCauchyBound d N_c k C p₀)
    (hC : C ≤ physicalContractionRate β) :
    SingletonFullCauchyBound d N_c k β p₀ := by
  intro K₁ K₂
  calc
    |K₁ p₀ - K₂ p₀|
      ≤ C * ActivityNorm.dist K₁ K₂ := hpoint K₁ K₂
    _ ≤ physicalContractionRate β * ActivityNorm.dist K₁ K₂ := by
      have hdist : 0 ≤ ActivityNorm.dist K₁ K₂ :=
        ActivityNorm.dist_nonneg _ _
      exact mul_le_mul_of_nonneg_right hC hdist

/-! ## Automatic singleton control constructor -/

/-- Build the singleton full bridge control from pointwise large-field and
pointwise Cauchy bounds plus scalar comparisons.
0 sorrys. -/
def singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β C_large C_cauchy : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (hlarge : SingletonPointwiseBound d N_c k C_large p₀)
    (hlargeC : C_large ≤ Real.exp (-β))
    (hcauchy : SingletonPointwiseCauchyBound d N_c k C_cauchy p₀)
    (hcauchyC : C_cauchy ≤ physicalContractionRate β) :
    RGViaBridgeControlFull d N_c k β :=
  singletonCanonicalGeometricBridgeControlFull k β p₀
    (singleton_large_field_bound_of_pointwise k β C_large p₀ hlarge hlargeC)
    (singleton_cauchy_bound_of_pointwise k β C_cauchy p₀ hcauchy hcauchyC)

/-- The automatically constructed control satisfies the expected full
large-field estimate. 0 sorrys. -/
theorem singleton_pointwise_bounds_control_large_field
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β C_large C_cauchy : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (hlarge : SingletonPointwiseBound d N_c k C_large p₀)
    (hlargeC : C_large ≤ Real.exp (-β))
    (hcauchy : SingletonPointwiseCauchyBound d N_c k C_cauchy p₀)
    (hcauchyC : C_cauchy ≤ physicalContractionRate β)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |(singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
        k β C_large C_cauchy p₀ hlarge hlargeC hcauchy hcauchyC).core.bridge.fieldOfActivity K x| ≤
      Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  large_field_suppression_finite_full_consumer
    (singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
      k β C_large C_cauchy p₀ hlarge hlargeC hcauchy hcauchyC)
    K x

/-- The automatically constructed control satisfies the expected full
Cauchy estimate. 0 sorrys. -/
theorem singleton_pointwise_bounds_control_cauchy
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β C_large C_cauchy : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (hlarge : SingletonPointwiseBound d N_c k C_large p₀)
    (hlargeC : C_large ≤ Real.exp (-β))
    (hcauchy : SingletonPointwiseCauchyBound d N_c k C_cauchy p₀)
    (hcauchyC : C_cauchy ≤ physicalContractionRate β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |(singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
        k β C_large C_cauchy p₀ hlarge hlargeC hcauchy hcauchyC).core.bridge.fieldOfActivity K₁ x -
      (singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
        k β C_large C_cauchy p₀ hlarge hlargeC hcauchy hcauchyC).core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂ :=
  cauchy_summability_finite_full_consumer
    (singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
      k β C_large C_cauchy p₀ hlarge hlargeC hcauchy hcauchyC)
    K₁ K₂ x

/-- The automatically constructed control has the expected zero-field property.
0 sorrys. -/
theorem singleton_pointwise_bounds_control_zero_field
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β C_large C_cauchy : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (hlarge : SingletonPointwiseBound d N_c k C_large p₀)
    (hlargeC : C_large ≤ Real.exp (-β))
    (hcauchy : SingletonPointwiseCauchyBound d N_c k C_cauchy p₀)
    (hcauchyC : C_cauchy ≤ physicalContractionRate β) :
    (singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
      k β C_large C_cauchy p₀ hlarge hlargeC hcauchy hcauchyC).core.bridge.fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  rg_control_full_zero_field
    (singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
      k β C_large C_cauchy p₀ hlarge hlargeC hcauchy hcauchyC)

end

end YangMills.ClayCore
