import Mathlib
import YangMills.ClayCore.BalabanRG.RGCauchyTelescoping
import YangMills.ClayCore.BalabanRG.BalabanBlockingMap

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# RGCauchyP81Interface — Layer 11H

Named predicates for the physical input of P81 §3.
Separates the mathematical structure from the analytic content.

## The two physical inputs needed from P81

1. `RGIncrementDecayBound`: each scale contributes a bounded increment
2. `RGTelescopingSeriesBound`: the increments sum to give the Lipschitz bound
-/

noncomputable section

/-- Single-scale increment decay bound (P81 §3, single scale).
At each scale k, the RG map difference is bounded by exp(-β) · ‖K₁-K₂‖. -/
def RGIncrementDecayBound
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] (β : ℝ) : Prop :=
  ∀ k K₁ K₂,
    ActivityNorm.dist (RGBlockingMap d N_c k K₁) (RGBlockingMap d N_c k K₂)
      ≤ physicalContractionRate β * ActivityNorm.dist K₁ K₂

/-- If the increment decay bound holds, then RGCauchySummabilityBound follows directly. -/
theorem increment_decay_implies_cauchy_summability
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (β : ℝ) (h : RGIncrementDecayBound d N_c β) :
    RGCauchySummabilityBound d N_c β := fun k K₁ K₂ => h k K₁ K₂

/-- The P81 physical input: the increment decay bound holds at weak coupling.

In the current repository semantics this is dischargeable because `RGBlockingMap`
is still the zero map. This does **not** identify the present proof with the intended
final Bałaban theorem after the explicit blocking map is internalized.
-/
theorem rg_increment_decay_P81
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (β : ℝ) (_hβ : 1 ≤ β) :
    RGIncrementDecayBound d N_c β := by
  intro k K₁ K₂
  have h1 : RGBlockingMap d N_c k K₁ = fun _ => 0 := by
    funext p
    simp [RGBlockingMap]
  have h2 : RGBlockingMap d N_c k K₂ = fun _ => 0 := by
    funext p
    simp [RGBlockingMap]
  rw [h1, h2, ActivityNorm.dist_self]
  have hdist : 0 ≤ ActivityNorm.dist K₁ K₂ := ActivityNorm.dist_nonneg K₁ K₂
  have hrate : 0 ≤ physicalContractionRate β := le_of_lt (physicalContractionRate_pos β)
  nlinarith

/-- RGCauchySummabilityBound from the P81 increment decay. -/
theorem rg_cauchy_from_increment_decay
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (β : ℝ) (hβ : 1 ≤ β) :
    RGCauchySummabilityBound d N_c β :=
  increment_decay_implies_cauchy_summability d N_c β
    (rg_increment_decay_P81 d N_c β hβ)

end

end YangMills.ClayCore
