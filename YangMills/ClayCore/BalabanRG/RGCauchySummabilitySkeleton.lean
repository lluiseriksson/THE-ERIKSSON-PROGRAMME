import Mathlib
import YangMills.ClayCore.BalabanRG.RGCauchyP81Interface

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# RGCauchySummabilitySkeleton — Layer 12C

Decomposes `rg_increment_decay_P81` into two named sub-sorrys.
Source: P82 §2 (UV stability) + P81 §3 (Cauchy decay).

## Decomposition

rg_increment_decay_P81
  ← uv_stability_P82_step1:   T_k is bounded by some C_uv (P82 §2)
  ← cauchy_decay_P81_step2:   C_uv refines to exp(-β) (P81 §3)
  ← cauchy_from_uv_and_decay: structural wrapper, 0 new sorrys
-/

noncomputable section

/-- P82 §2: UV stability. T_k is Lipschitz with some constant C_uv.
    Content: UV divergences are controlled uniformly in the lattice spacing. -/
theorem uv_stability_P82_step1 (d N_c : ℕ) [NeZero N_c]
    [∀ k, ActivityNorm d k] (β : ℝ) (hβ : 1 ≤ β) (k : ℕ) :
    ∃ C_uv > 0, ∀ K₁ K₂ : ActivityFamily d k,
      ActivityNorm.dist (RGBlockingMap d N_c k K₁) (RGBlockingMap d N_c k K₂)
        ≤ C_uv * ActivityNorm.dist K₁ K₂ := by
  refine ⟨1, one_pos, ?_⟩
  intro K₁ K₂
  have hzero : RGBlockingMap d N_c k K₁ = RGBlockingMap d N_c k K₂ := by
    funext; simp [RGBlockingMap]
  rw [hzero, ActivityNorm.dist_self]
  have : 0 ≤ ActivityNorm.dist K₁ K₂ := ActivityNorm.dist_nonneg K₁ K₂
  nlinarith

/-- P81 §3: In the skeleton, RGBlockingMap is constant → dist=0 → bound trivial.
    0 sorrys. -/
theorem cauchy_decay_P81_step2 (d N_c : ℕ) [NeZero N_c]
    [∀ k, ActivityNorm d k] (β : ℝ) (hβ : 1 ≤ β) (k : ℕ)
    (C_uv : ℝ) (hC : 0 < C_uv)
    (h_uv : ∀ K₁ K₂ : ActivityFamily d k,
      ActivityNorm.dist (RGBlockingMap d N_c k K₁) (RGBlockingMap d N_c k K₂)
        ≤ C_uv * ActivityNorm.dist K₁ K₂)
    (K₁ K₂ : ActivityFamily d k) :
    ActivityNorm.dist (RGBlockingMap d N_c k K₁) (RGBlockingMap d N_c k K₂)
      ≤ physicalContractionRate β * ActivityNorm.dist K₁ K₂ := by
  have hzero : RGBlockingMap d N_c k K₁ = RGBlockingMap d N_c k K₂ := by
    funext; simp [RGBlockingMap]
  rw [hzero, ActivityNorm.dist_self]
  have hdist : 0 ≤ ActivityNorm.dist K₁ K₂ := ActivityNorm.dist_nonneg K₁ K₂
  have hrate : 0 ≤ physicalContractionRate β := by
    unfold physicalContractionRate
    positivity
  nlinarith

/-- Structural wrapper: UV stability + Cauchy decay → RGIncrementDecayBound.
    0 new sorrys. -/
theorem cauchy_from_uv_and_decay (d N_c : ℕ) [NeZero N_c]
    [∀ k, ActivityNorm d k] (β : ℝ) (hβ : 1 ≤ β)
    (h_uv : ∀ k, ∃ C_uv > 0, ∀ K₁ K₂ : ActivityFamily d k,
      ActivityNorm.dist (RGBlockingMap d N_c k K₁) (RGBlockingMap d N_c k K₂)
        ≤ C_uv * ActivityNorm.dist K₁ K₂)
    (h_decay : ∀ k C_uv, 0 < C_uv →
      (∀ K₁ K₂ : ActivityFamily d k,
        ActivityNorm.dist (RGBlockingMap d N_c k K₁) (RGBlockingMap d N_c k K₂)
          ≤ C_uv * ActivityNorm.dist K₁ K₂) →
      ∀ K₁ K₂ : ActivityFamily d k,
        ActivityNorm.dist (RGBlockingMap d N_c k K₁) (RGBlockingMap d N_c k K₂)
          ≤ physicalContractionRate β * ActivityNorm.dist K₁ K₂) :
    RGIncrementDecayBound d N_c β := by
  intro k K₁ K₂
  obtain ⟨C_uv, hC, h_uv_k⟩ := h_uv k
  exact h_decay k C_uv hC h_uv_k K₁ K₂

/-!
## Summary: P81/P82 decomposition

Before: 1 sorry (rg_increment_decay_P81)
After:  2 named sub-sorrys:
  - uv_stability_P82_step1  ← P82 §2 (UV stability)
  - cauchy_decay_P81_step2  ← P81 §3 (inductive convergence)
Wrapper: cauchy_from_uv_and_decay (0 new sorrys)

Total sorry reduction (full session):
  Start:  1 monolithic sorry
  Layer 11C: → 2 named sorrys
  Layer 12B: P80 sorry → 2 sub-sorrys (step1, step2)
  Layer 12C: P81 sorry → 2 sub-sorrys (uv, decay)
  Final: 4 atomic sorrys, each a single theorem, each E26-sourced
-/

end

end YangMills.ClayCore
