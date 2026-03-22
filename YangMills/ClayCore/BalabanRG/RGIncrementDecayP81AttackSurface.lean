import Mathlib
import YangMills.ClayCore.BalabanRG.RGCauchyP81LiveTarget

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-!
# RGIncrementDecayP81AttackSurface

Honest theorem-side attack packet for the live P81 bottleneck.

This file does **not** solve `rg_increment_decay_P81`.
It packages the exact paper-side submechanisms singled out by the current strategy:

* small-field random-walk decay,
* large-field polymer suppression,
* cluster expansion / gluing with holes,

together with the theorem-bearing gluing output needed by the current Lean frontier.

Important Lean note:
the local packet is a projection-safe structure.
The uniform surface below is proposition-valued by storing only `Nonempty`
local packets above a weak-coupling threshold.
-/

/-- Exact theorem-side attack packet for the live P81 increment-decay theorem. -/
structure RGIncrementDecayP81AttackSurface
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] (β : ℝ) where
  smallFieldRandomWalkDecay : Prop
  largeFieldPolymerSuppression : Prop
  clusterExpansionWithHoles : Prop
  gluesToIncrementDecay : RGIncrementDecayBound d N_c β

/-- Uniform proposition-valued attack surface: above a threshold, every β carries
at least one local attack packet. -/
def RGIncrementDecayP81UniformAttackSurface
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop :=
  ∃ beta0 : ℝ, 0 < beta0 ∧
    ∀ β : ℝ, beta0 ≤ β → Nonempty (RGIncrementDecayP81AttackSurface d N_c β)

/-- Projection to the single-scale increment-decay theorem-side target. -/
theorem rg_increment_decay_bound_of_attack_surface
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    {β : ℝ}
    (attack : RGIncrementDecayP81AttackSurface d N_c β) :
    RGIncrementDecayBound d N_c β := by
  exact attack.gluesToIncrementDecay

/-- Projection to the RG-Cauchy summability side. -/
theorem rg_cauchy_summability_bound_of_attack_surface
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    {β : ℝ}
    (attack : RGIncrementDecayP81AttackSurface d N_c β) :
    RGCauchySummabilityBound d N_c β := by
  exact
    increment_decay_implies_cauchy_summability d N_c β
      attack.gluesToIncrementDecay

/-- A populated attack packet at a specific β yields the explicit P81 obligation packet. -/
theorem rg_cauchy_p81_obligation_of_attack_surface
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    {β : ℝ}
    (hβ : 1 ≤ β)
    (attack : RGIncrementDecayP81AttackSurface d N_c β) :
    RGCauchyP81Obligation d N_c := by
  exact
    ⟨⟨β, hβ, attack.gluesToIncrementDecay,
      rg_cauchy_summability_bound_of_attack_surface attack⟩⟩

/-- A uniform populated attack surface yields the theorem-side live target. -/
theorem rg_cauchy_p81_live_target_of_uniform_attack_surface
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (attack : RGIncrementDecayP81UniformAttackSurface d N_c) :
    RGCauchyP81LiveTarget d N_c := by
  rcases attack with ⟨beta0, hbeta0_pos, hattack⟩
  refine ⟨beta0, hbeta0_pos, ?_⟩
  intro β hβ0
  exact (Classical.choice (hattack β hβ0)).gluesToIncrementDecay

/-- The current frontier is an immediate downstream consumer of the uniform attack surface. -/
theorem rg_cauchy_p81_frontier_of_audit_packet_and_uniform_attack_surface
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (attack : RGIncrementDecayP81UniformAttackSurface d N_c) :
    RGCauchyP81Frontier d N_c := by
  exact
    rg_cauchy_p81_frontier_of_audit_packet_and_live_target d N_c audit
      (rg_cauchy_p81_live_target_of_uniform_attack_surface d N_c attack)

/-- The coherence packet is likewise an immediate downstream consumer. -/
theorem rg_cauchy_p81_coherence_packet_of_audit_packet_and_uniform_attack_surface
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (attack : RGIncrementDecayP81UniformAttackSurface d N_c) :
    RGCauchyP81CoherencePacket d N_c := by
  exact
    rg_cauchy_p81_coherence_packet_of_audit_packet_and_live_target d N_c audit
      (rg_cauchy_p81_live_target_of_uniform_attack_surface d N_c attack)

end

end YangMills.ClayCore
