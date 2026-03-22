import Mathlib
import YangMills.ClayCore.BalabanRG.RGIncrementDecayP81AttackSurface

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-!
# RGIncrementDecayP81SlotFamily

Uniform bridge from the three paper-side P81 ingredients to the local attack packet.

This file does **not** prove `rg_increment_decay_P81`.
It makes the next theorem-side move explicit:
once one has β-indexed theorem families for

* small-field random-walk decay,
* large-field polymer suppression,
* cluster expansion with holes,

together with the gluing theorem that turns those three ingredients into
`RGIncrementDecayBound`, the current repository can already manufacture the
existing local attack packet, the uniform attack surface, the live target, and the
short theorem-side public frontier.

The point is to provide a single landing zone for the actual Bałaban mathematics.
-/

/-- A β-indexed family of P81 paper-side inputs together with the gluing theorem
to the single-scale increment-decay bound. -/
structure RGIncrementDecayP81SlotFamily
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] where
  smallFieldRandomWalkDecay : ℝ → Prop
  largeFieldPolymerSuppression : ℝ → Prop
  clusterExpansionWithHoles : ℝ → Prop
  gluesToIncrementDecay :
    ∀ {β : ℝ},
      smallFieldRandomWalkDecay β →
      largeFieldPolymerSuppression β →
      clusterExpansionWithHoles β →
      RGIncrementDecayBound d N_c β

/-- Above `beta0`, all three slot families hold. -/
def RGIncrementDecayP81SlotFamilyUniformAt
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (slots : RGIncrementDecayP81SlotFamily d N_c)
    (beta0 : ℝ) : Prop :=
  ∀ β : ℝ, beta0 ≤ β →
    slots.smallFieldRandomWalkDecay β ∧
    slots.largeFieldPolymerSuppression β ∧
    slots.clusterExpansionWithHoles β

/-- Local theorem-side output from populated slots at one β. -/
theorem rg_increment_decay_bound_of_slot_family
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (slots : RGIncrementDecayP81SlotFamily d N_c)
    {β : ℝ}
    (hsf : slots.smallFieldRandomWalkDecay β)
    (hlf : slots.largeFieldPolymerSuppression β)
    (hce : slots.clusterExpansionWithHoles β) :
    RGIncrementDecayBound d N_c β := by
  exact slots.gluesToIncrementDecay hsf hlf hce

/-- Local attack packet from populated slots at one β. -/
def attack_surface_of_slot_family
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (slots : RGIncrementDecayP81SlotFamily d N_c)
    {β : ℝ}
    (hsf : slots.smallFieldRandomWalkDecay β)
    (hlf : slots.largeFieldPolymerSuppression β)
    (hce : slots.clusterExpansionWithHoles β) :
    RGIncrementDecayP81AttackSurface d N_c β :=
  { smallFieldRandomWalkDecay := slots.smallFieldRandomWalkDecay β
    largeFieldPolymerSuppression := slots.largeFieldPolymerSuppression β
    clusterExpansionWithHoles := slots.clusterExpansionWithHoles β
    gluesToIncrementDecay := rg_increment_decay_bound_of_slot_family slots hsf hlf hce }

/-- Uniform attack surface from a slot family that holds uniformly above `beta0`. -/
theorem uniform_attack_surface_of_slot_family
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (slots : RGIncrementDecayP81SlotFamily d N_c)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hslots : RGIncrementDecayP81SlotFamilyUniformAt d N_c slots beta0) :
    RGIncrementDecayP81UniformAttackSurface d N_c := by
  refine ⟨beta0, hbeta0_pos, ?_⟩
  intro β hβ
  rcases hslots β hβ with ⟨hsf, hrest⟩
  rcases hrest with ⟨hlf, hce⟩
  exact ⟨attack_surface_of_slot_family slots hsf hlf hce⟩

/-- The theorem-side live target follows immediately from a uniformly populated slot family. -/
theorem rg_cauchy_p81_live_target_of_slot_family
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (slots : RGIncrementDecayP81SlotFamily d N_c)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hslots : RGIncrementDecayP81SlotFamilyUniformAt d N_c slots beta0) :
    RGCauchyP81LiveTarget d N_c := by
  exact
    rg_cauchy_p81_live_target_of_uniform_attack_surface d N_c
      (uniform_attack_surface_of_slot_family d N_c slots hbeta0_pos hslots)

/-- The short theorem-side public frontier is an immediate downstream consumer
of a uniformly populated slot family. -/
theorem rg_cauchy_p81_frontier_of_audit_packet_and_slot_family
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (slots : RGIncrementDecayP81SlotFamily d N_c)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hslots : RGIncrementDecayP81SlotFamilyUniformAt d N_c slots beta0) :
    RGCauchyP81Frontier d N_c := by
  exact
    rg_cauchy_p81_frontier_of_audit_packet_and_uniform_attack_surface d N_c audit
      (uniform_attack_surface_of_slot_family d N_c slots hbeta0_pos hslots)

/-- The theorem-side coherence packet is likewise an immediate downstream consumer
of a uniformly populated slot family. -/
theorem rg_cauchy_p81_coherence_packet_of_audit_packet_and_slot_family
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (slots : RGIncrementDecayP81SlotFamily d N_c)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hslots : RGIncrementDecayP81SlotFamilyUniformAt d N_c slots beta0) :
    RGCauchyP81CoherencePacket d N_c := by
  exact
    rg_cauchy_p81_coherence_packet_of_audit_packet_and_uniform_attack_surface d N_c audit
      (uniform_attack_surface_of_slot_family d N_c slots hbeta0_pos hslots)

end

end YangMills.ClayCore
