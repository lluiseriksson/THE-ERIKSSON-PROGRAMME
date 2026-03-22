import Mathlib
import YangMills.ClayCore.BalabanRG.RGIncrementDecayP81SlotFamily
import YangMills.ClayCore.BalabanRG.SmallFieldLargeFieldSplit

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-!
# RGIncrementDecayP81SmallFieldSlot

Dedicated landing zone for the first live P81 ingredient:
small-field random-walk decay.

This file does **not** prove the small-field random-walk theorem itself.
It does something precise and useful:
it isolates that ingredient as its own β-indexed family, ties it to the existing
small-field threshold surface, and provides the uniform bridge from that ingredient
plus the two remaining slots to the current `RGIncrementDecayP81SlotFamily`.

In other words:
once the actual Bałaban small-field RW theorem is formalized,
this file is where it should land.
-/

/-- The physical small-field threshold already used elsewhere in the repository. -/
def p81_small_field_threshold (β : ℝ) : ℝ := fieldThreshold β

theorem p81_small_field_threshold_pos (β : ℝ) :
    0 < p81_small_field_threshold β := by
  unfold p81_small_field_threshold
  exact fieldThreshold_pos β

theorem p81_small_field_threshold_nonneg (β : ℝ) :
    0 ≤ p81_small_field_threshold β := by
  exact le_of_lt (p81_small_field_threshold_pos β)

theorem p81_small_field_threshold_lt_one (β : ℝ) (hβ : 0 < β) :
    p81_small_field_threshold β < 1 := by
  unfold p81_small_field_threshold
  exact fieldThreshold_lt_one β hβ

/-- A β-indexed family for the first live P81 ingredient:
small-field random-walk decay. -/
structure P81SmallFieldRandomWalkDecayFamily
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] where
  holds : ℝ → Prop

/-- Uniform validity of the small-field random-walk family above `beta0`. -/
def P81SmallFieldRandomWalkDecayUniformAt
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (beta0 : ℝ) : Prop :=
  ∀ β : ℝ, beta0 ≤ β → small.holds β

/-- Inject the dedicated small-field family into the full P81 slot-family bridge. -/
def p81_slot_family_of_small_field_random_walk
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (largeFieldPolymerSuppression : ℝ → Prop)
    (clusterExpansionWithHoles : ℝ → Prop)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        largeFieldPolymerSuppression β →
        clusterExpansionWithHoles β →
        RGIncrementDecayBound d N_c β) :
    RGIncrementDecayP81SlotFamily d N_c :=
  { smallFieldRandomWalkDecay := small.holds
    largeFieldPolymerSuppression := largeFieldPolymerSuppression
    clusterExpansionWithHoles := clusterExpansionWithHoles
    gluesToIncrementDecay := by
      intro β hsf hlf hce
      exact glue hsf hlf hce }

/-- If the small-field family and the two remaining slots hold uniformly above `beta0`,
then the full slot-family bridge also holds uniformly above `beta0`. -/
theorem uniform_slot_family_of_uniform_small_field_and_remaining_slots
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (largeFieldPolymerSuppression : ℝ → Prop)
    (clusterExpansionWithHoles : ℝ → Prop)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        largeFieldPolymerSuppression β →
        clusterExpansionWithHoles β →
        RGIncrementDecayBound d N_c β)
    {beta0 : ℝ}
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small beta0)
    (hlarge : ∀ β : ℝ, beta0 ≤ β → largeFieldPolymerSuppression β)
    (hholes : ∀ β : ℝ, beta0 ≤ β → clusterExpansionWithHoles β) :
    RGIncrementDecayP81SlotFamilyUniformAt d N_c
      (p81_slot_family_of_small_field_random_walk d N_c small
        largeFieldPolymerSuppression clusterExpansionWithHoles glue)
      beta0 := by
  intro β hβ
  exact ⟨hsmall β hβ, ⟨hlarge β hβ, hholes β hβ⟩⟩

/-- The theorem-side live target follows immediately once the first slot and the two
remaining slots are populated uniformly above `beta0`. -/
theorem rg_cauchy_p81_live_target_of_uniform_small_field_and_remaining_slots
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (largeFieldPolymerSuppression : ℝ → Prop)
    (clusterExpansionWithHoles : ℝ → Prop)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        largeFieldPolymerSuppression β →
        clusterExpansionWithHoles β →
        RGIncrementDecayBound d N_c β)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small beta0)
    (hlarge : ∀ β : ℝ, beta0 ≤ β → largeFieldPolymerSuppression β)
    (hholes : ∀ β : ℝ, beta0 ≤ β → clusterExpansionWithHoles β) :
    RGCauchyP81LiveTarget d N_c := by
  exact
    rg_cauchy_p81_live_target_of_slot_family d N_c
      (p81_slot_family_of_small_field_random_walk d N_c small
        largeFieldPolymerSuppression clusterExpansionWithHoles glue)
      hbeta0_pos
      (uniform_slot_family_of_uniform_small_field_and_remaining_slots
        d N_c small largeFieldPolymerSuppression clusterExpansionWithHoles
        glue hsmall hlarge hholes)

/-- The short theorem-side public frontier is an immediate downstream consumer of the
dedicated small-field slot plus the two remaining populated slots. -/
theorem rg_cauchy_p81_frontier_of_audit_packet_and_uniform_small_field_and_remaining_slots
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (largeFieldPolymerSuppression : ℝ → Prop)
    (clusterExpansionWithHoles : ℝ → Prop)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        largeFieldPolymerSuppression β →
        clusterExpansionWithHoles β →
        RGIncrementDecayBound d N_c β)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small beta0)
    (hlarge : ∀ β : ℝ, beta0 ≤ β → largeFieldPolymerSuppression β)
    (hholes : ∀ β : ℝ, beta0 ≤ β → clusterExpansionWithHoles β) :
    RGCauchyP81Frontier d N_c := by
  exact
    rg_cauchy_p81_frontier_of_audit_packet_and_slot_family d N_c audit
      (p81_slot_family_of_small_field_random_walk d N_c small
        largeFieldPolymerSuppression clusterExpansionWithHoles glue)
      hbeta0_pos
      (uniform_slot_family_of_uniform_small_field_and_remaining_slots
        d N_c small largeFieldPolymerSuppression clusterExpansionWithHoles
        glue hsmall hlarge hholes)

/-- The theorem-side coherence packet is likewise an immediate downstream consumer. -/
theorem rg_cauchy_p81_coherence_packet_of_audit_packet_and_uniform_small_field_and_remaining_slots
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (largeFieldPolymerSuppression : ℝ → Prop)
    (clusterExpansionWithHoles : ℝ → Prop)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        largeFieldPolymerSuppression β →
        clusterExpansionWithHoles β →
        RGIncrementDecayBound d N_c β)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small beta0)
    (hlarge : ∀ β : ℝ, beta0 ≤ β → largeFieldPolymerSuppression β)
    (hholes : ∀ β : ℝ, beta0 ≤ β → clusterExpansionWithHoles β) :
    RGCauchyP81CoherencePacket d N_c := by
  exact
    rg_cauchy_p81_coherence_packet_of_audit_packet_and_slot_family d N_c audit
      (p81_slot_family_of_small_field_random_walk d N_c small
        largeFieldPolymerSuppression clusterExpansionWithHoles glue)
      hbeta0_pos
      (uniform_slot_family_of_uniform_small_field_and_remaining_slots
        d N_c small largeFieldPolymerSuppression clusterExpansionWithHoles
        glue hsmall hlarge hholes)

end

end YangMills.ClayCore
