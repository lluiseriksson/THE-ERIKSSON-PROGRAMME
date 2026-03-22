import Mathlib
import YangMills.ClayCore.BalabanRG.RGIncrementDecayP81SmallFieldSlot
import YangMills.ClayCore.BalabanRG.SmallFieldLargeFieldSplit

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-!
# RGIncrementDecayP81LargeFieldSlot

Dedicated landing zone for the second live P81 ingredient:
large-field polymer suppression.

This file does **not** prove the large-field suppression theorem itself.
It does something precise and useful:
it isolates that ingredient as its own β-indexed family, ties it to the existing
large-field threshold / norm surface, and provides the uniform bridge from the first
two slots plus the remaining cluster-expansion slot to the current
`RGIncrementDecayP81SlotFamily`.

In other words:
once the actual Bałaban large-field suppression theorem is formalized,
this file is where it should land.
-/

/-- The physical large-field threshold is the same `fieldThreshold β`
that defines the complement of the small-field regime. -/
def p81_large_field_threshold (β : ℝ) : ℝ := fieldThreshold β

theorem p81_large_field_threshold_pos (β : ℝ) :
    0 < p81_large_field_threshold β := by
  unfold p81_large_field_threshold
  exact fieldThreshold_pos β

theorem p81_large_field_threshold_nonneg (β : ℝ) :
    0 ≤ p81_large_field_threshold β := by
  exact le_of_lt (p81_large_field_threshold_pos β)

theorem p81_large_field_threshold_lt_one (β : ℝ) (hβ : 0 < β) :
    p81_large_field_threshold β < 1 := by
  unfold p81_large_field_threshold
  exact fieldThreshold_lt_one β hβ

/-- The existing discrete large-field norm is the natural geometric monitor
for the large-field slot. -/
def p81_large_field_norm
    {d k : ℕ}
    (φ : BalabanLatticeSite d k → ℝ)
    (β : ℝ) : ℝ :=
  largeFieldNorm φ β

theorem p81_large_field_norm_nonneg
    {d k : ℕ}
    (φ : BalabanLatticeSite d k → ℝ)
    (β : ℝ) :
    0 ≤ p81_large_field_norm φ β := by
  unfold p81_large_field_norm
  exact largeFieldNorm_nonneg φ β

theorem p81_large_field_norm_zero_of_small
    {d N_c : ℕ} [NeZero N_c]
    {k : ℕ} {β : ℝ}
    (φ : BalabanLatticeSite d k → ℝ)
    (hS : SmallFieldPredicateField d N_c k β φ) :
    p81_large_field_norm φ β = 0 := by
  unfold p81_large_field_norm
  exact largeFieldNorm_zero_of_small φ hS

theorem p81_large_field_norm_pos_of_large
    {d N_c : ℕ} [NeZero N_c]
    {k : ℕ} {β : ℝ}
    (φ : BalabanLatticeSite d k → ℝ)
    (hL : LargeFieldPredicateField d N_c k β φ) :
    0 < p81_large_field_norm φ β := by
  unfold p81_large_field_norm
  exact largeFieldNorm_pos_of_large φ hL

/-- A β-indexed family for the second live P81 ingredient:
large-field polymer suppression. -/
structure P81LargeFieldPolymerSuppressionFamily
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] where
  holds : ℝ → Prop

/-- Uniform validity of the large-field suppression family above `beta0`. -/
def P81LargeFieldPolymerSuppressionUniformAt
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (large : P81LargeFieldPolymerSuppressionFamily d N_c)
    (beta0 : ℝ) : Prop :=
  ∀ β : ℝ, beta0 ≤ β → large.holds β

/-- Inject the dedicated small-field and large-field families into the full
P81 slot-family bridge. -/
def p81_slot_family_of_small_and_large_field
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (large : P81LargeFieldPolymerSuppressionFamily d N_c)
    (clusterExpansionWithHoles : ℝ → Prop)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        large.holds β →
        clusterExpansionWithHoles β →
        RGIncrementDecayBound d N_c β) :
    RGIncrementDecayP81SlotFamily d N_c :=
  { smallFieldRandomWalkDecay := small.holds
    largeFieldPolymerSuppression := large.holds
    clusterExpansionWithHoles := clusterExpansionWithHoles
    gluesToIncrementDecay := by
      intro β hsf hlf hce
      exact glue hsf hlf hce }

/-- If the first two slots and the remaining cluster-expansion slot hold uniformly
above `beta0`, then the full slot-family bridge also holds uniformly above `beta0`. -/
theorem uniform_slot_family_of_uniform_small_and_large_field_and_remaining_slot
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (large : P81LargeFieldPolymerSuppressionFamily d N_c)
    (clusterExpansionWithHoles : ℝ → Prop)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        large.holds β →
        clusterExpansionWithHoles β →
        RGIncrementDecayBound d N_c β)
    {beta0 : ℝ}
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small beta0)
    (hlarge : P81LargeFieldPolymerSuppressionUniformAt d N_c large beta0)
    (hholes : ∀ β : ℝ, beta0 ≤ β → clusterExpansionWithHoles β) :
    RGIncrementDecayP81SlotFamilyUniformAt d N_c
      (p81_slot_family_of_small_and_large_field d N_c small large
        clusterExpansionWithHoles glue)
      beta0 := by
  intro β hβ
  exact ⟨hsmall β hβ, ⟨hlarge β hβ, hholes β hβ⟩⟩

/-- The theorem-side live target follows immediately once the first two slots and
the remaining cluster-expansion slot are populated uniformly above `beta0`. -/
theorem rg_cauchy_p81_live_target_of_uniform_small_and_large_field_and_remaining_slot
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (large : P81LargeFieldPolymerSuppressionFamily d N_c)
    (clusterExpansionWithHoles : ℝ → Prop)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        large.holds β →
        clusterExpansionWithHoles β →
        RGIncrementDecayBound d N_c β)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small beta0)
    (hlarge : P81LargeFieldPolymerSuppressionUniformAt d N_c large beta0)
    (hholes : ∀ β : ℝ, beta0 ≤ β → clusterExpansionWithHoles β) :
    RGCauchyP81LiveTarget d N_c := by
  exact
    rg_cauchy_p81_live_target_of_slot_family d N_c
      (p81_slot_family_of_small_and_large_field d N_c small large
        clusterExpansionWithHoles glue)
      hbeta0_pos
      (uniform_slot_family_of_uniform_small_and_large_field_and_remaining_slot
        d N_c small large clusterExpansionWithHoles
        glue hsmall hlarge hholes)

/-- The short theorem-side public frontier is an immediate downstream consumer of the
first two slots plus the remaining cluster-expansion slot. -/
theorem rg_cauchy_p81_frontier_of_audit_packet_and_uniform_small_and_large_field_and_remaining_slot
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (large : P81LargeFieldPolymerSuppressionFamily d N_c)
    (clusterExpansionWithHoles : ℝ → Prop)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        large.holds β →
        clusterExpansionWithHoles β →
        RGIncrementDecayBound d N_c β)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small beta0)
    (hlarge : P81LargeFieldPolymerSuppressionUniformAt d N_c large beta0)
    (hholes : ∀ β : ℝ, beta0 ≤ β → clusterExpansionWithHoles β) :
    RGCauchyP81Frontier d N_c := by
  exact
    rg_cauchy_p81_frontier_of_audit_packet_and_slot_family d N_c audit
      (p81_slot_family_of_small_and_large_field d N_c small large
        clusterExpansionWithHoles glue)
      hbeta0_pos
      (uniform_slot_family_of_uniform_small_and_large_field_and_remaining_slot
        d N_c small large clusterExpansionWithHoles
        glue hsmall hlarge hholes)

/-- The theorem-side coherence packet is likewise an immediate downstream consumer. -/
theorem rg_cauchy_p81_coherence_packet_of_audit_packet_and_uniform_small_and_large_field_and_remaining_slot
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (large : P81LargeFieldPolymerSuppressionFamily d N_c)
    (clusterExpansionWithHoles : ℝ → Prop)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        large.holds β →
        clusterExpansionWithHoles β →
        RGIncrementDecayBound d N_c β)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small beta0)
    (hlarge : P81LargeFieldPolymerSuppressionUniformAt d N_c large beta0)
    (hholes : ∀ β : ℝ, beta0 ≤ β → clusterExpansionWithHoles β) :
    RGCauchyP81CoherencePacket d N_c := by
  exact
    rg_cauchy_p81_coherence_packet_of_audit_packet_and_slot_family d N_c audit
      (p81_slot_family_of_small_and_large_field d N_c small large
        clusterExpansionWithHoles glue)
      hbeta0_pos
      (uniform_slot_family_of_uniform_small_and_large_field_and_remaining_slot
        d N_c small large clusterExpansionWithHoles
        glue hsmall hlarge hholes)

end

end YangMills.ClayCore
