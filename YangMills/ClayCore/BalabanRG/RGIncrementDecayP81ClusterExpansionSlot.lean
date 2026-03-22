import Mathlib
import YangMills.ClayCore.BalabanRG.RGIncrementDecayP81LargeFieldSlot
import YangMills.ClayCore.BalabanRG.SmallFieldLargeFieldSplit

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-!
# RGIncrementDecayP81ClusterExpansionSlot

Dedicated landing zone for the third live P81 ingredient:
cluster expansion with holes.

This file does **not** prove the cluster-expansion-with-holes theorem itself.
It does something precise and useful:
it isolates that ingredient as its own β-indexed family, ties it to the existing
field-split / large-field-hole geometry surface, and provides the uniform bridge from
the three isolated slots to the current `RGIncrementDecayP81SlotFamily`.

In other words:
once the actual Bałaban / Dimock cluster-expansion-with-holes mechanism is formalized,
this file is where it should land.
-/

/-- The field-dependent split surface already present in the repository is the natural
geometric carrier for the holes mechanism. -/
def p81_cluster_holes_field_split
    (d N_c : ℕ) [NeZero N_c]
    (k : ℕ) : RGFieldSplitOnField d N_c k :=
  trivialRGFieldSplitOnField d N_c k

theorem p81_cluster_holes_field_split_small_eq
    {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (φ : BalabanLatticeSite d k → ℝ)
    (K : ActivityFamily d k) :
    (p81_cluster_holes_field_split d N_c k).smallPart φ K =
      RGBlockingMap d N_c k K := by
  rfl

theorem p81_cluster_holes_field_split_large_zero
    {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (φ : BalabanLatticeSite d k → ℝ)
    (K : ActivityFamily d k) :
    (p81_cluster_holes_field_split d N_c k).largePart φ K = fun _ => 0 := by
  rfl

/-- A β-indexed family for the third live P81 ingredient:
cluster expansion with holes. -/
structure P81ClusterExpansionWithHolesFamily
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] where
  holds : ℝ → Prop

/-- Uniform validity of the cluster-expansion-with-holes family above `beta0`. -/
def P81ClusterExpansionWithHolesUniformAt
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (cluster : P81ClusterExpansionWithHolesFamily d N_c)
    (beta0 : ℝ) : Prop :=
  ∀ β : ℝ, beta0 ≤ β → cluster.holds β

/-- Inject the three dedicated families into the full P81 slot-family bridge. -/
def p81_slot_family_of_small_large_and_cluster
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (large : P81LargeFieldPolymerSuppressionFamily d N_c)
    (cluster : P81ClusterExpansionWithHolesFamily d N_c)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        large.holds β →
        cluster.holds β →
        RGIncrementDecayBound d N_c β) :
    RGIncrementDecayP81SlotFamily d N_c :=
  { smallFieldRandomWalkDecay := small.holds
    largeFieldPolymerSuppression := large.holds
    clusterExpansionWithHoles := cluster.holds
    gluesToIncrementDecay := by
      intro β hsf hlf hce
      exact glue hsf hlf hce }

/-- If all three isolated slots hold uniformly above `beta0`, then the full slot-family
bridge also holds uniformly above `beta0`. -/
theorem uniform_slot_family_of_uniform_small_large_and_cluster
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (large : P81LargeFieldPolymerSuppressionFamily d N_c)
    (cluster : P81ClusterExpansionWithHolesFamily d N_c)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        large.holds β →
        cluster.holds β →
        RGIncrementDecayBound d N_c β)
    {beta0 : ℝ}
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small beta0)
    (hlarge : P81LargeFieldPolymerSuppressionUniformAt d N_c large beta0)
    (hcluster : P81ClusterExpansionWithHolesUniformAt d N_c cluster beta0) :
    RGIncrementDecayP81SlotFamilyUniformAt d N_c
      (p81_slot_family_of_small_large_and_cluster d N_c small large cluster glue)
      beta0 := by
  intro β hβ
  exact ⟨hsmall β hβ, ⟨hlarge β hβ, hcluster β hβ⟩⟩

/-- The theorem-side live target follows immediately once all three isolated slots
are populated uniformly above `beta0`. -/
theorem rg_cauchy_p81_live_target_of_uniform_small_large_and_cluster
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (large : P81LargeFieldPolymerSuppressionFamily d N_c)
    (cluster : P81ClusterExpansionWithHolesFamily d N_c)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        large.holds β →
        cluster.holds β →
        RGIncrementDecayBound d N_c β)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small beta0)
    (hlarge : P81LargeFieldPolymerSuppressionUniformAt d N_c large beta0)
    (hcluster : P81ClusterExpansionWithHolesUniformAt d N_c cluster beta0) :
    RGCauchyP81LiveTarget d N_c := by
  exact
    rg_cauchy_p81_live_target_of_slot_family d N_c
      (p81_slot_family_of_small_large_and_cluster d N_c small large cluster glue)
      hbeta0_pos
      (uniform_slot_family_of_uniform_small_large_and_cluster
        d N_c small large cluster glue hsmall hlarge hcluster)

/-- The short theorem-side public frontier is an immediate downstream consumer of the
three isolated slots. -/
theorem rg_cauchy_p81_frontier_of_audit_packet_and_uniform_small_large_and_cluster
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (large : P81LargeFieldPolymerSuppressionFamily d N_c)
    (cluster : P81ClusterExpansionWithHolesFamily d N_c)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        large.holds β →
        cluster.holds β →
        RGIncrementDecayBound d N_c β)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small beta0)
    (hlarge : P81LargeFieldPolymerSuppressionUniformAt d N_c large beta0)
    (hcluster : P81ClusterExpansionWithHolesUniformAt d N_c cluster beta0) :
    RGCauchyP81Frontier d N_c := by
  exact
    rg_cauchy_p81_frontier_of_audit_packet_and_slot_family d N_c audit
      (p81_slot_family_of_small_large_and_cluster d N_c small large cluster glue)
      hbeta0_pos
      (uniform_slot_family_of_uniform_small_large_and_cluster
        d N_c small large cluster glue hsmall hlarge hcluster)

/-- The theorem-side coherence packet is likewise an immediate downstream consumer. -/
theorem rg_cauchy_p81_coherence_packet_of_audit_packet_and_uniform_small_large_and_cluster
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (large : P81LargeFieldPolymerSuppressionFamily d N_c)
    (cluster : P81ClusterExpansionWithHolesFamily d N_c)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        large.holds β →
        cluster.holds β →
        RGIncrementDecayBound d N_c β)
    {beta0 : ℝ}
    (hbeta0_pos : 0 < beta0)
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small beta0)
    (hlarge : P81LargeFieldPolymerSuppressionUniformAt d N_c large beta0)
    (hcluster : P81ClusterExpansionWithHolesUniformAt d N_c cluster beta0) :
    RGCauchyP81CoherencePacket d N_c := by
  exact
    rg_cauchy_p81_coherence_packet_of_audit_packet_and_slot_family d N_c audit
      (p81_slot_family_of_small_large_and_cluster d N_c small large cluster glue)
      hbeta0_pos
      (uniform_slot_family_of_uniform_small_large_and_cluster
        d N_c small large cluster glue hsmall hlarge hcluster)

end

end YangMills.ClayCore
