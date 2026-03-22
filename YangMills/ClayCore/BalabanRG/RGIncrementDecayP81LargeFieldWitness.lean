import Mathlib
import YangMills.ClayCore.BalabanRG.RGIncrementDecayP81ClusterExpansionSlot
import YangMills.ClayCore.BalabanRG.P80EstimateSkeleton

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-!
# RGIncrementDecayP81LargeFieldWitness

First populated witness file for the P81 slot architecture.

This file does **not** prove the full Bałaban large-field theorem in its intended final
mathematical form.
It does something narrower but honest:
it records that, under the repository's current RG semantics, the existing 0-sorry
P80 skeleton already provides a canonical witness for the large-field suppression slot.

So this is not a new slot and not a new hub.
It is the first actual inhabitant of one of the existing slots.
-/

/-- Canonical large-field suppression family extracted from the current theorem-side
P80 skeleton. -/
def canonicalLargeFieldPolymerSuppressionFamily
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    P81LargeFieldPolymerSuppressionFamily d N_c :=
  { holds := fun β => LargeFieldSuppressionBound d N_c β }

/-- The current 0-sorry P80 skeleton populates the large-field slot at every `β ≥ 1`. -/
theorem canonical_large_field_polymer_suppression_from_p80_skeleton
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (β : ℝ) (hβ : 1 ≤ β) :
    (canonicalLargeFieldPolymerSuppressionFamily d N_c).holds β := by
  exact
    large_field_suppression_from_P80_steps d N_c β hβ
      (fun k => large_field_decomposition_P80_step1 d N_c β hβ k)
      (fun k split h_lf K =>
        large_field_exponential_suppression_P80_step2 d N_c β hβ k split h_lf K)

/-- Uniform theorem-side population of the large-field slot above threshold `1`. -/
theorem canonical_large_field_polymer_suppression_uniform
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    P81LargeFieldPolymerSuppressionUniformAt d N_c
      (canonicalLargeFieldPolymerSuppressionFamily d N_c) 1 := by
  intro β hβ
  exact canonical_large_field_polymer_suppression_from_p80_skeleton d N_c β hβ

theorem canonical_large_field_polymer_suppression_threshold_pos :
    0 < (1 : ℝ) := by norm_num

/-- Convenience bridge: whenever the remaining two slots are populated uniformly above
`1`, the current canonical large-field witness can be used directly in the existing
three-slot public corridor. -/
theorem rg_cauchy_p81_live_target_of_uniform_small_and_cluster_with_canonical_large_field
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (cluster : P81ClusterExpansionWithHolesFamily d N_c)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        (canonicalLargeFieldPolymerSuppressionFamily d N_c).holds β →
        cluster.holds β →
        RGIncrementDecayBound d N_c β)
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small 1)
    (hcluster : P81ClusterExpansionWithHolesUniformAt d N_c cluster 1) :
    RGCauchyP81LiveTarget d N_c := by
  exact
    rg_cauchy_p81_live_target_of_uniform_small_large_and_cluster d N_c
      small
      (canonicalLargeFieldPolymerSuppressionFamily d N_c)
      cluster
      glue
      canonical_large_field_polymer_suppression_threshold_pos
      hsmall
      (canonical_large_field_polymer_suppression_uniform d N_c)
      hcluster

/-- The short theorem-side public frontier is an immediate downstream consumer of the
current canonical large-field witness once the other two slots are supplied. -/
theorem rg_cauchy_p81_frontier_of_audit_packet_with_canonical_large_field
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (cluster : P81ClusterExpansionWithHolesFamily d N_c)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        (canonicalLargeFieldPolymerSuppressionFamily d N_c).holds β →
        cluster.holds β →
        RGIncrementDecayBound d N_c β)
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small 1)
    (hcluster : P81ClusterExpansionWithHolesUniformAt d N_c cluster 1) :
    RGCauchyP81Frontier d N_c := by
  exact
    rg_cauchy_p81_frontier_of_audit_packet_and_uniform_small_large_and_cluster d N_c
      audit
      small
      (canonicalLargeFieldPolymerSuppressionFamily d N_c)
      cluster
      glue
      canonical_large_field_polymer_suppression_threshold_pos
      hsmall
      (canonical_large_field_polymer_suppression_uniform d N_c)
      hcluster

/-- The theorem-side coherence packet is likewise an immediate downstream consumer. -/
theorem rg_cauchy_p81_coherence_packet_of_audit_packet_with_canonical_large_field
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (small : P81SmallFieldRandomWalkDecayFamily d N_c)
    (cluster : P81ClusterExpansionWithHolesFamily d N_c)
    (glue :
      ∀ {β : ℝ},
        small.holds β →
        (canonicalLargeFieldPolymerSuppressionFamily d N_c).holds β →
        cluster.holds β →
        RGIncrementDecayBound d N_c β)
    (hsmall : P81SmallFieldRandomWalkDecayUniformAt d N_c small 1)
    (hcluster : P81ClusterExpansionWithHolesUniformAt d N_c cluster 1) :
    RGCauchyP81CoherencePacket d N_c := by
  exact
    rg_cauchy_p81_coherence_packet_of_audit_packet_and_uniform_small_large_and_cluster d N_c
      audit
      small
      (canonicalLargeFieldPolymerSuppressionFamily d N_c)
      cluster
      glue
      canonical_large_field_polymer_suppression_threshold_pos
      hsmall
      (canonical_large_field_polymer_suppression_uniform d N_c)
      hcluster

end

end YangMills.ClayCore
