import Mathlib
import YangMills.ClayCore.BalabanRG.RGIncrementDecayP81SmallFieldWitness
import YangMills.ClayCore.BalabanRG.RGContractionRate

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-!
# RGIncrementDecayP81ClusterExpansionWitness

Third populated witness file for the P81 slot architecture.

This file does **not** prove the full Bałaban / Dimock cluster-expansion-with-holes
theorem in its intended final mathematical form.
It does something narrower but honest:
it records that, under the repository's current hole-split semantics,
the existing `largePart = 0` surface already provides a canonical witness for the
cluster-expansion slot.

So this is not a new slot and not a new hub.
It is the third actual inhabitant of one of the existing slots.
-/

/-- Canonical cluster-expansion family extracted from the current hole-split semantics. -/
def canonicalClusterExpansionWithHolesFamily
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    P81ClusterExpansionWithHolesFamily d N_c :=
  { holds := fun β =>
      ∀ k (φ : BalabanLatticeSite d k → ℝ) (K : ActivityFamily d k),
        ActivityNorm.dist
          ((p81_cluster_holes_field_split d N_c k).largePart φ K)
          (fun _ => 0)
          ≤ physicalContractionRate β * ActivityNorm.dist K (fun _ => 0) }

/-- The current hole-split semantics populate the cluster-expansion slot at every `β`. -/
theorem canonical_cluster_expansion_with_holes_from_current_semantics
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (β : ℝ) :
    (canonicalClusterExpansionWithHolesFamily d N_c).holds β := by
  intro k φ K
  rw [p81_cluster_holes_field_split_large_zero (d := d) (N_c := N_c) (k := k) φ K]
  rw [ActivityNorm.dist_self]
  have hdist : 0 ≤ ActivityNorm.dist K (fun _ => 0) := ActivityNorm.dist_nonneg K _
  have hrate : 0 ≤ physicalContractionRate β := le_of_lt (physicalContractionRate_pos β)
  nlinarith

/-- Uniform theorem-side population of the cluster slot above threshold `1`. -/
theorem canonical_cluster_expansion_with_holes_uniform
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    P81ClusterExpansionWithHolesUniformAt d N_c
      (canonicalClusterExpansionWithHolesFamily d N_c) 1 := by
  intro β hβ
  exact canonical_cluster_expansion_with_holes_from_current_semantics d N_c β

theorem canonical_cluster_expansion_with_holes_threshold_pos :
    0 < (1 : ℝ) := by norm_num

/-- Convenience bridge: if the actual final glue is provided, the three canonical
witnesses already discharge the theorem-side live target. -/
theorem rg_cauchy_p81_live_target_of_canonical_small_large_cluster_and_glue
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (glue :
      ∀ {β : ℝ},
        (canonicalSmallFieldRandomWalkDecayFamily d N_c).holds β →
        (canonicalLargeFieldPolymerSuppressionFamily d N_c).holds β →
        (canonicalClusterExpansionWithHolesFamily d N_c).holds β →
        RGIncrementDecayBound d N_c β) :
    RGCauchyP81LiveTarget d N_c := by
  exact
    rg_cauchy_p81_live_target_of_uniform_small_large_and_cluster d N_c
      (canonicalSmallFieldRandomWalkDecayFamily d N_c)
      (canonicalLargeFieldPolymerSuppressionFamily d N_c)
      (canonicalClusterExpansionWithHolesFamily d N_c)
      glue
      canonical_cluster_expansion_with_holes_threshold_pos
      (canonical_small_field_random_walk_decay_uniform d N_c)
      (canonical_large_field_polymer_suppression_uniform d N_c)
      (canonical_cluster_expansion_with_holes_uniform d N_c)

/-- The public frontier likewise becomes an immediate downstream consumer once the
actual final glue is supplied. -/
theorem rg_cauchy_p81_frontier_of_audit_packet_with_canonical_small_large_cluster_and_glue
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (glue :
      ∀ {β : ℝ},
        (canonicalSmallFieldRandomWalkDecayFamily d N_c).holds β →
        (canonicalLargeFieldPolymerSuppressionFamily d N_c).holds β →
        (canonicalClusterExpansionWithHolesFamily d N_c).holds β →
        RGIncrementDecayBound d N_c β) :
    RGCauchyP81Frontier d N_c := by
  exact
    rg_cauchy_p81_frontier_of_audit_packet_and_uniform_small_large_and_cluster d N_c
      audit
      (canonicalSmallFieldRandomWalkDecayFamily d N_c)
      (canonicalLargeFieldPolymerSuppressionFamily d N_c)
      (canonicalClusterExpansionWithHolesFamily d N_c)
      glue
      canonical_cluster_expansion_with_holes_threshold_pos
      (canonical_small_field_random_walk_decay_uniform d N_c)
      (canonical_large_field_polymer_suppression_uniform d N_c)
      (canonical_cluster_expansion_with_holes_uniform d N_c)

/-- The theorem-side coherence packet is likewise an immediate downstream consumer. -/
theorem rg_cauchy_p81_coherence_packet_of_audit_packet_with_canonical_small_large_cluster_and_glue
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (glue :
      ∀ {β : ℝ},
        (canonicalSmallFieldRandomWalkDecayFamily d N_c).holds β →
        (canonicalLargeFieldPolymerSuppressionFamily d N_c).holds β →
        (canonicalClusterExpansionWithHolesFamily d N_c).holds β →
        RGIncrementDecayBound d N_c β) :
    RGCauchyP81CoherencePacket d N_c := by
  exact
    rg_cauchy_p81_coherence_packet_of_audit_packet_and_uniform_small_large_and_cluster d N_c
      audit
      (canonicalSmallFieldRandomWalkDecayFamily d N_c)
      (canonicalLargeFieldPolymerSuppressionFamily d N_c)
      (canonicalClusterExpansionWithHolesFamily d N_c)
      glue
      canonical_cluster_expansion_with_holes_threshold_pos
      (canonical_small_field_random_walk_decay_uniform d N_c)
      (canonical_large_field_polymer_suppression_uniform d N_c)
      (canonical_cluster_expansion_with_holes_uniform d N_c)

end

end YangMills.ClayCore
