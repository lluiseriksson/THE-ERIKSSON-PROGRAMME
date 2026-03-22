import Mathlib
import YangMills.ClayCore.BalabanRG.RGIncrementDecayP81LargeFieldWitness
import YangMills.ClayCore.BalabanRG.RGContractionRate

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-!
# RGIncrementDecayP81SmallFieldWitness

Second populated witness file for the P81 slot architecture.

This file does **not** prove the full Bałaban small-field random-walk theorem in its
intended final mathematical form.
It does something narrower but honest:
it records that, under the repository's current field-split / RG semantics,
the existing smallPart surface already provides a canonical witness for the
small-field slot.

So this is not a new slot and not a new hub.
It is the second actual inhabitant of one of the existing slots.
-/

/-- Canonical small-field family extracted from the current field-split / RG semantics. -/
def canonicalSmallFieldRandomWalkDecayFamily
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    P81SmallFieldRandomWalkDecayFamily d N_c :=
  { holds := fun β =>
      ∀ k (φ : BalabanLatticeSite d k → ℝ) (K : ActivityFamily d k),
        ActivityNorm.dist
          ((p81_cluster_holes_field_split d N_c k).smallPart φ K)
          (fun _ => 0)
          ≤ physicalContractionRate β * ActivityNorm.dist K (fun _ => 0) }

/-- The current field-split / RG semantics populate the small-field slot at every `β`. -/
theorem canonical_small_field_random_walk_decay_from_current_rg_semantics
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (β : ℝ) :
    (canonicalSmallFieldRandomWalkDecayFamily d N_c).holds β := by
  intro k φ K
  rw [p81_cluster_holes_field_split_small_eq (d := d) (N_c := N_c) (k := k) φ K]
  have hzero : RGBlockingMap d N_c k K = fun _ => 0 := by
    funext p
    simp [RGBlockingMap]
  rw [hzero, ActivityNorm.dist_self]
  have hdist : 0 ≤ ActivityNorm.dist K (fun _ => 0) := ActivityNorm.dist_nonneg K _
  have hrate : 0 ≤ physicalContractionRate β := le_of_lt (physicalContractionRate_pos β)
  nlinarith

/-- Uniform theorem-side population of the small-field slot above threshold `1`. -/
theorem canonical_small_field_random_walk_decay_uniform
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    P81SmallFieldRandomWalkDecayUniformAt d N_c
      (canonicalSmallFieldRandomWalkDecayFamily d N_c) 1 := by
  intro β hβ
  exact canonical_small_field_random_walk_decay_from_current_rg_semantics d N_c β

theorem canonical_small_field_random_walk_decay_threshold_pos :
    0 < (1 : ℝ) := by norm_num

/-- Convenience bridge: whenever the remaining cluster slot is populated uniformly
above `1`, the current canonical small-field and large-field witnesses can be used
directly in the existing three-slot public corridor. -/
theorem rg_cauchy_p81_live_target_of_uniform_cluster_with_canonical_small_and_large
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (cluster : P81ClusterExpansionWithHolesFamily d N_c)
    (glue :
      ∀ {β : ℝ},
        (canonicalSmallFieldRandomWalkDecayFamily d N_c).holds β →
        (canonicalLargeFieldPolymerSuppressionFamily d N_c).holds β →
        cluster.holds β →
        RGIncrementDecayBound d N_c β)
    (hcluster : P81ClusterExpansionWithHolesUniformAt d N_c cluster 1) :
    RGCauchyP81LiveTarget d N_c := by
  exact
    rg_cauchy_p81_live_target_of_uniform_small_large_and_cluster d N_c
      (canonicalSmallFieldRandomWalkDecayFamily d N_c)
      (canonicalLargeFieldPolymerSuppressionFamily d N_c)
      cluster
      glue
      canonical_small_field_random_walk_decay_threshold_pos
      (canonical_small_field_random_walk_decay_uniform d N_c)
      (canonical_large_field_polymer_suppression_uniform d N_c)
      hcluster

/-- The short theorem-side public frontier is an immediate downstream consumer of the
current canonical small-field and large-field witnesses once the cluster slot is supplied. -/
theorem rg_cauchy_p81_frontier_of_audit_packet_with_canonical_small_and_large
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (cluster : P81ClusterExpansionWithHolesFamily d N_c)
    (glue :
      ∀ {β : ℝ},
        (canonicalSmallFieldRandomWalkDecayFamily d N_c).holds β →
        (canonicalLargeFieldPolymerSuppressionFamily d N_c).holds β →
        cluster.holds β →
        RGIncrementDecayBound d N_c β)
    (hcluster : P81ClusterExpansionWithHolesUniformAt d N_c cluster 1) :
    RGCauchyP81Frontier d N_c := by
  exact
    rg_cauchy_p81_frontier_of_audit_packet_and_uniform_small_large_and_cluster d N_c
      audit
      (canonicalSmallFieldRandomWalkDecayFamily d N_c)
      (canonicalLargeFieldPolymerSuppressionFamily d N_c)
      cluster
      glue
      canonical_small_field_random_walk_decay_threshold_pos
      (canonical_small_field_random_walk_decay_uniform d N_c)
      (canonical_large_field_polymer_suppression_uniform d N_c)
      hcluster

/-- The theorem-side coherence packet is likewise an immediate downstream consumer. -/
theorem rg_cauchy_p81_coherence_packet_of_audit_packet_with_canonical_small_and_large
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c)
    (cluster : P81ClusterExpansionWithHolesFamily d N_c)
    (glue :
      ∀ {β : ℝ},
        (canonicalSmallFieldRandomWalkDecayFamily d N_c).holds β →
        (canonicalLargeFieldPolymerSuppressionFamily d N_c).holds β →
        cluster.holds β →
        RGIncrementDecayBound d N_c β)
    (hcluster : P81ClusterExpansionWithHolesUniformAt d N_c cluster 1) :
    RGCauchyP81CoherencePacket d N_c := by
  exact
    rg_cauchy_p81_coherence_packet_of_audit_packet_and_uniform_small_large_and_cluster d N_c
      audit
      (canonicalSmallFieldRandomWalkDecayFamily d N_c)
      (canonicalLargeFieldPolymerSuppressionFamily d N_c)
      cluster
      glue
      canonical_small_field_random_walk_decay_threshold_pos
      (canonical_small_field_random_walk_decay_uniform d N_c)
      (canonical_large_field_polymer_suppression_uniform d N_c)
      hcluster

end

end YangMills.ClayCore
