import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Canonical public registry recording that all currently exported threshold-one theorem-side
names on the quantitative P81 lane encode the same remaining obstruction. -/
structure BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  normalFormToThresholdOneObstructionBridge :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c
  normalFormToThresholdOneObstructionCoherence :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionCoherence d N_c
  normalFormToThresholdOneKernelCoherence :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c
  normalFormToThresholdOneLiveTargetCoherence :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneLiveTargetCoherence d N_c
  normalFormToThresholdOneCanonicalLiveTargetCoherence :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneCanonicalLiveTargetCoherence d N_c
  normalFormToQuantitativeP81InterfaceBridge :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c
  normalFormToQuantitativeP81CanonicalLiveTargetBridge :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c
  normalFormToQuantitativeFrontierAndLiveTarget :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c)

/-- The current threshold-one theorem-side names admit a single canonical equivalence registry. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_equivalence_registry
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry d N_c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_threshold_one_obstruction_bridge
        d N_c
  · exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_threshold_one_obstruction_coherence
        d N_c
  · exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_threshold_one_kernel_coherence
        d N_c
  · exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_threshold_one_live_target_coherence
        d N_c
  · exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_threshold_one_canonical_live_target_coherence
        d N_c
  · exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_quantitative_p81_interface_bridge
        d N_c
  · exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_quantitative_p81_canonical_live_target_bridge
        d N_c
  · exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_quantitative_frontier_and_live_target
        d N_c

/-- Projection to the threshold-one obstruction bridge equivalence. -/
theorem normal_form_to_threshold_one_obstruction_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_equivalence_registry
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (reg : BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c := by
  exact reg.normalFormToThresholdOneObstructionBridge

/-- Projection to the threshold-one obstruction coherence equivalence. -/
theorem normal_form_to_threshold_one_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_equivalence_registry
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (reg : BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionCoherence d N_c := by
  exact reg.normalFormToThresholdOneObstructionCoherence

/-- Projection to the threshold-one kernel coherence equivalence. -/
theorem normal_form_to_threshold_one_kernel_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_equivalence_registry
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (reg : BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c := by
  exact reg.normalFormToThresholdOneKernelCoherence

/-- Projection to the threshold-one live-target coherence equivalence. -/
theorem normal_form_to_threshold_one_live_target_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_equivalence_registry
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (reg : BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneLiveTargetCoherence d N_c := by
  exact reg.normalFormToThresholdOneLiveTargetCoherence

/-- Projection to the threshold-one canonical-live-target coherence equivalence. -/
theorem normal_form_to_threshold_one_canonical_live_target_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_equivalence_registry
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (reg : BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneCanonicalLiveTargetCoherence d N_c := by
  exact reg.normalFormToThresholdOneCanonicalLiveTargetCoherence

/-- Projection to the quantitative P81 interface bridge equivalence. -/
theorem normal_form_to_quantitative_p81_interface_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_equivalence_registry
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (reg : BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact reg.normalFormToQuantitativeP81InterfaceBridge

/-- Projection to the quantitative P81 canonical live-target bridge equivalence. -/
theorem normal_form_to_quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_equivalence_registry
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (reg : BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c := by
  exact reg.normalFormToQuantitativeP81CanonicalLiveTargetBridge

/-- Projection to the quantitative-frontier/theorem-live-target equivalence. -/
theorem normal_form_to_quantitative_frontier_and_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_equivalence_registry
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (reg : BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  exact reg.normalFormToQuantitativeFrontierAndLiveTarget

end

end YangMills.ClayCore
