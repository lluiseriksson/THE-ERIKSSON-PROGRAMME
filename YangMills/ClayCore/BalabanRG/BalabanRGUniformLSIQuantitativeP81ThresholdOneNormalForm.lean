import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81ThresholdOneCanonicalLiveTargetCoherence

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-- Dedicated theorem-side normal-form hub centralizing all currently equivalent threshold-one
descriptions on the quantitative P81 lane. -/
structure BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] : Prop where
  thresholdOneObstructionBridge :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c
  thresholdOneObstructionCoherence :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionCoherence d N_c
  thresholdOneKernelCoherence :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c
  thresholdOneLiveTargetCoherence :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneLiveTargetCoherence d N_c
  thresholdOneCanonicalLiveTargetCoherence :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneCanonicalLiveTargetCoherence d N_c
  interfaceBridge :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c
  canonicalLiveTargetBridge :
    BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c
  quantitativeFrontier :
    BalabanRGUniformLSIQuantitativeFrontier d N_c
  theoremLiveTarget :
    RGCauchyP81LiveTarget d N_c

/-- Canonical threshold-one normal form from the threshold-one canonical-live-target coherence
hub. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_of_threshold_one_canonical_live_target_coherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (coh : BalabanRGUniformLSIQuantitativeP81ThresholdOneCanonicalLiveTargetCoherence d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c := by
  exact
    ⟨ coh.thresholdOneObstructionCoherence.thresholdOneObstructionBridge,
      coh.thresholdOneObstructionCoherence,
      coh.thresholdOneKernelCoherence,
      coh.thresholdOneLiveTargetCoherence,
      coh,
      coh.interfaceBridge,
      coh.canonicalLiveTargetBridge,
      coh.thresholdOneKernelCoherence.quantitativeFrontier,
      coh.theoremLiveTarget ⟩

/-- Canonical threshold-one normal form from the direct quantitative frontier together with the
theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_of_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (frontier : BalabanRGUniformLSIQuantitativeFrontier d N_c)
    (live : RGCauchyP81LiveTarget d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c := by
  exact
    balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_of_threshold_one_canonical_live_target_coherence
      d N_c
      (balaban_rg_uniform_lsi_quantitative_p81_threshold_one_canonical_live_target_coherence_of_quantitative_frontier_and_live_target
        d N_c frontier live)

/-- Projection to the threshold-one obstruction bridge. -/
theorem threshold_one_obstruction_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (nf : BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c := by
  exact nf.thresholdOneObstructionBridge

/-- Projection to the threshold-one obstruction coherence hub. -/
theorem threshold_one_obstruction_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (nf : BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionCoherence d N_c := by
  exact nf.thresholdOneObstructionCoherence

/-- Projection to the threshold-one kernel coherence hub. -/
theorem threshold_one_kernel_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (nf : BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c := by
  exact nf.thresholdOneKernelCoherence

/-- Projection to the threshold-one live-target coherence hub. -/
theorem threshold_one_live_target_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (nf : BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneLiveTargetCoherence d N_c := by
  exact nf.thresholdOneLiveTargetCoherence

/-- Projection to the threshold-one canonical-live-target coherence hub. -/
theorem threshold_one_canonical_live_target_coherence_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (nf : BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c) :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneCanonicalLiveTargetCoherence d N_c := by
  exact nf.thresholdOneCanonicalLiveTargetCoherence

/-- Projection to the quantitative P81 interface bridge. -/
theorem quantitative_p81_interface_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (nf : BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c) :
    BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  exact nf.interfaceBridge

/-- Projection to the quantitative P81 canonical live-target bridge. -/
theorem quantitative_p81_canonical_live_target_bridge_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (nf : BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c) :
    BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c := by
  exact nf.canonicalLiveTargetBridge

/-- Projection to the direct quantitative frontier. -/
theorem quantitative_frontier_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (nf : BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c) :
    BalabanRGUniformLSIQuantitativeFrontier d N_c := by
  exact nf.quantitativeFrontier

/-- Projection to the theorem-side live target. -/
theorem theorem_live_target_of_balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (nf : BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c) :
    RGCauchyP81LiveTarget d N_c := by
  exact nf.theoremLiveTarget

/-- Logical normal form: the threshold-one normal-form hub is equivalent to the threshold-one
obstruction bridge. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_threshold_one_obstruction_bridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionBridge d N_c := by
  constructor
  · intro nf
    exact nf.thresholdOneObstructionBridge
  · intro bridge
    let coh₀ : BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionCoherence d N_c :=
      (balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_coherence_iff_threshold_one_obstruction_bridge
        d N_c).2 bridge
    let h : BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c :=
      (balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_coherence_iff_quantitative_frontier_and_live_target
        d N_c).1 coh₀
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

/-- Logical normal form: the threshold-one normal-form hub is equivalent to the threshold-one
obstruction coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_threshold_one_obstruction_coherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneObstructionCoherence d N_c := by
  constructor
  · intro nf
    exact nf.thresholdOneObstructionCoherence
  · intro coh
    let h : BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c :=
      (balaban_rg_uniform_lsi_quantitative_p81_threshold_one_obstruction_coherence_iff_quantitative_frontier_and_live_target
        d N_c).1 coh
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

/-- Logical normal form: the threshold-one normal-form hub is equivalent to the threshold-one
kernel coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_threshold_one_kernel_coherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneKernelCoherence d N_c := by
  constructor
  · intro nf
    exact nf.thresholdOneKernelCoherence
  · intro coh
    let h : BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c :=
      (balaban_rg_uniform_lsi_quantitative_p81_threshold_one_kernel_coherence_iff_quantitative_frontier_and_live_target
        d N_c).1 coh
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

/-- Logical normal form: the threshold-one normal-form hub is equivalent to the threshold-one
live-target coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_threshold_one_live_target_coherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneLiveTargetCoherence d N_c := by
  constructor
  · intro nf
    exact nf.thresholdOneLiveTargetCoherence
  · intro coh
    let h : BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c :=
      (balaban_rg_uniform_lsi_quantitative_p81_threshold_one_live_target_coherence_iff_quantitative_frontier_and_live_target
        d N_c).1 coh
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

/-- Logical normal form: the threshold-one normal-form hub is equivalent to the threshold-one
canonical-live-target coherence hub. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_threshold_one_canonical_live_target_coherence
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81ThresholdOneCanonicalLiveTargetCoherence d N_c := by
  constructor
  · intro nf
    exact nf.thresholdOneCanonicalLiveTargetCoherence
  · intro coh
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_of_threshold_one_canonical_live_target_coherence
        d N_c coh

/-- Logical normal form: the threshold-one normal-form hub is equivalent to the quantitative P81
interface bridge. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_quantitative_p81_interface_bridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81InterfaceBridge d N_c := by
  constructor
  · intro nf
    exact nf.interfaceBridge
  · intro bridge
    let h : BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c :=
      (balaban_rg_uniform_lsi_quantitative_p81_interface_bridge_iff_quantitative_frontier_and_live_target
        d N_c).1 bridge
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

/-- Logical normal form: the threshold-one normal-form hub is equivalent to the quantitative P81
canonical live-target bridge. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_quantitative_p81_canonical_live_target_bridge
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      BalabanRGUniformLSIQuantitativeP81CanonicalLiveTargetBridge d N_c := by
  constructor
  · intro nf
    exact nf.canonicalLiveTargetBridge
  · intro bridge
    let h : BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c :=
      (balaban_rg_uniform_lsi_quantitative_p81_canonical_live_target_bridge_iff_quantitative_frontier_and_live_target
        d N_c).1 bridge
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

/-- Logical normal form: the threshold-one normal-form hub is equivalent to the pair consisting
of the direct quantitative frontier and the theorem-side live target. -/
theorem balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_iff_quantitative_frontier_and_live_target
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm d N_c ↔
      (BalabanRGUniformLSIQuantitativeFrontier d N_c ∧ RGCauchyP81LiveTarget d N_c) := by
  constructor
  · intro nf
    exact ⟨nf.quantitativeFrontier, nf.theoremLiveTarget⟩
  · intro h
    exact
      balaban_rg_uniform_lsi_quantitative_p81_threshold_one_normal_form_of_quantitative_frontier_and_live_target
        d N_c h.1 h.2

end

end YangMills.ClayCore
