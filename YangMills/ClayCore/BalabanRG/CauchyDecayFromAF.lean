import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData
import YangMills.ClayCore.BalabanRG.P91BetaDivergence
import YangMills.ClayCore.BalabanRG.RGCauchySummabilitySkeleton
import YangMills.ClayCore.BalabanRG.CauchyDecayViaBridge
import YangMills.ClayCore.BalabanRG.ConcreteActivityFieldBridge
import YangMills.ClayCore.BalabanRG.FinitePolymerReadout
import YangMills.ClayCore.BalabanRG.PolymerGeometricReadout
import YangMills.ClayCore.BalabanRG.PolymerCanonicalSite
import YangMills.ClayCore.BalabanRG.CauchyDecayViaBridgeFull
import YangMills.ClayCore.BalabanRG.CauchyDecayViaBridgeFiniteFull
import YangMills.ClayCore.BalabanRG.FullCauchySingletonBound

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-!
# CauchyDecayFromAF — Layer 14C (v0.8.81)

Bridge: P91 data → β diverges → rate → 0.
0 sorrys. Takes hβ_upper explicitly.
-/

noncomputable section

/-- AF implies rate decays to 0. 0 sorrys. -/
theorem rate_to_zero_from_af (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) :=
  rate_to_zero_from_p91_data N_c data β r hβ0 hstep hr hβ_upper

/-- Conditional Cauchy decay: given P91RecursionData → Cauchy estimate. 0 sorrys. -/
theorem cauchy_decay_from_p91_data {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (data : P91RecursionData N_c)
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2)
    (hβ_upper : β_k < 2 / balabanBetaCoeff N_c)
    (C_uv : ℝ) (hC : 0 < C_uv)
    (h_uv : ∀ K₁ K₂ : ActivityFamily d (0 : ℕ),
      ActivityNorm.dist (RGBlockingMap d N_c 0 K₁) (RGBlockingMap d N_c 0 K₂)
        ≤ C_uv * ActivityNorm.dist K₁ K₂)
    (h_refine : C_uv ≤ physicalContractionRate β_k)
    (K₁ K₂ : ActivityFamily d (0 : ℕ)) :
    ActivityNorm.dist (RGBlockingMap d N_c 0 K₁) (RGBlockingMap d N_c 0 K₂)
      ≤ physicalContractionRate β_k * ActivityNorm.dist K₁ K₂ :=
  le_trans (h_uv K₁ K₂)
    (mul_le_mul_of_nonneg_right h_refine (ActivityNorm.dist_nonneg K₁ K₂))


/-! ## Bridge Path (v1.0.1-alpha) -/

/-- Bridge-path Cauchy decay at scale 0, consuming RGViaBridgeControl.
    Parallel to cauchy_decay_from_p91_data. Does NOT replace it.
    Uses physicalContractionRate as the Cauchy constant. 0 sorrys. -/
theorem cauchy_decay_from_p91_data_via_bridge {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k : ℝ)
    (ctrl : RGViaBridgeControl d N_c 0 β_k)
    (K₁ K₂ : ActivityFamily d (0 : ℕ)) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c 0 ctrl.bridge β_k K₁).largePart
        (ctrl.bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    physicalContractionRate β_k * ActivityNorm.dist K₁ K₂ :=
  cauchy_summability_bridge_consumer ctrl K₁ K₂
    (physicalContractionRate β_k) (by unfold physicalContractionRate; positivity)



/-- Concrete-bridge Cauchy decay at scale 0.
    Uses the named concreteActivityFieldBridge instance (not abstract).
    First theorem consuming a specific named bridge object. 0 sorrys. -/
theorem cauchy_decay_from_p91_data_via_concrete_bridge {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k : ℝ)
    (K₁ K₂ : ActivityFamily d (0 : ℕ)) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c 0
          (concreteActivityFieldBridge d 0) β_k K₁).largePart
        ((concreteActivityFieldBridge d 0).fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    physicalContractionRate β_k * ActivityNorm.dist K₁ K₂ :=
  cauchy_summability_bridge_consumer
    (d := d) (N_c := N_c) (k := 0) (β := β_k)
    (concreteBridgeControl d N_c 0 β_k) K₁ K₂
    (physicalContractionRate β_k)
    (by unfold physicalContractionRate; positivity)



/-- Cauchy decay at scale 0 via the singleton bridge.
    First high-level theorem using a genuinely non-trivial bridge.
    0 sorrys. -/
theorem cauchy_decay_from_p91_data_via_singleton_bridge {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k : ℝ)
    (p₀ : Polymer d (Int.ofNat 0)) (x₀ : BalabanLatticeSite d 0)
    (K₁ K₂ : ActivityFamily d (0 : ℕ)) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c 0
          (singletonBridge p₀ x₀) β_k K₁).largePart
        ((singletonBridge p₀ x₀).fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    physicalContractionRate β_k * ActivityNorm.dist K₁ K₂ := by
  let ctrl : RGViaBridgeControl d N_c 0 β_k :=
    singletonBridgeControl (d := d) (N_c := N_c) 0 β_k p₀ x₀
  exact cauchy_summability_bridge_consumer
    (d := d) (N_c := N_c) (k := 0) (β := β_k)
    ctrl K₁ K₂
    (physicalContractionRate β_k)
    (by unfold physicalContractionRate; positivity)



/-- Cauchy decay via physical geometric bridge at scale 0.
    Uses toBalabanSite adapter (LatticeSite → BalabanLatticeSite).
    Requires [NeZero d]. 0 sorrys. -/
theorem cauchy_decay_from_p91_data_via_geometric_bridge {d N_c : ℕ}
    [NeZero d] [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k : ℝ)
    (rep : PhysicalPolymerRepSite d 0)
    (polys : Finset (Polymer d (Int.ofNat 0)))
    (K₁ K₂ : ActivityFamily d (0 : ℕ)) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c 0
          (physicalGeometricBridge rep polys) β_k K₁).largePart
        ((physicalGeometricBridge rep polys).fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    physicalContractionRate β_k * ActivityNorm.dist K₁ K₂ := by
  let ctrl : RGViaBridgeControl d N_c 0 β_k :=
    physicalGeometricBridgeControl (d := d) (N_c := N_c) 0 β_k rep polys
  exact cauchy_summability_bridge_consumer
    (d := d) (N_c := N_c) (k := 0) (β := β_k)
    ctrl K₁ K₂
    (physicalContractionRate β_k)
    (by unfold physicalContractionRate; positivity)



/-- Cauchy decay via the canonical geometric bridge at scale 0.
    siteOf = Classical.choose X.nonEmpty (polymer's canonical site).
    First theorem where the bridge is fully determined by polymer geometry.
    Requires [NeZero d]. 0 sorrys. -/
theorem cauchy_decay_from_p91_data_via_canonical_geometric_bridge {d N_c : ℕ}
    [NeZero d] [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k : ℝ)
    (polys : Finset (Polymer d (Int.ofNat 0)))
    (K₁ K₂ : ActivityFamily d (0 : ℕ)) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c 0
          (canonicalGeometricBridge polys) β_k K₁).largePart
        ((canonicalGeometricBridge polys).fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    physicalContractionRate β_k * ActivityNorm.dist K₁ K₂ := by
  let ctrl : RGViaBridgeControl d N_c 0 β_k :=
    canonicalGeometricBridgeControl (d := d) (N_c := N_c) 0 β_k polys
  exact cauchy_summability_bridge_consumer
    (d := d) (N_c := N_c) (k := 0) (β := β_k)
    ctrl K₁ K₂
    (physicalContractionRate β_k)
    (by unfold physicalContractionRate; positivity)



/-- Cauchy decay via the full canonical geometric bridge.
    Uses (ℤ/2^k ℤ)^d geometry (not simplified Fin(2^k)×Fin d).
    Requires RGViaBridgeControlFull — analytic content as hypothesis.
    0 sorrys given the control structure. -/
theorem cauchy_decay_from_p91_data_via_canonical_geometric_bridge_full {d N_c : ℕ}
    [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k : ℝ)
    (ctrl : RGViaBridgeControlFull d N_c 0 β_k)
    (K₁ K₂ : ActivityFamily d (0 : ℕ))
    (x : BalabanFiniteSite d 0) :
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β_k) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β_k * ActivityNorm.dist K₁ K₂) :=
  cauchy_decay_via_full_bridge_control ctrl K₁ K₂ x



/-- Cauchy decay via the finite-support full canonical geometric bridge.
    Uses full (ℤ/2^k ℤ)^d geometry with finite polymer support.
    Requires named finite-support hypotheses through RGViaBridgeControlFull.
    0 sorrys. -/
theorem cauchy_decay_from_p91_data_via_finite_canonical_geometric_bridge_full
    {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k : ℝ)
    (ctrl : RGViaBridgeControlFull d N_c 0 β_k)
    (K₁ K₂ : ActivityFamily d (0 : ℕ))
    (x : BalabanFiniteSite d 0) :
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β_k) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β_k * ActivityNorm.dist K₁ K₂) :=
  cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x



/-- High-level consumer from pointwise singleton full-bridge data.
    Uses pointwise large-field and Cauchy bounds at a singleton polymer,
    then packages them into the full canonical geometric bridge control.
    0 sorrys. -/
theorem cauchy_decay_from_pointwise_singleton_data_via_full_canonical_geometric_bridge
    {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k C_large C_cauchy : ℝ)
    (p₀ : Polymer d (Int.ofNat 0))
    (hlarge : SingletonPointwiseBound d N_c 0 C_large p₀)
    (hlargeC : C_large ≤ Real.exp (-β_k))
    (hcauchy : SingletonPointwiseCauchyBound d N_c 0 C_cauchy p₀)
    (hcauchyC : C_cauchy ≤ physicalContractionRate β_k)
    (K₁ K₂ : ActivityFamily d (0 : ℕ))
    (x : BalabanFiniteSite d 0) :
    let ctrl := singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
      0 β_k C_large C_cauchy p₀ hlarge hlargeC hcauchy hcauchyC
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β_k) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β_k * ActivityNorm.dist K₁ K₂) := by
  intro ctrl
  exact cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x

/-- Zero-field extractor for the pointwise singleton full-bridge control.
    0 sorrys. -/
theorem zero_field_from_pointwise_singleton_data_via_full_canonical_geometric_bridge
    {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k C_large C_cauchy : ℝ)
    (p₀ : Polymer d (Int.ofNat 0))
    (hlarge : SingletonPointwiseBound d N_c 0 C_large p₀)
    (hlargeC : C_large ≤ Real.exp (-β_k))
    (hcauchy : SingletonPointwiseCauchyBound d N_c 0 C_cauchy p₀)
    (hcauchyC : C_cauchy ≤ physicalContractionRate β_k) :
    let ctrl := singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
      0 β_k C_large C_cauchy p₀ hlarge hlargeC hcauchy hcauchyC
    ctrl.core.bridge.fieldOfActivity (fun _ => 0) = fun _ => 0 := by
  intro ctrl
  exact rg_control_full_zero_field ctrl


end

end YangMills.ClayCore