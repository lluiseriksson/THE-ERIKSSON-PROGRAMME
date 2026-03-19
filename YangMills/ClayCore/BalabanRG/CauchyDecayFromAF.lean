import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData
import YangMills.ClayCore.BalabanRG.P91BetaDivergence
import YangMills.ClayCore.BalabanRG.RGCauchySummabilitySkeleton
import YangMills.ClayCore.BalabanRG.CauchyDecayViaBridge
import YangMills.ClayCore.BalabanRG.ConcreteActivityFieldBridge

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


end

end YangMills.ClayCore
