import Mathlib
import YangMills.ClayCore.BalabanRG.FullLargeFieldSuppressionSkeleton
import YangMills.ClayCore.BalabanRG.PolymerCanonicalSiteFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# FullLargeFieldSuppressionSingleton — (v1.0.6-alpha)

Discharges P80 and P81 for the singleton polymer set {p₀}.

## Strategy

`canonicalBridgeFull_field_zero_offsite`:
- prove the singleton filter is empty off-site,
- convert the filtered-sum notation to explicit `Finset.sum`,
- close by rewriting the filter to `∅`.

P80/P81 for general polys: formal debt (needs P78/P80/P81).
-/

noncomputable section

/-! ## Off-site zero -/

/-- The canonical full bridge field is 0 at sites ≠ canonical site of p₀. 0 sorrys. -/
theorem canonicalBridgeFull_field_zero_offsite {d k : ℕ}
    (p₀ : Polymer d (Int.ofNat k)) (K : ActivityFamily d k)
    (x : BalabanFiniteSite d k)
    (hx : x ≠ canonicalBalabanFiniteSite p₀) :
    (canonicalGeometricBridgeFull ({p₀} : Finset (Polymer d (Int.ofNat k)))).fieldOfActivity K x = 0 := by
  have hpx : ¬ siteOfBalabanFull (canonicalPhysicalRepSiteFull d k) p₀ = x := by
    intro h
    apply hx
    simpa [siteOfBalabanFull, canonicalPhysicalRepSiteFull, canonicalBalabanFiniteSite]
      using h.symm

  have hfilter :
      (({p₀} : Finset (Polymer d (Int.ofNat k))).filter
        (fun p => siteOfBalabanFull (canonicalPhysicalRepSiteFull d k) p = x)) = ∅ := by
    ext p
    by_cases hp0 : p = p₀
    · subst hp0
      simp [hpx]
    · simp [hp0]

  have hsum :
      ∑ p ∈ ({p₀} : Finset (Polymer d (Int.ofNat k)))
        with siteOfBalabanFull (canonicalPhysicalRepSiteFull d k) p = x, K p = 0 := by
    change
      Finset.sum
        ((({p₀} : Finset (Polymer d (Int.ofNat k))).filter
          (fun p => siteOfBalabanFull (canonicalPhysicalRepSiteFull d k) p = x)))
        (fun p => K p) = 0
    rw [hfilter]
    simp

  simpa [canonicalGeometricBridgeFull, canonicalGeometricReadoutFull,
    bridgeFromFiniteReadoutFull, geometricFiniteReadoutFull, finiteReadoutFieldFull]
    using hsum

/-! ## P80 bound for singleton -/

/-- P80 for singleton: K(p₀) bounded by exp(-β)·dist(K,0). Named hypothesis. -/
def SingletonFullLargeFieldBound (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (p₀ : Polymer d (Int.ofNat k)) : Prop :=
  ∀ (K : ActivityFamily d k),
    |K p₀| ≤ Real.exp (-β) * ActivityNorm.dist K (fun _ => 0)

/-- P80 discharged from hypothesis. 0 sorrys. -/
theorem singleton_full_large_field_suppression {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (p₀ : Polymer d (Int.ofNat k))
    (hbound : SingletonFullLargeFieldBound d N_c k β p₀) :
    FullLargeFieldSuppressionBound d N_c k β
      (canonicalGeometricBridgeFull ({p₀} : Finset (Polymer d (Int.ofNat k)))) := by
  intro K x
  by_cases hx : x = canonicalBalabanFiniteSite p₀
  · rw [hx, canonicalBridgeFull_field_at_site]
    exact hbound K
  · rw [canonicalBridgeFull_field_zero_offsite p₀ K x hx]
    have hexp : 0 ≤ Real.exp (-β) := by positivity
    have hdist : 0 ≤ ActivityNorm.dist K (fun _ => 0) := ActivityNorm.dist_nonneg _ _
    simpa using mul_nonneg hexp hdist

/-! ## P81 bound for singleton -/

/-- P81 for singleton: |K₁(p₀)-K₂(p₀)| bounded by rate·dist(K₁,K₂). Named hypothesis. -/
def SingletonFullCauchyBound (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (p₀ : Polymer d (Int.ofNat k)) : Prop :=
  ∀ (K₁ K₂ : ActivityFamily d k),
    |K₁ p₀ - K₂ p₀| ≤ physicalContractionRate β * ActivityNorm.dist K₁ K₂

/-- P81 discharged from hypothesis. 0 sorrys. -/
theorem singleton_full_cauchy_summability {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (p₀ : Polymer d (Int.ofNat k))
    (hcauchy : SingletonFullCauchyBound d N_c k β p₀) :
    FullCauchySummabilityBound d N_c k β
      (canonicalGeometricBridgeFull ({p₀} : Finset (Polymer d (Int.ofNat k)))) := by
  intro K₁ K₂ x
  by_cases hx : x = canonicalBalabanFiniteSite p₀
  · rw [hx, canonicalBridgeFull_field_at_site, canonicalBridgeFull_field_at_site]
    exact hcauchy K₁ K₂
  · rw [canonicalBridgeFull_field_zero_offsite p₀ K₁ x hx,
        canonicalBridgeFull_field_zero_offsite p₀ K₂ x hx]
    have hrate : 0 ≤ physicalContractionRate β := by
      unfold physicalContractionRate
      positivity
    have hdist : 0 ≤ ActivityNorm.dist K₁ K₂ := ActivityNorm.dist_nonneg _ _
    simpa using mul_nonneg hrate hdist

/-! ## Full control for singleton -/

/-- First non-trivial filled RGViaBridgeControlFull: {p₀}.
    Both P80+P81 assembled from named hypotheses. 0 sorrys. -/
def singletonCanonicalGeometricBridgeControlFull {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (p₀ : Polymer d (Int.ofNat k))
    (hlarge : SingletonFullLargeFieldBound d N_c k β p₀)
    (hcauchy : SingletonFullCauchyBound d N_c k β p₀) :
    RGViaBridgeControlFull d N_c k β :=
  canonicalGeometricBridgeControlFull_from_bounds k β {p₀}
    (singleton_full_large_field_suppression k β p₀ hlarge)
    (singleton_full_cauchy_summability k β p₀ hcauchy)

end

end YangMills.ClayCore
