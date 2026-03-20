import Mathlib
import YangMills.ClayCore.BalabanRG.FullLargeFieldSuppressionSingleton
import YangMills.ClayCore.BalabanRG.PolymerCanonicalSiteFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# FullLargeFieldSuppressionFinite — (v1.0.7-alpha)

Finite-support full-geometry control under named hypotheses.

This file extends the progression
  ∅  →  {p₀}  →  polys : Finset (Polymer ...)
for the full (ℤ/2^k ℤ)^d bridge path.

Design:
- define finite-support P80/P81 named hypotheses,
- wrap them into FullLargeFieldSuppressionBound / FullCauchySummabilityBound,
- package them as RGViaBridgeControlFull,
- provide empty/singleton finite packaged controls.
-/

noncomputable section

/-! ## Finite-support named hypotheses -/

/-- Finite-support P80 hypothesis for the full bridge. -/
def FiniteFullLargeFieldBound (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (polys : Finset (Polymer d (Int.ofNat k))) : Prop :=
  ∀ (K : ActivityFamily d k) (x : BalabanFiniteSite d k),
    |(canonicalGeometricBridgeFull polys).fieldOfActivity K x| ≤
      Real.exp (-β) * ActivityNorm.dist K (fun _ => 0)

/-- Finite-support P81 hypothesis for the full bridge. -/
def FiniteFullCauchyBound (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (polys : Finset (Polymer d (Int.ofNat k))) : Prop :=
  ∀ (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k),
    |(canonicalGeometricBridgeFull polys).fieldOfActivity K₁ x -
      (canonicalGeometricBridgeFull polys).fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂

/-! ## Tautological wrappers into the full API -/

/-- Finite-support P80 wrapper. 0 sorrys. -/
theorem finite_full_large_field_suppression {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    {polys : Finset (Polymer d (Int.ofNat k))}
    (hlarge : FiniteFullLargeFieldBound d N_c k β polys) :
    FullLargeFieldSuppressionBound d N_c k β
      (canonicalGeometricBridgeFull polys) :=
  hlarge

/-- Finite-support P81 wrapper. 0 sorrys. -/
theorem finite_full_cauchy_summability {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    {polys : Finset (Polymer d (Int.ofNat k))}
    (hcauchy : FiniteFullCauchyBound d N_c k β polys) :
    FullCauchySummabilityBound d N_c k β
      (canonicalGeometricBridgeFull polys) :=
  hcauchy

/-! ## Finite packaged control -/

/-- Finite-support full bridge control package. 0 sorrys. -/
def finiteCanonicalGeometricBridgeControlFull {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (hlarge : FiniteFullLargeFieldBound d N_c k β polys)
    (hcauchy : FiniteFullCauchyBound d N_c k β polys) :
    RGViaBridgeControlFull d N_c k β :=
  canonicalGeometricBridgeControlFull_from_bounds k β polys
    (finite_full_large_field_suppression hlarge)
    (finite_full_cauchy_summability hcauchy)

/-! ## Empty and singleton packaged specializations -/

/-- Empty-support finite packaged control. 0 sorrys. -/
def emptyFiniteCanonicalGeometricBridgeControlFull {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ) :
    RGViaBridgeControlFull d N_c k β :=
  finiteCanonicalGeometricBridgeControlFull
    (d := d) (N_c := N_c) k β
    (∅ : Finset (Polymer d (Int.ofNat k)))
    (empty_full_large_field_suppression (d := d) (N_c := N_c) k β)
    (empty_full_cauchy_summability (d := d) (N_c := N_c) k β)

/-- Singleton P80 hypothesis upgrades to the finite-support P80 hypothesis on {p₀}. 0 sorrys. -/
theorem singleton_large_to_finite {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (p₀ : Polymer d (Int.ofNat k))
    (hlarge : SingletonFullLargeFieldBound d N_c k β p₀) :
    FiniteFullLargeFieldBound d N_c k β ({p₀} : Finset (Polymer d (Int.ofNat k))) := by
  intro K x
  exact singleton_full_large_field_suppression
    (d := d) (N_c := N_c) k β p₀ hlarge K x

/-- Singleton P81 hypothesis upgrades to the finite-support P81 hypothesis on {p₀}. 0 sorrys. -/
theorem singleton_cauchy_to_finite {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (p₀ : Polymer d (Int.ofNat k))
    (hcauchy : SingletonFullCauchyBound d N_c k β p₀) :
    FiniteFullCauchyBound d N_c k β ({p₀} : Finset (Polymer d (Int.ofNat k))) := by
  intro K₁ K₂ x
  exact singleton_full_cauchy_summability
    (d := d) (N_c := N_c) k β p₀ hcauchy K₁ K₂ x

/-- Singleton-support finite packaged control. 0 sorrys. -/
def singletonFiniteCanonicalGeometricBridgeControlFull {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (p₀ : Polymer d (Int.ofNat k))
    (hlarge : SingletonFullLargeFieldBound d N_c k β p₀)
    (hcauchy : SingletonFullCauchyBound d N_c k β p₀) :
    RGViaBridgeControlFull d N_c k β :=
  finiteCanonicalGeometricBridgeControlFull
    (d := d) (N_c := N_c) k β
    ({p₀} : Finset (Polymer d (Int.ofNat k)))
    (singleton_large_to_finite (d := d) (N_c := N_c) k β p₀ hlarge)
    (singleton_cauchy_to_finite (d := d) (N_c := N_c) k β p₀ hcauchy)

end

end YangMills.ClayCore
