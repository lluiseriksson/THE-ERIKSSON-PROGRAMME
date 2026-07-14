/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpCardTilt
import YangMills.RG.AppendixFHsharpSourceResidualCanonicalRoot

/-!
# Raw metric decay to the active-skeleton KP criterion

This module composes the source-facing canonical-root theorem for the actual
integrated Appendix-F `H#` activity with the bounded-hole cardinality-tilt
bridge.  It removes the intermediate residual-`H#` hypothesis from callers:

`raw metric activity decay -> integrated K# -> residual H# -> local KP`.

All genuinely analytic inputs remain explicit: the raw activity estimate,
probability measures, half-budget, scalar profile, hole geometry, bounded-hole
substitute, and final scalar KP smallness.  No Yang--Mills fluctuation estimate
is manufactured here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open MeasureTheory

/-- **Source-facing raw-to-KP closure.**  At the theta-shifted B3 rate, the
canonical-root integrated `H#` residual theorem supplies the activity profile
needed by the volume-uniform active-skeleton KP criterion. -/
theorem
    omegaHolePolymerSystem_KPCriterion_of_rawMetricDecay_canonicalRoot_boundedHoles
    {d L lieDim : ℕ} [NeZero L]
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (g : ℕ → ℝ)
    (Hraw : ℕ → ℕ → ℝ)
    (B : ℕ) (t₀ kScale : ℕ)
    (C Hscale c₀ κ₀ s A : ℝ)
    (hκ₀ : 0 < κ₀)
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hHraw : ∀ t k, 0 ≤ Hraw t k)
    (hHraw_one : ∀ t k, Hraw t k ≤ 1)
    (hhalf : ∀ t k,
      appendixFSecondUrsellLeafConstant d κ₀ *
          (2 * Hraw t k * appendixFHoleRootSumConstant d κ₀) ≤ 1 / 2)
    (hprofile : ∀ t k,
      4 * appendixFSecondUrsellMomentConstant d κ₀ *
          Hraw t k * appendixFHoleRootSumConstant d κ₀ ≤
        C * Hscale * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        Hraw t k * appendixFHoleExpWeight HF
          (4 * κ₀ + 3 + boundedHoleCardinalityTilt d B) X.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hB : ∀ H₀ ∈ HF.holes, H₀.card ≤ B)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 *
      (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hAmp0 : 0 ≤ C * Hscale * Real.exp (-(c₀ * (t₀ : ℝ))) * g kScale ^ κ₀)
    (hA0 : 0 ≤ A)
    (hA : Real.exp s *
        (C * Hscale * Real.exp (-(c₀ * (t₀ : ℝ))) * g kScale ^ κ₀) ≤ A)
    (hsmall : A *
      (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
        (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹ ≤ 1) :
    let zK : Finset (Cube d L) → ℂ :=
      balabanCMP116AppendixFIntegratedKsharpActivityFamily HF z Λ F ν t₀ kScale
    let zH : Finset (Cube d L) → ℂ := appendixFHoleHsharp HF zK
    KP.KPCriterion
      ((omegaHolePolymerSystem HF zH).scaleActivity (Real.exp s))
      (fun Y => (Y.val.card : ℝ)) := by
  let theta : ℝ := boundedHoleCardinalityTilt d B
  let κ : ℝ := 4 * κ₀ + 3 + theta
  let zK : Finset (Cube d L) → ℂ :=
    balabanCMP116AppendixFIntegratedKsharpActivityFamily HF z Λ F ν t₀ kScale
  let zH : Finset (Cube d L) → ℂ := appendixFHoleHsharp HF zK
  let amp : ℝ :=
    C * Hscale * Real.exp (-(c₀ * (t₀ : ℝ))) * g kScale ^ κ₀
  have htheta0 : 0 ≤ theta := by
    unfold theta boundedHoleCardinalityTilt
    positivity
  have hmargin : 3 * κ₀ + 3 ≤ κ := by
    unfold κ
    linarith
  have hresidual :=
    norm_appendixFHoleHsharp_le_residual_of_rawMetricDecay_canonicalRoot_halfBudget_of_source
      (d := d) (L := L) (lieDim := lieDim) (β := β)
      HF zH z Λ F ν g Hraw
      (C := C) (Hscale := Hscale) (c₀ := c₀) (κ := κ) (κ₀ := κ₀)
      hmargin hκ₀ hν hHraw hHraw_one hhalf hprofile
      (by
        intro t k ψ φ X hX
        simpa [κ, theta] using hraw t k ψ φ X hX)
      hdisj hnoedges hholes_ne hCq
  exact
    omegaHolePolymerSystem_KPCriterion_of_Hsharp_residual_bounded_holes
      HF zH B κ₀ s amp A hdisj hnoedges hholes_ne hB hAmp0 hA0 hA
      (by
        intro Y
        simpa [zH, zK, amp, κ, theta, appendixFHoleExpWeight] using
          hresidual t₀ kScale Y)
      hCq hsmall

end YangMills.RG
