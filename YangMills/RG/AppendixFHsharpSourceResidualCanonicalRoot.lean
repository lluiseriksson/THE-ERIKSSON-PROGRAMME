/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFKsharpCanonicalRoot
import YangMills.RG.AppendixFHsharpSourceResidual

/-!
# Appendix F residual `H#` estimate from raw decay and canonical root budget

This module composes the canonical-root `K#` source estimate with the all-tail
residual `H#` estimate.  It removes the intermediate `hactivityKsharp` caller
obligation from the CMP116 integrated normal form.

Honest scope: the raw metric decay estimate, the second-Ursell half-budget, the
final profile inequality, source constants, and hole geometry remain explicit.
This is source-facing composition only; it does not prove those analytic inputs
from Dimock/Balaban source text.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

variable {d L : ℕ} [NeZero L]

open MeasureTheory

/-- CMP116 integrated residual `H#` estimate from raw metric decay, the canonical
root budget, and the second-Ursell half-budget/profile inequalities.

Compared with
`norm_appendixFHoleHsharp_le_residual_of_dimockII_appendixF_halfBudget`, the
caller no longer supplies the intermediate `hactivityKsharp` estimate for the
second-Ursell activity.  It is derived from
`balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_canonicalRoot_halfBudget_of_source`.

The remaining source-facing inputs are exactly the raw metric activity bound,
the canonical-root half-budget, the final profile inequality, and the
hole-geometry hypotheses. -/
theorem
    norm_appendixFHoleHsharp_le_residual_of_rawMetricDecay_canonicalRoot_halfBudget_of_source
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (g : ℕ → ℝ)
    (Hraw : ℕ → ℕ → ℝ)
    {C Hscale c₀ κ κ₀ : ℝ}
    (hmargin : 3 * κ₀ + 3 ≤ κ)
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
        Hraw t k * appendixFHoleExpWeight HF κ X.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      ‖appendixFHoleHsharp HF
          (balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k) P.val‖ ≤
        C * Hscale * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  let zK : ℕ → ℕ → Finset (Cube d L) → ℂ :=
    fun t k =>
      balabanCMP116AppendixFIntegratedKsharpActivityFamily HF z Λ F ν t k
  let rootBudget : ℕ → ℕ → ℝ :=
    fun _ _ => appendixFHoleRootSumConstant d κ₀
  have hroot0 : ∀ t k, 0 ≤ rootBudget t k := by
    intro t k
    exact appendixFHoleRootSumConstant_nonneg_of_hCq hCq
  have hκ₀_nonneg : 0 ≤ κ₀ := le_of_lt hκ₀
  have hκ : κ₀ ≤ κ := by
    linarith
  have hactivityKsharp :
      ∀ t k (Q : OmegaPolymerType HF (zK t k)),
        ‖zK t k Q.val‖ ≤
          (2 * Hraw t k * rootBudget t k) *
            appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Q.val := by
    intro t k Q
    simpa [zK, rootBudget] using
      (balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_canonicalRoot_halfBudget_of_source
        (d := d) (L := L) (lieDim := lieDim) (β := β)
        (κ := κ) (κ₀ := κ₀)
        HF z Λ F ν Hraw hν hHraw hHraw_one hhalf hκ₀_nonneg hκ
        hraw hdisj hnoedges hholes_ne hCq t k Q)
  exact
    norm_appendixFHoleHsharp_le_residual_of_dimockII_appendixF_halfBudget
      (d := d) (L := L)
      HF zCarrier zK g Hraw rootBudget
      (C := C) (H₀ := Hscale) (c₀ := c₀) (κ := κ) (κ₀ := κ₀)
      hmargin hκ₀ hHraw hroot0 hactivityKsharp
      (fun t k => by simpa [rootBudget] using hhalf t k)
      (fun t k => by simpa [rootBudget] using hprofile t k)
      hdisj hnoedges hholes_ne hCq

end YangMills.RG
