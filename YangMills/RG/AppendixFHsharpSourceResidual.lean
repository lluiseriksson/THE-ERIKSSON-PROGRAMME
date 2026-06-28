/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpCertifiedTail
import YangMills.RG.AppendixFHsharpLeafSource

/-!
# Appendix F source-fed residual estimate for `H#`

This module composes the Dimock-II source-rate extraction with the certified-tail
residual theorem.  It removes the intermediate caller obligations
`w`, `Croot`, `Cleaf`, `hactivity`, and `hleaf_dimockF` from the residual
consumer, replacing them by the source-facing first-activity estimate at the
`k#` rate plus the explicit smallness and scalar budget hypotheses.

It also exposes a half-budget variant that derives those two scalar obligations
from the already-formal second-Ursell denominator closure.

Honest scope: this still assumes the analytic first-activity estimate
`hactivityKsharp`, the small denominator condition, and the final scalar budget.
It proves only the formal extraction from those source obligations to the
all-tail residual `H#` bound.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

variable {d L : ℕ} [NeZero L]

/-- Source-fed residual `H#` estimate from the Dimock-II Appendix-F rate split.

The caller supplies only the source-facing `k#` activity estimate, the scalar
smallness/budget hypotheses, and the hole-geometry inputs.  The theorem derives
the exact weighted-tree package expected by
`norm_appendixFHoleHsharp_le_residual_of_appendixF_weightedTree_certifiedTail`
using `dimockII_appendixF_weightedTree_sourceEstimate`, then applies the
certified-tail residual closure. -/
theorem norm_appendixFHoleHsharp_le_residual_of_dimockII_appendixF_sourceEstimate
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (epsilon : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hε0 : ∀ t k, 0 ≤ epsilon t k)
    (hactivityKsharp :
      ∀ t k (Q : OmegaPolymerType HF (zK t k)),
        ‖zK t k Q.val‖ ≤
          epsilon t k *
            appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Q.val)
    (hsmall :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1)
    (hbudget :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ * epsilon t k) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀)
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
      ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  let w : ∀ t k, OmegaPolymerType HF (zK t k) → ℝ :=
    fun _t _k Q =>
      appendixFHoleExpWeight HF
          (polymerClusterResidualRate κ κ₀) Q.val *
        appendixFHoleExpWeight HF (2 * κ₀) Q.val
  let Croot : ℕ → ℕ → ℝ :=
    fun _t _k => appendixFSecondUrsellMomentConstant d κ₀
  let Cleaf : ℕ → ℕ → ℝ :=
    fun _t _k => appendixFSecondUrsellLeafConstant d κ₀
  have hsrc :=
    dimockII_appendixF_weightedTree_sourceEstimate
      (d := d) (L := L) HF zCarrier zK g epsilon hmargin hκ₀ hε0
      hactivityKsharp hsmall hbudget hdisj hnoedges hholes_ne hCq
  exact
    norm_appendixFHoleHsharp_le_residual_of_appendixF_weightedTree_certifiedTail
      (d := d) (L := L) HF zCarrier zK g w epsilon Croot Cleaf
      hε0
      (fun _t _k => appendixFSecondUrsellMomentConstant_nonneg d κ₀)
      (fun _t _k => appendixFSecondUrsellLeafConstant_nonneg d κ₀)
      hsrc.1 hsrc.2.1 hsrc.2.2.1 hsrc.2.2.2.1 hsrc.2.2.2.2

/-- Source-fed residual `H#` estimate with the scalar smallness/budget closed by
the Appendix-F half-budget algebra.

Compared with
`norm_appendixFHoleHsharp_le_residual_of_dimockII_appendixF_sourceEstimate`,
the caller no longer supplies the strict denominator condition or the closed
scalar budget.  They are derived from the half-budget
`L * (2*A*K) <= 1/2` and the final profile comparison
`4*M*A*K <= C*H₀*exp(-c₀*t)*g k^κ₀`, using
`appendixFSecondUrsell_sourceObligations_of_halfBudget`. -/
theorem norm_appendixFHoleHsharp_le_residual_of_dimockII_appendixF_halfBudget
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (amplitude rootBudget : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hamplitude0 : ∀ t k, 0 ≤ amplitude t k)
    (hroot0 : ∀ t k, 0 ≤ rootBudget t k)
    (hactivityKsharp :
      ∀ t k (Q : OmegaPolymerType HF (zK t k)),
        ‖zK t k Q.val‖ ≤
          (2 * amplitude t k * rootBudget t k) *
            appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Q.val)
    (hhalf :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ *
            (2 * amplitude t k * rootBudget t k) ≤ 1 / 2)
    (hprofile :
      ∀ t k,
        4 * appendixFSecondUrsellMomentConstant d κ₀ *
            amplitude t k * rootBudget t k ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀)
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
      ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  let epsilon : ℕ → ℕ → ℝ :=
    fun t k => 2 * amplitude t k * rootBudget t k
  have hε0 : ∀ t k, 0 ≤ epsilon t k := by
    intro t k
    exact mul_nonneg (mul_nonneg zero_le_two (hamplitude0 t k)) (hroot0 t k)
  have hobligations :
      ∀ t k,
        epsilon t k ≤ 1 ∧
        appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1 ∧
        (appendixFSecondUrsellMomentConstant d κ₀ * epsilon t k) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ := by
    intro t k
    simpa [epsilon] using
      (appendixFSecondUrsell_sourceObligations_of_halfBudget
        (d := d) (κ₀ := κ₀)
        (A := amplitude t k) (K := rootBudget t k)
        (S := C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀)
        (hamplitude0 t k) (hroot0 t k) (hhalf t k) (hprofile t k))
  exact
    norm_appendixFHoleHsharp_le_residual_of_dimockII_appendixF_sourceEstimate
      (d := d) (L := L) HF zCarrier zK g epsilon hmargin hκ₀ hε0
      hactivityKsharp
      (fun t k => (hobligations t k).2.1)
      (fun t k => (hobligations t k).2.2)
      hdisj hnoedges hholes_ne hCq

end YangMills.RG
