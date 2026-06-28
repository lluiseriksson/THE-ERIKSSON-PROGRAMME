/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFSecondUrsellClosure
import YangMills.RG.BalabanCMP116HsharpAdapter

/-!
# Appendix F `K#` estimates with the canonical rooted summability budget

This module removes the caller-supplied rooted summability hypothesis from the
first Appendix-F `K#` estimate.  The rooted finite modified-metric summability
theorem already proves the required bound with the canonical constant
`appendixFHoleRootSumConstant d kappa0`; the estimates below feed that theorem
directly into the generic and CMP116-specialized `K#` source estimators.

Honest scope: the raw metric activity estimate, K# smallness, source constants,
and hole-geometry hypotheses remain explicit.  This closes only the rooted
finite summability field `hroot`; it does not prove the Yang--Mills activity
estimate or the second-Ursell/H# source theorem.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open MeasureTheory

variable {d L : ℕ} [NeZero L]

/-- First `K#` estimate with the rooted summability budget discharged by the
canonical Appendix-F modified-metric root-sum theorem.

Compared with
`norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted`,
the caller no longer supplies
`∀ r, ∑ X ∈ Λ.filter (fun X => r ∈ skeleton HF X.val), ... ≤ K0`; the constant
is fixed to `appendixFHoleRootSumConstant d κ₀` and proved from the hole
geometry plus the geometric ratio condition `hCq`. -/
theorem norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_canonicalRoot
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z →
      LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hsmall : 2 * H₀ * appendixFHoleRootSumConstant d κ₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(H X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hint : Integrable
      (fun φ =>
        (appendixFHoleConnectedLocalActivity
          HF z Λ H Y).globalEval ψ φ)
      (Measure.pi fun _ : Cube d L => μ))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    ‖(appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ‖ ≤
      (2 * H₀ * appendixFHoleRootSumConstant d κ₀) *
        appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y := by
  refine
    norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted
      HF z Λ H μ hY ψ hH₀ hH₀_one
      (appendixFHoleRootSumConstant_nonneg_of_hCq hCq) hsmall
      hκ₀ hκ ?_ hraw hint
  intro r
  simpa [appendixFHoleRootSumConstant] using
    appendixFHole_rootedFiniteExpWeightSum_le
      HF z Λ r κ₀ hdisj hnoedges hholes_ne hCq

/-- First `K#` estimate with the canonical rooted summability budget, where the
`K#` convexity/smallness hypothesis is derived from the Appendix-F
second-Ursell half-budget.

This is useful when the caller is on the downstream `H#` route: the same
half-budget that controls the second-Ursell denominator also implies
`2 * H₀ * appendixFHoleRootSumConstant d κ₀ <= 1`, so the first-gas estimate no
longer needs that scalar condition as a separate input. -/
theorem norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_canonicalRoot_halfBudget
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z →
      LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hhalf :
      appendixFSecondUrsellLeafConstant d κ₀ *
          (2 * H₀ * appendixFHoleRootSumConstant d κ₀) ≤ 1 / 2)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(H X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hint : Integrable
      (fun φ =>
        (appendixFHoleConnectedLocalActivity
          HF z Λ H Y).globalEval ψ φ)
      (Measure.pi fun _ : Cube d L => μ))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    ‖(appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ‖ ≤
      (2 * H₀ * appendixFHoleRootSumConstant d κ₀) *
        appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y := by
  have hK : 0 ≤ appendixFHoleRootSumConstant d κ₀ :=
    appendixFHoleRootSumConstant_nonneg_of_hCq hCq
  have hsmall : 2 * H₀ * appendixFHoleRootSumConstant d κ₀ ≤ 1 :=
    appendixFSecondUrsell_ksharpSmallness_of_halfBudget
      (d := d) (κ₀ := κ₀) (A := H₀)
      (K := appendixFHoleRootSumConstant d κ₀)
      hH₀ hK hhalf
  exact
    norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_canonicalRoot
      HF z Λ H μ hY ψ hH₀ hH₀_one hsmall hκ₀ hκ hraw hint
      hdisj hnoedges hholes_ne hCq

/-- CMP116 scale-family `K#` estimate with the rooted summability budget
discharged by the canonical Appendix-F root-sum theorem.

The remaining source-facing input is the raw metric decay of the localized
CMP116 activity family.  Measurability/integrability is still supplied by the
localized activity package, as in the existing source-shaped K# theorem. -/
theorem
    balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_canonicalRoot_of_source
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (H₀ : ℕ → ℕ → ℝ)
    {κ κ₀ : ℝ}
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hH₀ : ∀ t k, 0 ≤ H₀ t k)
    (hH₀_one : ∀ t k, H₀ t k ≤ 1)
    (hsmall :
      ∀ t k,
        2 * H₀ t k * appendixFHoleRootSumConstant d κ₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        H₀ t k * appendixFHoleExpWeight HF κ X.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    ∀ t k (Q : OmegaPolymerType HF
      (balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t k)),
      ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Q.val‖ ≤
        (2 * H₀ t k * appendixFHoleRootSumConstant d κ₀) *
          appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Q.val := by
  refine
    balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_rooted_of_source
      HF z Λ F ν H₀ (fun _ _ => appendixFHoleRootSumConstant d κ₀)
      hν hH₀ hH₀_one
      (fun _ _ => appendixFHoleRootSumConstant_nonneg_of_hCq hCq)
      hsmall hκ₀ hκ ?_ hraw
  intro t k r
  simpa [appendixFHoleRootSumConstant] using
    appendixFHole_rootedFiniteExpWeightSum_le
      HF (z t k) (Λ t k) r κ₀ hdisj hnoedges hholes_ne hCq

/-- CMP116 scale-family `K#` estimate with canonical root budget and `K#`
smallness derived from the Appendix-F half-budget.

The remaining source-facing inputs are now the raw metric decay, the
scale-by-scale half-budget, the source constants, and hole geometry. -/
theorem
    balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_canonicalRoot_halfBudget_of_source
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (H₀ : ℕ → ℕ → ℝ)
    {κ κ₀ : ℝ}
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hH₀ : ∀ t k, 0 ≤ H₀ t k)
    (hH₀_one : ∀ t k, H₀ t k ≤ 1)
    (hhalf :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ *
            (2 * H₀ t k * appendixFHoleRootSumConstant d κ₀) ≤ 1 / 2)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        H₀ t k * appendixFHoleExpWeight HF κ X.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    ∀ t k (Q : OmegaPolymerType HF
      (balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t k)),
      ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Q.val‖ ≤
        (2 * H₀ t k * appendixFHoleRootSumConstant d κ₀) *
          appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Q.val := by
  have hK : 0 ≤ appendixFHoleRootSumConstant d κ₀ :=
    appendixFHoleRootSumConstant_nonneg_of_hCq hCq
  have hsmall :
      ∀ t k,
        2 * H₀ t k * appendixFHoleRootSumConstant d κ₀ ≤ 1 := by
    intro t k
    exact
      appendixFSecondUrsell_ksharpSmallness_of_halfBudget
        (d := d) (κ₀ := κ₀) (A := H₀ t k)
        (K := appendixFHoleRootSumConstant d κ₀)
        (hH₀ t k) hK (hhalf t k)
  exact
    balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_canonicalRoot_of_source
      HF z Λ F ν H₀ hν hH₀ hH₀_one hsmall hκ₀ hκ hraw
      hdisj hnoedges hholes_ne hCq

end YangMills.RG
