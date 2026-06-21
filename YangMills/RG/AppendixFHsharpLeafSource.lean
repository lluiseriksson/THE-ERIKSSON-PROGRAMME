/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpMarkedVertexSource
import YangMills.RG.AppendixFSecondUrsellLeafSummation
import YangMills.RG.AppendixFSecondUrsellClosure

/-!
# Source-facing leaf-summation contracts for Appendix-F `H#`

This module connects the finite marked-root leaf summation theorem to the
CMP116-specialized `H#` source interfaces.  The remaining source obligations are
kept explicit: a pointwise first-activity extraction, a residual-weight split
`w ≤ exp(-rate d_M) u`, and a hard-core leaf budget
`u ≤ exp(-2κ₀ d_M)`.

No Yang--Mills raw activity estimate, Balaban support/locality theorem,
`hRpoly`, continuum construction, or Clay conclusion is proved here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

open MeasureTheory

namespace YangMills.RG

variable {d L : ℕ} [NeZero L]

/-- The finite leaf constant is nonnegative. -/
theorem appendixFSecondUrsellLeafConstant_nonneg
    (d : ℕ) (κ₀ : ℝ) :
    0 ≤ appendixFSecondUrsellLeafConstant d κ₀ := by
  unfold appendixFSecondUrsellLeafConstant
  exact mul_nonneg (by norm_num)
    (sq_nonneg (appendixFSecondUrsellMomentConstant d κ₀))

/-- CMP116 geometric `H#` profile from the finite marked-root leaf summation.

Compared with
`balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_weighted_tree_geometric`,
the abstract weighted-tree hypothesis is discharged by
`appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_expWeight_leafSummation`.
The source still must provide the first-activity extraction and the two
weight-splitting inequalities. -/
noncomputable def
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_expWeight_leafSummation
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
    (w u : ∀ t k,
      OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k) → ℝ)
    (epsilon : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1)
    (hw :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)), 0 ≤ w t k Q)
    (hu :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)), 0 ≤ u t k Q)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤ epsilon t k * w t k Q)
    (hsplit :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        w t k Q ≤
          appendixFHoleExpWeight HF (polymerClusterResidualRate κ κ₀) Q.val *
            u t k Q)
    (hu_exp :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        u t k Q ≤ appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ * epsilon t k) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    BalabanCMP116AppendixFHsharpGeometricMajorantProfile
      HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀ := by
  refine
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_weighted_tree_geometric
      HF zCarrier z Λ F ν g w epsilon
      (fun _t _k => appendixFSecondUrsellMomentConstant d κ₀)
      (fun _t _k => appendixFSecondUrsellLeafConstant d κ₀)
      hε
      (fun _t _k => appendixFSecondUrsellMomentConstant_nonneg d κ₀)
      (fun _t _k => appendixFSecondUrsellLeafConstant_nonneg d κ₀)
      hρ1 hw hactivity ?_ hBclosed
  intro t k P n
  let zInt :=
    balabanCMP116AppendixFIntegratedKsharpActivityFamily
      HF z Λ F ν t k
  let Q : OmegaPolymerType HF zInt :=
    omegaPolymerReindex HF (z' := zInt) P
  have hrate : 0 ≤ polymerClusterResidualRate κ κ₀ :=
    polymerClusterResidualRate_nonneg_of_three_mul_add_le hmargin
  have hr : omegaPolymerSkeletonRoot HF Q ∈ skeleton HF P.val := by
    simpa [Q, zInt] using omegaPolymerSkeletonRoot_mem HF Q
  have hleaf :=
    appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_expWeight_leafSummation
      HF zInt (w t k) (u t k) P.val
      (omegaPolymerSkeletonRoot HF Q) n
      (polymerClusterResidualRate κ κ₀) κ₀
      hrate (hw t k) (hu t k) (hsplit t k) (hu_exp t k)
      hr hκ₀ hdisj hnoedges hholes_ne hCq
  simpa [zInt, Q, appendixFHoleExpWeight]
    using hleaf

/-- Normalize a source-facing pointwise `K#` estimate at the canonical
first-gas rate into the residual-times-leaf product expected by the finite
marked-root leaf summation. -/
theorem
    balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_residual_mul_leaf_of_ksharpRate
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β)
          (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (epsilon : ℕ → ℕ → ℝ)
    {κ κ₀ : ℝ}
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hactivityKsharp :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤
          epsilon t k *
            appendixFHoleExpWeight HF
              (appendixFKsharpRate κ κ₀) Q.val) :
    ∀ t k (Q : OmegaPolymerType HF
      (balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t k)),
      ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Q.val‖ ≤
        epsilon t k *
          (appendixFHoleExpWeight HF
              (polymerClusterResidualRate κ κ₀) Q.val *
            appendixFHoleExpWeight HF (2 * κ₀) Q.val) := by
  intro t k Q
  calc
    ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t k Q.val‖
        ≤ epsilon t k *
            appendixFHoleExpWeight HF
              (appendixFKsharpRate κ κ₀) Q.val :=
      hactivityKsharp t k Q
    _ ≤ epsilon t k *
        (appendixFHoleExpWeight HF
            (polymerClusterResidualRate κ κ₀) Q.val *
          appendixFHoleExpWeight HF (2 * κ₀) Q.val) :=
      mul_le_mul_of_nonneg_left
        (appendixFHoleExpWeight_ksharpRate_le_residual_mul_leafBudget
          HF κ κ₀ Q.val)
        (hε t k)

/-- CMP116 geometric `H#` profile from a single pointwise activity bound with
the source-normal split already multiplied out.

This constructor is a convenience wrapper around
`balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_expWeight_leafSummation`
with

`u(Q) = exp(-2κ₀ d_M(Q))` and
`w(Q) = exp(-residualRate d_M(Q)) * u(Q)`.

Thus a source theorem can state the first-activity input directly as one
pointwise estimate, without separately manufacturing the intermediate weights.
-/
noncomputable def
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_pointwise_expWeight_leafSummation
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
    (epsilon : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤
          epsilon t k *
            (appendixFHoleExpWeight HF
                (polymerClusterResidualRate κ κ₀) Q.val *
              appendixFHoleExpWeight HF (2 * κ₀) Q.val))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ * epsilon t k) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    BalabanCMP116AppendixFHsharpGeometricMajorantProfile
      HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_expWeight_leafSummation
    HF zCarrier z Λ F ν g
    (fun _t _k Q =>
      appendixFHoleExpWeight HF (polymerClusterResidualRate κ κ₀) Q.val *
        appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    (fun _t _k Q => appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    epsilon hmargin hκ₀ hε hρ1
    (fun _t _k Q =>
      mul_nonneg
        (appendixFHoleExpWeight_nonneg HF
          (polymerClusterResidualRate κ κ₀) Q.val)
        (appendixFHoleExpWeight_nonneg HF (2 * κ₀) Q.val))
    (fun _t _k Q => appendixFHoleExpWeight_nonneg HF (2 * κ₀) Q.val)
    hactivity
    (fun _t _k _Q => le_rfl)
    (fun _t _k _Q => le_rfl)
    hdisj hnoedges hholes_ne hCq hBclosed

/-- CMP116 geometric `H#` profile from a pointwise first-gas `K#` estimate at
the canonical source rate.  The normalization to the residual-times-leaf split
is supplied by
`balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_residual_mul_leaf_of_ksharpRate`.
-/
noncomputable def
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_pointwise_ksharpRate_leafSummation
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
    (epsilon : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1)
    (hactivityKsharp :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤
          epsilon t k *
            appendixFHoleExpWeight HF
              (appendixFKsharpRate κ κ₀) Q.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ * epsilon t k) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    BalabanCMP116AppendixFHsharpGeometricMajorantProfile
      HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_pointwise_expWeight_leafSummation
    HF zCarrier z Λ F ν g epsilon
    hmargin hκ₀ hε hρ1
    (balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_residual_mul_leaf_of_ksharpRate
      (κ := κ) (κ₀ := κ₀)
      HF z Λ F ν epsilon hε hactivityKsharp)
    hdisj hnoedges hholes_ne hCq hBclosed

/-- Build the fluctuation-integrability `hint` used by the source-facing
`H#` endpoints from raw one-polymer decay plus strong measurability of the
connected first-activity integrand.

This keeps the analytic source obligation honest: future CMP/Balaban input
still has to prove `hmeas` and `hraw`, but downstream `K#`/`H#` consumers no
longer need an opaque, separately stated `Integrable` hypothesis. -/
theorem
    balabanCMP116AppendixFConnectedLocalActivity_hint_of_rawMetricDecay_rooted
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (Hraw Kroot : ℕ → ℕ → ℝ)
    {κ κ₀ : ℝ}
    (hHraw : ∀ t k, 0 ≤ Hraw t k)
    (hHraw_one : ∀ t k, Hraw t k ≤ 1)
    (hKroot : ∀ t k, 0 ≤ Kroot t k)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ t k r,
      (∑ X ∈ (Λ t k).filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ Kroot t k)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        Hraw t k * appendixFHoleExpWeight HF κ X.val)
    (hmeas : ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        AEStronglyMeasurable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim)) :
    ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        Integrable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim) := by
  intro t k Y hY ψ
  exact
    integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted
      HF (z t k) (Λ t k) (F t k) hY ψ
      (hHraw t k) (hHraw_one t k) (hKroot t k)
      hκ₀ hκ (hroot t k)
      (hraw t k ψ)
      (hmeas t k Y hY ψ)

/-- Ordinary strong measurability is enough to build the source-facing
fluctuation-integrability `hint`.

This is a thin source-facing adapter for future CMP/Balaban inputs that prove
the connected first-activity integrand is `StronglyMeasurable` under the
Gaussian product measure.  The raw decay and rooted summability assumptions
are unchanged. -/
theorem
    balabanCMP116AppendixFConnectedLocalActivity_hint_of_rawMetricDecay_rooted_of_stronglyMeasurable
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (Hraw Kroot : ℕ → ℕ → ℝ)
    {κ κ₀ : ℝ}
    (hHraw : ∀ t k, 0 ≤ Hraw t k)
    (hHraw_one : ∀ t k, Hraw t k ≤ 1)
    (hKroot : ∀ t k, 0 ≤ Kroot t k)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ t k r,
      (∑ X ∈ (Λ t k).filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ Kroot t k)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        Hraw t k * appendixFHoleExpWeight HF κ X.val)
    (hmeas : ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        StronglyMeasurable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ)) :
    ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        Integrable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim) :=
  balabanCMP116AppendixFConnectedLocalActivity_hint_of_rawMetricDecay_rooted
    HF z Λ F Hraw Kroot hHraw hHraw_one hKroot hκ₀ hκ
    hroot hraw
    (fun t k Y hY ψ => (hmeas t k Y hY ψ).aestronglyMeasurable)

/-- CMP116 geometric `H#` profile from rooted raw-metric first-activity data.

This is the source-facing composition of the rooted `K#` estimate with the
canonical Ksharp-rate leaf-summation profile.  The hypotheses still name the
true source obligations: raw pointwise decay, the rooted first-cover budget,
spectator probability, fluctuation integrability, and the closed geometric
smallness condition for the second gas. -/
noncomputable def
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_rawMetricDecay_rooted_ksharpRate
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
    (Hraw Kroot : ℕ → ℕ → ℝ)
    {C Hscale c₀ κ κ₀ : ℝ}
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hHraw : ∀ t k, 0 ≤ Hraw t k)
    (hHraw_one : ∀ t k, Hraw t k ≤ 1)
    (hKroot : ∀ t k, 0 ≤ Kroot t k)
    (hsmall : ∀ t k, 2 * Hraw t k * Kroot t k ≤ 1)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ *
            (2 * Hraw t k * Kroot t k) < 1)
    (hroot : ∀ t k r,
      (∑ X ∈ (Λ t k).filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ Kroot t k)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        Hraw t k * appendixFHoleExpWeight HF κ X.val)
    (hint : ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        Integrable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ *
            (2 * Hraw t k * Kroot t k)) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              (2 * Hraw t k * Kroot t k))⁻¹ ≤
          C * Hscale * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    BalabanCMP116AppendixFHsharpGeometricMajorantProfile
      HF zCarrier z Λ F ν g C Hscale c₀ κ κ₀ := by
  have hε : ∀ t k, 0 ≤ 2 * Hraw t k * Kroot t k := by
    intro t k
    exact mul_nonneg (mul_nonneg zero_le_two (hHraw t k)) (hKroot t k)
  have hκ : κ₀ ≤ κ := by
    linarith
  exact
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_pointwise_ksharpRate_leafSummation
      HF zCarrier z Λ F ν g
      (fun t k => 2 * Hraw t k * Kroot t k)
      hmargin hκ₀ hε hρ1
      (balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_rooted
        HF z Λ F ν Hraw Kroot hν hHraw hHraw_one hKroot hsmall
        (le_of_lt hκ₀) hκ hroot hraw hint)
      hdisj hnoedges hholes_ne hCq hBclosed

/-- Source-normal `cluster3` constructor from the finite leaf summation plus
pointwise first-activity extraction and explicit weight splitting. -/
noncomputable def
    balabanCMP116AppendixFHsharpCluster3Contract_of_expWeight_leafSummation
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
    (w u : ∀ t k,
      OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k) → ℝ)
    (epsilon : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hinput : Prop) (hinput_holds : hinput)
    (hultralocal : Prop) (hultralocal_holds : hultralocal)
    (hlocal : Prop) (hlocal_holds : hlocal)
    (hinfluence : Prop) (hinfluence_holds : hinfluence)
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1)
    (hw :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)), 0 ≤ w t k Q)
    (hu :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)), 0 ≤ u t k Q)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤ epsilon t k * w t k Q)
    (hsplit :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        w t k Q ≤
          appendixFHoleExpWeight HF (polymerClusterResidualRate κ κ₀) Q.val *
            u t k Q)
    (hu_exp :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        u t k Q ≤ appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ * epsilon t k) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    AppendixFHsharpCluster3Contract HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpCluster3Contract_of_profile
    HF zCarrier z Λ F ν g
    hinput hinput_holds hultralocal hultralocal_holds
    hlocal hlocal_holds hinfluence hinfluence_holds hmargin
    (balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_expWeight_leafSummation
      HF zCarrier z Λ F ν g w u epsilon hmargin hκ₀ hε hρ1
      hw hu hactivity hsplit hu_exp
      hdisj hnoedges hholes_ne hCq hBclosed)

/-- Source-normal `cluster3` constructor from one pointwise activity estimate
whose residual and hard-core leaf weights have already been multiplied out. -/
noncomputable def
    balabanCMP116AppendixFHsharpCluster3Contract_of_pointwise_expWeight_leafSummation
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
    (epsilon : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hinput : Prop) (hinput_holds : hinput)
    (hultralocal : Prop) (hultralocal_holds : hultralocal)
    (hlocal : Prop) (hlocal_holds : hlocal)
    (hinfluence : Prop) (hinfluence_holds : hinfluence)
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤
          epsilon t k *
            (appendixFHoleExpWeight HF
                (polymerClusterResidualRate κ κ₀) Q.val *
              appendixFHoleExpWeight HF (2 * κ₀) Q.val))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ * epsilon t k) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    AppendixFHsharpCluster3Contract HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpCluster3Contract_of_expWeight_leafSummation
    HF zCarrier z Λ F ν g
    (fun _t _k Q =>
      appendixFHoleExpWeight HF (polymerClusterResidualRate κ κ₀) Q.val *
        appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    (fun _t _k Q => appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    epsilon hinput hinput_holds hultralocal hultralocal_holds
    hlocal hlocal_holds hinfluence hinfluence_holds
    hmargin hκ₀ hε hρ1
    (fun _t _k Q =>
      mul_nonneg
        (appendixFHoleExpWeight_nonneg HF
          (polymerClusterResidualRate κ κ₀) Q.val)
        (appendixFHoleExpWeight_nonneg HF (2 * κ₀) Q.val))
    (fun _t _k Q => appendixFHoleExpWeight_nonneg HF (2 * κ₀) Q.val)
    hactivity
    (fun _t _k _Q => le_rfl)
    (fun _t _k _Q => le_rfl)
    hdisj hnoedges hholes_ne hCq hBclosed

/-- Source-normal `cluster3` constructor from a pointwise first-gas `K#`
estimate at the canonical source rate. -/
noncomputable def
    balabanCMP116AppendixFHsharpCluster3Contract_of_pointwise_ksharpRate_leafSummation
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
    (epsilon : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hinput : Prop) (hinput_holds : hinput)
    (hultralocal : Prop) (hultralocal_holds : hultralocal)
    (hlocal : Prop) (hlocal_holds : hlocal)
    (hinfluence : Prop) (hinfluence_holds : hinfluence)
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1)
    (hactivityKsharp :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤
          epsilon t k *
            appendixFHoleExpWeight HF
              (appendixFKsharpRate κ κ₀) Q.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ * epsilon t k) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    AppendixFHsharpCluster3Contract HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpCluster3Contract_of_pointwise_expWeight_leafSummation
    HF zCarrier z Λ F ν g epsilon
    hinput hinput_holds
    hultralocal hultralocal_holds
    hlocal hlocal_holds
    hinfluence hinfluence_holds
    hmargin hκ₀ hε hρ1
    (balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_residual_mul_leaf_of_ksharpRate
      (κ := κ) (κ₀ := κ₀)
      HF z Λ F ν epsilon hε hactivityKsharp)
    hdisj hnoedges hholes_ne hCq hBclosed

/-- Source-normal `cluster3` contract from rooted raw-metric first-activity
data, via the canonical Ksharp-rate leaf summation. -/
noncomputable def
    balabanCMP116AppendixFHsharpCluster3Contract_of_rawMetricDecay_rooted_ksharpRate
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
    (Hraw Kroot : ℕ → ℕ → ℝ)
    {C Hscale c₀ κ κ₀ : ℝ}
    (hinput : Prop) (hinput_holds : hinput)
    (hultralocal : Prop) (hultralocal_holds : hultralocal)
    (hlocal : Prop) (hlocal_holds : hlocal)
    (hinfluence : Prop) (hinfluence_holds : hinfluence)
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hHraw : ∀ t k, 0 ≤ Hraw t k)
    (hHraw_one : ∀ t k, Hraw t k ≤ 1)
    (hKroot : ∀ t k, 0 ≤ Kroot t k)
    (hsmall : ∀ t k, 2 * Hraw t k * Kroot t k ≤ 1)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ *
            (2 * Hraw t k * Kroot t k) < 1)
    (hroot : ∀ t k r,
      (∑ X ∈ (Λ t k).filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ Kroot t k)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        Hraw t k * appendixFHoleExpWeight HF κ X.val)
    (hint : ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        Integrable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ *
            (2 * Hraw t k * Kroot t k)) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              (2 * Hraw t k * Kroot t k))⁻¹ ≤
          C * Hscale * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    AppendixFHsharpCluster3Contract HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C Hscale c₀ κ κ₀ := by
  have hε : ∀ t k, 0 ≤ 2 * Hraw t k * Kroot t k := by
    intro t k
    exact mul_nonneg (mul_nonneg zero_le_two (hHraw t k)) (hKroot t k)
  have hκ : κ₀ ≤ κ := by
    linarith
  exact
    balabanCMP116AppendixFHsharpCluster3Contract_of_pointwise_ksharpRate_leafSummation
      HF zCarrier z Λ F ν g
      (fun t k => 2 * Hraw t k * Kroot t k)
      hinput hinput_holds
      hultralocal hultralocal_holds
      hlocal hlocal_holds
      hinfluence hinfluence_holds
      hmargin hκ₀ hε hρ1
      (balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_rooted
        HF z Λ F ν Hraw Kroot hν hHraw hHraw_one hKroot hsmall
        (le_of_lt hκ₀) hκ hroot hraw hint)
      hdisj hnoedges hholes_ne hCq hBclosed

/-- Real-part omega-rooted UV decay fed by the finite leaf summation plus
pointwise first-activity extraction and explicit weight splitting.  The
four-margin supplies the residual summability margin used by the UV consumer;
the leaf summation itself only needs the weaker three-margin. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_expWeight_leafSummation
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (w u : ∀ t k,
      OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k) → ℝ)
    (epsilon : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C)
    (hH₀ : 0 ≤ H₀)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val))
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1)
    (hw :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)), 0 ≤ w t k Q)
    (hu :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)), 0 ≤ u t k Q)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤ epsilon t k * w t k Q)
    (hsplit :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        w t k Q ≤
          appendixFHoleExpWeight HF (polymerClusterResidualRate κ κ₀) Q.val *
            u t k Q)
    (hu_exp :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        u t k Q ≤ appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ * epsilon t k) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ := by
  have hmargin : 3 * κ₀ + 3 ≤ κ := by
    linarith
  exact
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_profile
      HF zCarrier r z Λ F ν Rsc g
      hC hH₀ hg hκ hR
      (balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_expWeight_leafSummation
        HF zCarrier z Λ F ν g w u epsilon hmargin hκ₀ hε hρ1
        hw hu hactivity hsplit hu_exp
        hdisj hnoedges hholes_ne hCq hBclosed)
      hdisj hnoedges hholes_ne hCq

/-- Real-part omega-rooted UV decay from one pointwise activity estimate whose
residual and hard-core leaf weights have already been multiplied out. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_pointwise_expWeight_leafSummation
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (epsilon : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C)
    (hH₀ : 0 ≤ H₀)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val))
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤
          epsilon t k *
            (appendixFHoleExpWeight HF
                (polymerClusterResidualRate κ κ₀) Q.val *
              appendixFHoleExpWeight HF (2 * κ₀) Q.val))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ * epsilon t k) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ :=
  singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_expWeight_leafSummation
    HF zCarrier r z Λ F ν Rsc g
    (fun _t _k Q =>
      appendixFHoleExpWeight HF (polymerClusterResidualRate κ κ₀) Q.val *
        appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    (fun _t _k Q => appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    epsilon hC hH₀ hg hκ hκ₀ hR hε hρ1
    (fun _t _k Q =>
      mul_nonneg
        (appendixFHoleExpWeight_nonneg HF
          (polymerClusterResidualRate κ κ₀) Q.val)
        (appendixFHoleExpWeight_nonneg HF (2 * κ₀) Q.val))
    (fun _t _k Q => appendixFHoleExpWeight_nonneg HF (2 * κ₀) Q.val)
    hactivity
    (fun _t _k _Q => le_rfl)
    (fun _t _k _Q => le_rfl)
    hdisj hnoedges hholes_ne hCq hBclosed

/-- Real-part omega-rooted UV decay from a pointwise first-gas `K#` estimate at
the canonical source rate. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_pointwise_ksharpRate_leafSummation
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (epsilon : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C)
    (hH₀ : 0 ≤ H₀)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val))
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1)
    (hactivityKsharp :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤
          epsilon t k *
            appendixFHoleExpWeight HF
              (appendixFKsharpRate κ κ₀) Q.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ * epsilon t k) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ :=
  singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_pointwise_expWeight_leafSummation
    HF zCarrier r z Λ F ν Rsc g epsilon
    hC hH₀ hg hκ hκ₀ hR hε hρ1
    (balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_residual_mul_leaf_of_ksharpRate
      (κ := κ) (κ₀ := κ₀)
      HF z Λ F ν epsilon hε hactivityKsharp)
    hdisj hnoedges hholes_ne hCq hBclosed

/-- Real-part omega-rooted UV decay from rooted raw-metric first-activity data,
using the canonical Ksharp-rate first gas and the leaf-summation `H#`
consumer.  The four-margin is retained because the final rooted UV summability
uses the residual comparison with `κ₀`. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_ksharpRate
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (Hraw Kroot : ℕ → ℕ → ℝ)
    {C Hscale c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C)
    (hHscale : 0 ≤ Hscale)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val))
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hHraw : ∀ t k, 0 ≤ Hraw t k)
    (hHraw_one : ∀ t k, Hraw t k ≤ 1)
    (hKroot : ∀ t k, 0 ≤ Kroot t k)
    (hsmall : ∀ t k, 2 * Hraw t k * Kroot t k ≤ 1)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ *
            (2 * Hraw t k * Kroot t k) < 1)
    (hroot : ∀ t k r,
      (∑ X ∈ (Λ t k).filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ Kroot t k)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        Hraw t k * appendixFHoleExpWeight HF κ X.val)
    (hint : ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        Integrable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ *
            (2 * Hraw t k * Kroot t k)) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              (2 * Hraw t k * Kroot t k))⁻¹ ≤
          C * Hscale * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    SingleScaleUVDecay Rsc g
      ((C * Hscale) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ := by
  have hε : ∀ t k, 0 ≤ 2 * Hraw t k * Kroot t k := by
    intro t k
    exact mul_nonneg (mul_nonneg zero_le_two (hHraw t k)) (hKroot t k)
  have hκle : κ₀ ≤ κ := by
    linarith
  exact
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_pointwise_ksharpRate_leafSummation
      HF zCarrier r z Λ F ν Rsc g
      (fun t k => 2 * Hraw t k * Kroot t k)
      hC hHscale hg hκ hκ₀ hR hε hρ1
      (balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_rooted
        HF z Λ F ν Hraw Kroot hν hHraw hHraw_one hKroot hsmall
        (le_of_lt hκ₀) hκle hroot hraw hint)
      hdisj hnoedges hholes_ne hCq hBclosed

/-- Omega-rooted real-part UV decay obtained directly from the rooted
raw-metric CMP116 first-activity estimate.

The first-gas activity parameter is specialized to
`epsilon t k = 2 * A₀ t k * K₀ t k`.  All model-specific analytic inputs
remain explicit. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_leafSummation
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (A₀ K₀ : ℕ → ℕ → ℝ)
    {C Hbar c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C)
    (hHbar : 0 ≤ Hbar)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val))
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hA₀ : ∀ t k, 0 ≤ A₀ t k)
    (hA₀_one : ∀ t k, A₀ t k ≤ 1)
    (hK₀ : ∀ t k, 0 ≤ K₀ t k)
    (hsmall : ∀ t k, 2 * A₀ t k * K₀ t k ≤ 1)
    (hρ1 :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ *
            (2 * A₀ t k * K₀ t k) < 1)
    (hroot : ∀ t k r',
      (∑ X ∈ (Λ t k).filter
          (fun X => r' ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀ t k)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        A₀ t k * appendixFHoleExpWeight HF κ X.val)
    (hint : ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        Integrable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H ∈ HF.holes, H.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hBclosed :
      ∀ t k,
        (appendixFSecondUrsellMomentConstant d κ₀ *
            (2 * A₀ t k * K₀ t k)) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              (2 * A₀ t k * K₀ t k))⁻¹ ≤
          C * Hbar * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    SingleScaleUVDecay Rsc g
      ((C * Hbar) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ :=
  singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_ksharpRate
    (C := C) (Hscale := Hbar) (c₀ := c₀) (κ := κ) (κ₀ := κ₀)
    HF zCarrier r z Λ F ν Rsc g A₀ K₀
    hC hHbar hg hκ hκ₀ hR hν
    hA₀ hA₀_one hK₀ hsmall hρ1 hroot hraw hint
    hdisj hnoedges hholes_ne hCq hBclosed

/-- Omega-rooted real-part UV decay from rooted raw-metric first-activity data,
with the rooted finite summability constant specialized to the canonical
Appendix-F geometric constant.

Compared with
`singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_leafSummation`,
this corollary generates `hroot`, `hsmall`, `hρ1`, and `hBclosed` internally
from the rooted finite summability theorem and the half-budget closure lemma.
The source-facing analytic inputs `hraw`, `hint`, and the physical
identification `hR` remain explicit. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (A₀ : ℕ → ℕ → ℝ)
    {C Hbar c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C)
    (hHbar : 0 ≤ Hbar)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val))
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hA₀ : ∀ t k, 0 ≤ A₀ t k)
    (hA₀_one : ∀ t k, A₀ t k ≤ 1)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        A₀ t k * appendixFHoleExpWeight HF κ X.val)
    (hint : ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        Integrable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H ∈ HF.holes, H.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hhalf :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ *
            (2 * A₀ t k * appendixFHoleRootSumConstant d κ₀) ≤ 1 / 2)
    (hprofile :
      ∀ t k,
        4 * appendixFSecondUrsellMomentConstant d κ₀ *
            A₀ t k * appendixFHoleRootSumConstant d κ₀ ≤
          C * Hbar * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    SingleScaleUVDecay Rsc g
      ((C * Hbar) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ := by
  let Kroot : ℕ → ℕ → ℝ :=
    fun _ _ => appendixFHoleRootSumConstant d κ₀
  have hKroot : ∀ t k, 0 ≤ Kroot t k := by
    intro t k
    exact appendixFHoleRootSumConstant_nonneg_of_hCq hCq
  have hroot : ∀ t k r',
      (∑ X ∈ (Λ t k).filter
          (fun X => r' ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ Kroot t k := by
    intro t k r'
    simpa [Kroot, appendixFHoleRootSumConstant] using
      appendixFHole_rootedFiniteExpWeightSum_le
        HF (z t k) (Λ t k) r' κ₀
        hdisj hnoedges hholes_ne hCq
  have hoblig :
      ∀ t k,
        2 * A₀ t k * Kroot t k ≤ 1 ∧
        appendixFSecondUrsellLeafConstant d κ₀ *
            (2 * A₀ t k * Kroot t k) < 1 ∧
        (appendixFSecondUrsellMomentConstant d κ₀ *
            (2 * A₀ t k * Kroot t k)) *
            (1 - appendixFSecondUrsellLeafConstant d κ₀ *
              (2 * A₀ t k * Kroot t k))⁻¹ ≤
          C * Hbar * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ := by
    intro t k
    exact
      appendixFSecondUrsell_sourceObligations_of_halfBudget
        (d := d) (κ₀ := κ₀) (A := A₀ t k) (K := Kroot t k)
        (S := C * Hbar * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀)
        (hA₀ t k) (hKroot t k)
        (by simpa [Kroot] using hhalf t k)
        (by simpa [Kroot] using hprofile t k)
  exact
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_leafSummation
      (C := C) (Hbar := Hbar) (c₀ := c₀) (κ := κ) (κ₀ := κ₀)
      HF zCarrier r z Λ F ν Rsc g A₀ Kroot
      hC hHbar hg hκ hκ₀ hR hν hA₀ hA₀_one hKroot
      (fun t k => (hoblig t k).1)
      (fun t k => (hoblig t k).2.1)
      hroot hraw hint hdisj hnoedges hholes_ne hCq
      (fun t k => (hoblig t k).2.2)

/-- Omega-rooted real-part UV decay from rooted raw-metric first-activity data
and a.e. strong measurability of the connected first-activity integrand.

This is the source-facing consumer of
`balabanCMP116AppendixFConnectedLocalActivity_hint_of_rawMetricDecay_rooted`:
it derives the former opaque `hint` internally, while keeping the analytic
inputs `hraw`, `hmeas`, and the physical identification `hR` explicit. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_aestronglyMeasurable
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (A₀ : ℕ → ℕ → ℝ)
    {C Hbar c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C)
    (hHbar : 0 ≤ Hbar)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val))
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hA₀ : ∀ t k, 0 ≤ A₀ t k)
    (hA₀_one : ∀ t k, A₀ t k ≤ 1)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        A₀ t k * appendixFHoleExpWeight HF κ X.val)
    (hmeas : ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        AEStronglyMeasurable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H ∈ HF.holes, H.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hhalf :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ *
            (2 * A₀ t k * appendixFHoleRootSumConstant d κ₀) ≤ 1 / 2)
    (hprofile :
      ∀ t k,
        4 * appendixFSecondUrsellMomentConstant d κ₀ *
            A₀ t k * appendixFHoleRootSumConstant d κ₀ ≤
          C * Hbar * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    SingleScaleUVDecay Rsc g
      ((C * Hbar) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ := by
  let Kroot : ℕ → ℕ → ℝ :=
    fun _ _ => appendixFHoleRootSumConstant d κ₀
  have hKroot : ∀ t k, 0 ≤ Kroot t k := by
    intro t k
    exact appendixFHoleRootSumConstant_nonneg_of_hCq hCq
  have hroot : ∀ t k r',
      (∑ X ∈ (Λ t k).filter
          (fun X => r' ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ Kroot t k := by
    intro t k r'
    simpa [Kroot, appendixFHoleRootSumConstant] using
      appendixFHole_rootedFiniteExpWeightSum_le
        HF (z t k) (Λ t k) r' κ₀
        hdisj hnoedges hholes_ne hCq
  have hκ₀_nonneg : 0 ≤ κ₀ := le_of_lt hκ₀
  have hκle : κ₀ ≤ κ := by
    linarith
  have hint : ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        Integrable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim) :=
    balabanCMP116AppendixFConnectedLocalActivity_hint_of_rawMetricDecay_rooted
      (κ := κ) (κ₀ := κ₀)
      HF z Λ F A₀ Kroot hA₀ hA₀_one hKroot hκ₀_nonneg
      hκle hroot hraw hmeas
  exact
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget
      (C := C) (Hbar := Hbar) (c₀ := c₀) (κ := κ) (κ₀ := κ₀)
      HF zCarrier r z Λ F ν Rsc g A₀
      hC hHbar hg hκ hκ₀ hR hν hA₀ hA₀_one hraw hint
      hdisj hnoedges hholes_ne hCq hhalf hprofile

/-- Omega-rooted real-part UV decay from rooted raw-metric first-activity data
and ordinary strong measurability of the connected first-activity integrand.

This is the same canonical-root half-budget endpoint as
`..._of_aestronglyMeasurable`, with the source measurability obligation stated
in the ordinary `StronglyMeasurable` form. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_stronglyMeasurable
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (A₀ : ℕ → ℕ → ℝ)
    {C Hbar c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C)
    (hHbar : 0 ≤ Hbar)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hκ₀ : 0 < κ₀)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val))
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hA₀ : ∀ t k, 0 ≤ A₀ t k)
    (hA₀_one : ∀ t k, A₀ t k ≤ 1)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        A₀ t k * appendixFHoleExpWeight HF κ X.val)
    (hmeas : ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        StronglyMeasurable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H ∈ HF.holes, H.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1)
    (hhalf :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d κ₀ *
            (2 * A₀ t k * appendixFHoleRootSumConstant d κ₀) ≤ 1 / 2)
    (hprofile :
      ∀ t k,
        4 * appendixFSecondUrsellMomentConstant d κ₀ *
            A₀ t k * appendixFHoleRootSumConstant d κ₀ ≤
          C * Hbar * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    SingleScaleUVDecay Rsc g
      ((C * Hbar) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ :=
  singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_aestronglyMeasurable
    (C := C) (Hbar := Hbar) (c₀ := c₀) (κ := κ) (κ₀ := κ₀)
    HF zCarrier r z Λ F ν Rsc g A₀
    hC hHbar hg hκ hκ₀ hR hν hA₀ hA₀_one hraw
    (fun t k Y hY ψ => (hmeas t k Y hY ψ).aestronglyMeasurable)
    hdisj hnoedges hholes_ne hCq hhalf hprofile

end YangMills.RG
