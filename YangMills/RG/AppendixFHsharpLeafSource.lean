/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpMarkedVertexSource
import YangMills.RG.AppendixFSecondUrsellLeafSummation

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

end YangMills.RG
