/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharp
import YangMills.RG.PolymerClusterWithHolesBridge

/-!
# Appendix F: residual `H#` adapter

This module connects the definition-level second Ursell object
`appendixFHoleHsharp` to the existing residual with-holes UV producer.

The analytic estimate is deliberately not proved here.  Instead, a source
hypothesis bounding the complex norm of `H#` at residual rate
`κ - 3κ₀ - 3` is converted into the real-valued
`ClusterWithHolesActivityDecay` shape, and then into `SingleScaleUVDecay`
through the already verified omega-rooted summability bridge.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- The real part is a contractive real extraction from a complex activity. -/
theorem complex_re_contracts_norm (w : ℂ) : |Complex.re w| ≤ ‖w‖ :=
  Complex.abs_re_le_norm w

/-- The imaginary part is a contractive real extraction from a complex
activity. -/
theorem complex_im_contracts_norm (w : ℂ) : |Complex.im w| ≤ ‖w‖ :=
  RCLike.abs_im_le_norm w

/-- A complex-norm residual bound for the union-fiber `H#` activity implies the
real residual activity-decay predicate for any explicitly contractive real
extraction. -/
theorem clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (toReal : ℂ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (htoReal : ∀ w : ℂ, |toReal w| ≤ ‖w‖)
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    ClusterWithHolesActivityDecay
      (fun t k (P : OmegaPolymerType HF zCarrier) =>
        toReal (appendixFHoleHsharp HF (zK t k) P.val))
      (fun P : OmegaPolymerType HF zCarrier =>
        discreteModifiedMetric HF P.val + 1)
      g C H₀ c₀ κ κ₀ := by
  intro t k P
  exact (htoReal _).trans (hHsharp t k P)

/-- Rooted version of
`clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le`, matching the
index type consumed by the omega-rooted summability theorem. -/
theorem rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (toReal : ℂ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (htoReal : ∀ w : ℂ, |toReal w| ≤ ‖w‖)
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    ClusterWithHolesActivityDecay
      (fun t k (P : { P : OmegaPolymerType HF zCarrier //
          r ∈ skeleton HF P.val }) =>
        toReal (appendixFHoleHsharp HF (zK t k) P.val.val))
      (fun P : { P : OmegaPolymerType HF zCarrier //
          r ∈ skeleton HF P.val } =>
        discreteModifiedMetric HF (P.val.val : Finset (Cube d L)) + 1)
      g C H₀ c₀ κ κ₀ := by
  intro t k P
  exact (htoReal _).trans (hHsharp t k P.val)

/-- Source-facing `H#` residual producer for the scalar UV consumer.  It keeps
the real extraction explicit: the caller supplies a contraction
`|toReal w| ≤ ‖w‖`, for example the real part or any later physical projection
proved to have this property. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharp
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Rsc : ℕ → ℕ → ℝ)
    (toReal : ℂ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (htoReal : ∀ w : ℂ, |toReal w| ≤ ‖w‖)
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀) (hg : ∀ k, 0 ≤ g k)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            toReal (appendixFHoleHsharp HF (zK t k) P.val.val))
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))))
    (hdisj : ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ := by
  exact
    singleScaleUVDecay_of_omegaRootedClusterWithHolesActivities
      HF zCarrier r Rsc
      (fun t k P =>
        toReal (appendixFHoleHsharp HF (zK t k) P.val.val))
      g hC hH₀ hg hres hR
      (rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le
        HF zCarrier r zK toReal g htoReal hHsharp)
      hdisj hnoedges hholes_ne hCq

/-- Same `H#` residual producer, using the explicit sufficient source margin
`κ ≥ 4κ₀ + 3`. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharp_four_mul_margin
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Rsc : ℕ → ℕ → ℝ)
    (toReal : ℂ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (htoReal : ∀ w : ℂ, |toReal w| ≤ ‖w‖)
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀) (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            toReal (appendixFHoleHsharp HF (zK t k) P.val.val))
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))))
    (hdisj : ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ :=
  singleScaleUVDecay_of_omegaRootedAppendixFHsharp
    HF zCarrier r zK Rsc toReal g htoReal hC hH₀ hg
    (kappa0_le_polymerClusterResidualRate_of_four_mul_add_le hκ)
    hR hHsharp hdisj hnoedges hholes_ne hCq

/-- Real-part specialization of the source-facing `H#` residual producer. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀) (hg : ∀ k, 0 ≤ g k)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re (appendixFHoleHsharp HF (zK t k) P.val.val))
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))))
    (hdisj : ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ :=
  singleScaleUVDecay_of_omegaRootedAppendixFHsharp
    HF zCarrier r zK Rsc Complex.re g complex_re_contracts_norm
    hC hH₀ hg hres hR hHsharp hdisj hnoedges hholes_ne hCq

/-- Real-part specialization of the `H#` residual producer using the sufficient
source margin `κ ≥ 4κ₀ + 3`. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀) (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re (appendixFHoleHsharp HF (zK t k) P.val.val))
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))))
    (hdisj : ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ :=
  singleScaleUVDecay_of_omegaRootedAppendixFHsharp_four_mul_margin
    HF zCarrier r zK Rsc Complex.re g complex_re_contracts_norm
    hC hH₀ hg hκ hR hHsharp hdisj hnoedges hholes_ne hCq

/-- Imaginary-part specialization of the source-facing `H#` residual producer.
This is sometimes useful for auditing complex remainders, even though the
physical scalar projection is expected to be the real part. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharp_im
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀) (hg : ∀ k, 0 ≤ g k)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.im (appendixFHoleHsharp HF (zK t k) P.val.val))
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))))
    (hdisj : ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ :=
  singleScaleUVDecay_of_omegaRootedAppendixFHsharp
    HF zCarrier r zK Rsc Complex.im g complex_im_contracts_norm
    hC hH₀ hg hres hR hHsharp hdisj hnoedges hholes_ne hCq

/-- Imaginary-part specialization of the `H#` residual producer using the
sufficient source margin `κ ≥ 4κ₀ + 3`. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharp_im_four_mul_margin
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀) (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.im (appendixFHoleHsharp HF (zK t k) P.val.val))
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))))
    (hdisj : ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ :=
  singleScaleUVDecay_of_omegaRootedAppendixFHsharp_four_mul_margin
    HF zCarrier r zK Rsc Complex.im g complex_im_contracts_norm
    hC hH₀ hg hκ hR hHsharp hdisj hnoedges hholes_ne hCq

end YangMills.RG
