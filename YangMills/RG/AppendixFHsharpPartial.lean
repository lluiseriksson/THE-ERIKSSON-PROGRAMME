/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpResidual

/-!
# Appendix F: finite partial second Ursell activity

This module isolates the finite truncations of the second Appendix-F Ursell
activity.  The object
`appendixFHoleHsharpPartial HF zK N Y` sums only cluster sizes
`0, ..., N - 1`, so all identities here are finite and do not use convergence
of the totalized `tsum` defining `appendixFHoleHsharp`.

The residual adapters mirror the infinite `H#` adapters, but consume a
source-supplied norm estimate on the finite partial object.  They are intended
as staging lemmas for future analytic proofs of convergence and residual
decay.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- Finite partial second Ursell activity, summing only the first `N` cluster
sizes.  This is the convergence-free truncation of `appendixFHoleHsharp`. -/
noncomputable def appendixFHoleHsharpPartial
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (N : ℕ)
    (Y : Finset (Cube d L)) : ℂ :=
  ∑ n ∈ Finset.range N, appendixFHoleHsharpTerm HF zK Y n

@[simp] theorem appendixFHoleHsharpPartial_zero
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L)) :
    appendixFHoleHsharpPartial HF zK 0 Y = 0 := by
  simp [appendixFHoleHsharpPartial]

theorem appendixFHoleHsharpPartial_succ
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (N : ℕ)
    (Y : Finset (Cube d L)) :
    appendixFHoleHsharpPartial HF zK (N + 1) Y =
      appendixFHoleHsharpPartial HF zK N Y +
        appendixFHoleHsharpTerm HF zK Y N := by
  simp [appendixFHoleHsharpPartial, Finset.sum_range_succ]

/-- Summing a finite partial `H#` over all target unions is exactly the finite
sum of the corresponding ordinary KP cluster-sum terms.  No infinite
interchange is involved. -/
theorem sum_appendixFHoleHsharpPartial_eq_sum_clusterSum_terms
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (N : ℕ) :
    (∑ Y : Finset (Cube d L), appendixFHoleHsharpPartial HF zK N Y) =
      ∑ n ∈ Finset.range N,
        (((n + 1).factorial : ℂ))⁻¹ *
          ∑ X : Fin (n + 1) → OmegaPolymerType HF zK,
            (KP.ursell (omegaHolePolymerSystem HF zK) X : ℂ) *
              ∏ i, (omegaHolePolymerSystem HF zK).activity (X i) := by
  classical
  simp only [appendixFHoleHsharpPartial]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl
    (fun n _hn => sum_appendixFHoleHsharpTerm_eq_clusterSum_term HF zK n)

/-- A complex-norm residual bound for a finite partial `H#` activity implies
the real residual activity-decay predicate for any explicitly contractive real
extraction. -/
theorem clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_le
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (N : ℕ)
    (toReal : ℂ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (htoReal : ∀ w : ℂ, |toReal w| ≤ ‖w‖)
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    ClusterWithHolesActivityDecay
      (fun t k (P : OmegaPolymerType HF zCarrier) =>
        toReal (appendixFHoleHsharpPartial HF (zK t k) N P.val))
      (fun P : OmegaPolymerType HF zCarrier =>
        discreteModifiedMetric HF P.val + 1)
      g C H₀ c₀ κ κ₀ := by
  intro t k P
  exact (htoReal _).trans (hHsharp t k P)

/-- Rooted partial-`H#` residual adapter, matching the concrete omega-rooted
summability index shape. -/
theorem rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_le
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (N : ℕ)
    (toReal : ℂ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (htoReal : ∀ w : ℂ, |toReal w| ≤ ‖w‖)
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    ClusterWithHolesActivityDecay
      (fun t k (P : { P : OmegaPolymerType HF zCarrier //
          r ∈ skeleton HF P.val }) =>
        toReal (appendixFHoleHsharpPartial HF (zK t k) N P.val.val))
      (fun P : { P : OmegaPolymerType HF zCarrier //
          r ∈ skeleton HF P.val } =>
        discreteModifiedMetric HF (P.val.val : Finset (Cube d L)) + 1)
      g C H₀ c₀ κ κ₀ := by
  intro t k P
  exact (htoReal _).trans (hHsharp t k P.val)

/-- Absolute summability of a rooted real projection of the finite partial
Appendix-F `H#` activity follows from the same residual norm estimate used by
the finite-partial scalar UV consumer. -/
theorem summable_abs_of_omegaRootedAppendixFHsharpPartial
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (N : ℕ)
    (toReal : ℂ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (htoReal : ∀ w : ℂ, |toReal w| ≤ ‖w‖)
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀) (hg : ∀ k, 0 ≤ g k)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    ∀ t k,
      Summable
        (fun P : { P : OmegaPolymerType HF zCarrier //
            r ∈ skeleton HF P.val } =>
          |toReal (appendixFHoleHsharpPartial HF (zK t k) N P.val.val)|) :=
  summable_abs_of_omegaRootedClusterWithHolesActivityDecay
    HF zCarrier r
    (fun t k P =>
      toReal (appendixFHoleHsharpPartial HF (zK t k) N P.val.val))
    g hC hH₀ hg hres
    (rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_le
      HF zCarrier r zK N toReal g htoReal hHsharp)

/-- Real-part specialization of
`summable_abs_of_omegaRootedAppendixFHsharpPartial`. -/
theorem summable_abs_of_omegaRootedAppendixFHsharpPartial_re
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (N : ℕ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀) (hg : ∀ k, 0 ≤ g k)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    ∀ t k,
      Summable
        (fun P : { P : OmegaPolymerType HF zCarrier //
            r ∈ skeleton HF P.val } =>
          |Complex.re
            (appendixFHoleHsharpPartial HF (zK t k) N P.val.val)|) :=
  summable_abs_of_omegaRootedAppendixFHsharpPartial
    HF zCarrier r zK N Complex.re g complex_re_contracts_norm
    hC hH₀ hg hres hHsharp

/-- Source-facing residual producer for a finite partial `H#` scalar
remainder. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (N : ℕ)
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
            toReal (appendixFHoleHsharpPartial HF (zK t k) N P.val.val))
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
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
        toReal (appendixFHoleHsharpPartial HF (zK t k) N P.val.val))
      g hC hH₀ hg hres hR
      (rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_le
        HF zCarrier r zK N toReal g htoReal hHsharp)
      hdisj hnoedges hholes_ne hCq

/-- Finite partial `H#` residual producer with the sufficient source margin
`κ ≥ 4κ₀ + 3`. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial_four_mul_margin
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (N : ℕ)
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
            toReal (appendixFHoleHsharpPartial HF (zK t k) N P.val.val))
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
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
  singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial
    HF zCarrier r zK N Rsc toReal g htoReal hC hH₀ hg
    (kappa0_le_polymerClusterResidualRate_of_four_mul_add_le hκ)
    hR hHsharp hdisj hnoedges hholes_ne hCq

/-- Real-part specialization of the finite partial `H#` residual producer. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial_re
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (N : ℕ)
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
            Complex.re (appendixFHoleHsharpPartial HF (zK t k) N P.val.val))
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
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
  singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial
    HF zCarrier r zK N Rsc Complex.re g complex_re_contracts_norm
    hC hH₀ hg hres hR hHsharp hdisj hnoedges hholes_ne hCq

/-- Real-part specialization of the finite partial `H#` residual producer with
the sufficient source margin `κ ≥ 4κ₀ + 3`. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial_re_four_mul_margin
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (N : ℕ)
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
            Complex.re (appendixFHoleHsharpPartial HF (zK t k) N P.val.val))
    (hHsharp :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
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
  singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial_four_mul_margin
    HF zCarrier r zK N Rsc Complex.re g complex_re_contracts_norm
    hC hH₀ hg hκ hR hHsharp hdisj hnoedges hholes_ne hCq

end YangMills.RG
