/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpPartial

/-!
# Appendix F: convergence interface for `H#` truncations

This module isolates the analytic contract between the finite partial second
Ursell activities and the totalized `appendixFHoleHsharp`.

The key point is deliberately modest: if the fixed-target sequence of
`appendixFHoleHsharpTerm`s is summable, then the finite partial sums converge to
the totalized `H#`; if a residual bound is uniform over every finite partial
cutoff, the same residual bound passes to the limit.  The module does not prove
the summability or the residual estimate.  It only states and proves the
topological passage that future source estimates must feed.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- If the fixed-target `H#` term sequence is summable, the finite partial
truncations converge to the totalized `appendixFHoleHsharp`. -/
theorem appendixFHoleHsharpPartial_tendsto
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (hsum : Summable (fun n : ℕ => appendixFHoleHsharpTerm HF zK Y n)) :
    Filter.Tendsto
      (fun N : ℕ => appendixFHoleHsharpPartial HF zK N Y)
      Filter.atTop
      (nhds (appendixFHoleHsharp HF zK Y)) := by
  simpa [appendixFHoleHsharp, appendixFHoleHsharpPartial] using
    hsum.hasSum.tendsto_sum_nat

/-- Exact finite-plus-tail decomposition of totalized `H#`.  The tail is
written with the shifted index `i + N`, so later analytic estimates can bound
the remaining second-gas Ursell contribution after a finite cutoff. -/
theorem appendixFHoleHsharp_eq_partial_add_tail
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (N : ℕ)
    (hsum : Summable (fun n : ℕ => appendixFHoleHsharpTerm HF zK Y n)) :
    appendixFHoleHsharp HF zK Y =
      appendixFHoleHsharpPartial HF zK N Y +
        ∑' i : ℕ, appendixFHoleHsharpTerm HF zK Y (i + N) := by
  simpa [appendixFHoleHsharp, appendixFHoleHsharpPartial] using
    (hsum.sum_add_tsum_nat_add N).symm

/-- The truncation error tends to zero whenever the fixed-target `H#` term
sequence is summable.  This is the Cauchy/tail form of
`appendixFHoleHsharpPartial_tendsto`. -/
theorem appendixFHoleHsharp_sub_partial_tendsto_zero
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (hsum : Summable (fun n : ℕ => appendixFHoleHsharpTerm HF zK Y n)) :
    Filter.Tendsto
      (fun N : ℕ =>
        appendixFHoleHsharp HF zK Y -
          appendixFHoleHsharpPartial HF zK N Y)
      Filter.atTop
      (nhds 0) := by
  simpa using
    (appendixFHoleHsharpPartial_tendsto HF zK Y hsum).const_sub
      (appendixFHoleHsharp HF zK Y)

/-- Quantitative tail estimate for the finite `H#` truncation error.  It
reduces a future analytic residual proof to bounding the norm-sum of the
shifted tail `n ↦ appendixFHoleHsharpTerm ... (n + N)`. -/
theorem norm_appendixFHoleHsharp_sub_partial_le_tail_norm_tsum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (N : ℕ)
    (htail :
      Summable
        (fun i : ℕ => ‖appendixFHoleHsharpTerm HF zK Y (i + N)‖)) :
    ‖appendixFHoleHsharp HF zK Y -
        appendixFHoleHsharpPartial HF zK N Y‖ ≤
      ∑' i : ℕ, ‖appendixFHoleHsharpTerm HF zK Y (i + N)‖ := by
  have hsum :
      Summable (fun n : ℕ => appendixFHoleHsharpTerm HF zK Y n) :=
    Summable.comp_nat_add (k := N) htail.of_norm
  have hdecomp :=
    appendixFHoleHsharp_eq_partial_add_tail HF zK Y N hsum
  have hdiff :
      appendixFHoleHsharp HF zK Y -
          appendixFHoleHsharpPartial HF zK N Y =
        ∑' i : ℕ, appendixFHoleHsharpTerm HF zK Y (i + N) := by
    rw [hdecomp]
    abel
  rw [hdiff]
  exact norm_tsum_le_tsum_norm htail

/-- Convenient wrapper around
`norm_appendixFHoleHsharp_sub_partial_le_tail_norm_tsum` when the source work
has already packaged the shifted norm-tail sum by an explicit scalar bound. -/
theorem norm_appendixFHoleHsharp_sub_partial_le_of_tail_norm_bound
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (N : ℕ)
    {B : ℝ}
    (htail :
      Summable
        (fun i : ℕ => ‖appendixFHoleHsharpTerm HF zK Y (i + N)‖))
    (hB :
      (∑' i : ℕ, ‖appendixFHoleHsharpTerm HF zK Y (i + N)‖) ≤ B) :
    ‖appendixFHoleHsharp HF zK Y -
        appendixFHoleHsharpPartial HF zK N Y‖ ≤ B :=
  (norm_appendixFHoleHsharp_sub_partial_le_tail_norm_tsum
    HF zK Y N htail).trans hB

/-- A residual complex-norm bound that is uniform in the finite partial cutoff
passes to the totalized `H#`, assuming the fixed-target term sequence is
summable. -/
theorem norm_appendixFHoleHsharp_le_of_partial_bound
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsum :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Summable
          (fun n : ℕ => appendixFHoleHsharpTerm HF (zK t k) P.val n))
    (hpartial :
      ∀ N t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  intro t k P
  exact le_of_tendsto'
    ((appendixFHoleHsharpPartial_tendsto HF (zK t k) P.val
      (hsum t k P)).norm)
    (fun N => hpartial N t k P)

/-- Uniform finite-partial residual bounds plus fixed-target summability imply
the totalized `H#` residual activity-decay predicate. -/
theorem clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_limit_le
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (toReal : ℂ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (htoReal : ∀ w : ℂ, |toReal w| ≤ ‖w‖)
    (hsum :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Summable
          (fun n : ℕ => appendixFHoleHsharpTerm HF (zK t k) P.val n))
    (hpartial :
      ∀ N t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
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
  exact clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le
    HF zCarrier zK toReal g htoReal
    (norm_appendixFHoleHsharp_le_of_partial_bound
      HF zCarrier zK g hsum hpartial)

/-- Rooted version of
`clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_limit_le`,
matching the concrete omega-rooted summability index shape. -/
theorem rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_limit_le
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (toReal : ℂ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (htoReal : ∀ w : ℂ, |toReal w| ≤ ‖w‖)
    (hsum :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Summable
          (fun n : ℕ => appendixFHoleHsharpTerm HF (zK t k) P.val n))
    (hpartial :
      ∀ N t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
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
  exact rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le
    HF zCarrier r zK toReal g htoReal
    (norm_appendixFHoleHsharp_le_of_partial_bound
      HF zCarrier zK g hsum hpartial)

/-- Absolute summability of the rooted totalized `H#` projection follows from
fixed-target summability of the size expansion plus a uniform finite-partial
residual bound. -/
theorem summable_abs_of_omegaRootedAppendixFHsharp_of_partial_bounds
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (toReal : ℂ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (htoReal : ∀ w : ℂ, |toReal w| ≤ ‖w‖)
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀) (hg : ∀ k, 0 ≤ g k)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hsum :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Summable
          (fun n : ℕ => appendixFHoleHsharpTerm HF (zK t k) P.val n))
    (hpartial :
      ∀ N t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    ∀ t k,
      Summable
        (fun P : { P : OmegaPolymerType HF zCarrier //
            r ∈ skeleton HF P.val } =>
          |toReal (appendixFHoleHsharp HF (zK t k) P.val.val)|) :=
  summable_abs_of_omegaRootedAppendixFHsharp
    HF zCarrier r zK toReal g htoReal hC hH₀ hg hres
    (norm_appendixFHoleHsharp_le_of_partial_bound
      HF zCarrier zK g hsum hpartial)

/-- Real-part specialization of
`summable_abs_of_omegaRootedAppendixFHsharp_of_partial_bounds`. -/
theorem summable_abs_of_omegaRootedAppendixFHsharp_re_of_partial_bounds
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀) (hg : ∀ k, 0 ≤ g k)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hsum :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Summable
          (fun n : ℕ => appendixFHoleHsharpTerm HF (zK t k) P.val n))
    (hpartial :
      ∀ N t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    ∀ t k,
      Summable
        (fun P : { P : OmegaPolymerType HF zCarrier //
            r ∈ skeleton HF P.val } =>
          |Complex.re (appendixFHoleHsharp HF (zK t k) P.val.val)|) :=
  summable_abs_of_omegaRootedAppendixFHsharp_of_partial_bounds
    HF zCarrier r zK Complex.re g complex_re_contracts_norm
    hC hH₀ hg hres hsum hpartial

/-- Source-facing residual producer for totalized `H#`, consuming only
fixed-target summability and a uniform finite-partial residual estimate. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharp_of_partial_bounds
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
    (hsum :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Summable
          (fun n : ℕ => appendixFHoleHsharpTerm HF (zK t k) P.val n))
    (hpartial :
      ∀ N t k (P : OmegaPolymerType HF zCarrier),
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
  exact singleScaleUVDecay_of_omegaRootedAppendixFHsharp
    HF zCarrier r zK Rsc toReal g htoReal hC hH₀ hg hres hR
    (norm_appendixFHoleHsharp_le_of_partial_bound
      HF zCarrier zK g hsum hpartial)
    hdisj hnoedges hholes_ne hCq

/-- Same convergence interface, with the sufficient source margin
`κ ≥ 4κ₀ + 3`. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharp_of_partial_bounds_four_mul_margin
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
    (hsum :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Summable
          (fun n : ℕ => appendixFHoleHsharpTerm HF (zK t k) P.val n))
    (hpartial :
      ∀ N t k (P : OmegaPolymerType HF zCarrier),
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
  singleScaleUVDecay_of_omegaRootedAppendixFHsharp_of_partial_bounds
    HF zCarrier r zK Rsc toReal g htoReal hC hH₀ hg
    (kappa0_le_polymerClusterResidualRate_of_four_mul_add_le hκ)
    hR hsum hpartial hdisj hnoedges hholes_ne hCq

/-- Real-part specialization of the totalized `H#` convergence interface. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_of_partial_bounds
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
    (hsum :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Summable
          (fun n : ℕ => appendixFHoleHsharpTerm HF (zK t k) P.val n))
    (hpartial :
      ∀ N t k (P : OmegaPolymerType HF zCarrier),
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
  singleScaleUVDecay_of_omegaRootedAppendixFHsharp_of_partial_bounds
    HF zCarrier r zK Rsc Complex.re g complex_re_contracts_norm
    hC hH₀ hg hres hR hsum hpartial hdisj hnoedges hholes_ne hCq

/-- Real-part specialization of the convergence interface with the sufficient
source margin `κ ≥ 4κ₀ + 3`. -/
theorem singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_of_partial_bounds_four_mul_margin
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
    (hsum :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Summable
          (fun n : ℕ => appendixFHoleHsharpTerm HF (zK t k) P.val n))
    (hpartial :
      ∀ N t k (P : OmegaPolymerType HF zCarrier),
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
  singleScaleUVDecay_of_omegaRootedAppendixFHsharp_of_partial_bounds_four_mul_margin
    HF zCarrier r zK Rsc Complex.re g complex_re_contracts_norm
    hC hH₀ hg hκ hR hsum hpartial hdisj hnoedges hholes_ne hCq

end YangMills.RG
