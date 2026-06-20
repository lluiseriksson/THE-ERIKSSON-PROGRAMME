/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpPartial

/-!
# Appendix F: pointwise limit transfer for `H#`

This module is the source-facing limit API for the finite second-Ursell
truncations.  It keeps the analytic convergence premise explicit: a future
source proof may supply either pointwise convergence of the finite cluster-size
partials to the repository's totalized `appendixFHoleHsharp`, or the stronger
fixed-target summability hypothesis from which that convergence follows.

The transfer is deliberately pointwise in the target polymer.  We do not take a
limit through the outer rooted polymer `tsum`; instead, we first pass a
finite-cutoff residual norm bound to the total `H#` activity and then reuse the
existing omega-rooted residual consumer.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- Fixed-target summability of the second-Ursell terms implies that the finite
cluster-size truncations converge to the totalized `H#` object. -/
theorem tendsto_appendixFHoleHsharpPartial_of_summable
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (hsum :
      Summable (fun n : ℕ =>
        appendixFHoleHsharpTerm HF zK Y n)) :
    Filter.Tendsto
      (fun N : ℕ => appendixFHoleHsharpPartial HF zK N Y)
      Filter.atTop
      (nhds (appendixFHoleHsharp HF zK Y)) := by
  simpa [appendixFHoleHsharpPartial, appendixFHoleHsharp] using
    hsum.hasSum.tendsto_sum_nat

/-- A residual bound uniform in the finite cluster-size cutoff passes to the
total second-Ursell activity, provided convergence to that total activity is
supplied explicitly. -/
theorem norm_appendixFHoleHsharp_le_residual_of_partial_limit
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hlim :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Filter.Tendsto
          (fun N : ℕ =>
            appendixFHoleHsharpPartial HF (zK t k) N P.val)
          Filter.atTop
          (nhds (appendixFHoleHsharp HF (zK t k) P.val)))
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
  exact le_of_tendsto' ((hlim t k P).norm)
    (fun N => hpartial N t k P)

/-- Version of the residual transfer whose convergence premise is supplied as
fixed-target summability of the second-Ursell terms. -/
theorem norm_appendixFHoleHsharp_le_residual_of_summable_terms
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsum :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Summable (fun n : ℕ =>
          appendixFHoleHsharpTerm HF (zK t k) P.val n))
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
  exact norm_appendixFHoleHsharp_le_residual_of_partial_limit
    HF zCarrier zK g
    (fun t k P =>
      tendsto_appendixFHoleHsharpPartial_of_summable
        HF (zK t k) P.val (hsum t k P))
    hpartial

/-- The total real `H#` remainder satisfies single-scale UV decay when its
finite cluster-size truncations converge pointwise and obey the residual
estimate uniformly in the cutoff.  The limit passage occurs before the rooted
polymer summation, avoiding any dominated-convergence obligation for that
outer `tsum`. -/
theorem
    singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_partial_limit
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C)
    (hH₀ : 0 ≤ H₀)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (appendixFHoleHsharp HF (zK t k) P.val.val))
    (hlim :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Filter.Tendsto
          (fun N : ℕ =>
            appendixFHoleHsharpPartial HF (zK t k) N P.val)
          Filter.atTop
          (nhds (appendixFHoleHsharp HF (zK t k) P.val)))
    (hpartial :
      ∀ N t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))))
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
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ := by
  exact
    singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin
      HF zCarrier r zK Rsc g
      hC hH₀ hg hκ hR
      (norm_appendixFHoleHsharp_le_residual_of_partial_limit
        HF zCarrier zK g hlim hpartial)
      hdisj hnoedges hholes_ne hCq

end YangMills.RG
