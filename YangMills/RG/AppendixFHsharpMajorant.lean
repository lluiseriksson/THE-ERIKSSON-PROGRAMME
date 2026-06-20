/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpConvergence
import YangMills.RG.AppendixFHsharpLimit

/-!
# Appendix F: termwise majorants for `H#`

This module isolates the next analytic contract for the second-Ursell
`H#` layer.  A future source proof is expected to provide a nonnegative
summable majorant for the fixed-target cluster-size terms.  Once that
majorant is supplied, the purely functional-analytic consequences are
mechanical:

* fixed-target summability of the complex `H#` term sequence;
* finite-partial norm bounds from finite majorant sums;
* shifted-tail norm bounds from shifted majorant sums;
* the pointwise total residual estimate consumed by the omega-rooted UV
  adapter.

No Dimock estimate is proved here.  This is only the precise Lean-facing shape
of the second-Ursell majorant obligation.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- A summable real majorant for the norms of fixed-target `H#` terms implies
summability of the complex second-Ursell term sequence. -/
theorem summable_appendixFHoleHsharpTerm_of_norm_le_majorant
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (M : ℕ → ℝ)
    (hM : Summable M)
    (hterm :
      ∀ n : ℕ, ‖appendixFHoleHsharpTerm HF zK Y n‖ ≤ M n) :
    Summable (fun n : ℕ => appendixFHoleHsharpTerm HF zK Y n) := by
  exact
    (hM.of_nonneg_of_le
      (fun n => norm_nonneg
        (appendixFHoleHsharpTerm HF zK Y n))
      hterm).of_norm

/-- Finite partial `H#` norms are bounded by the finite sum of any termwise
norm majorant. -/
theorem norm_appendixFHoleHsharpPartial_le_majorant_sum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (N : ℕ)
    (M : ℕ → ℝ)
    (hterm :
      ∀ n : ℕ, ‖appendixFHoleHsharpTerm HF zK Y n‖ ≤ M n) :
    ‖appendixFHoleHsharpPartial HF zK N Y‖ ≤
      ∑ n ∈ Finset.range N, M n := by
  calc
    ‖appendixFHoleHsharpPartial HF zK N Y‖
        ≤ ∑ n ∈ Finset.range N,
            ‖appendixFHoleHsharpTerm HF zK Y n‖ := by
          simpa [appendixFHoleHsharpPartial] using
            norm_sum_le (Finset.range N)
              (fun n => appendixFHoleHsharpTerm HF zK Y n)
    _ ≤ ∑ n ∈ Finset.range N, M n :=
          Finset.sum_le_sum (fun n _hn => hterm n)

/-- The shifted norm-tail of `H#` is bounded by the shifted tail of any
summable termwise majorant. -/
theorem appendixFHoleHsharp_tail_norm_tsum_le_majorant_tail
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (N : ℕ)
    (M : ℕ → ℝ)
    (hM : Summable M)
    (hterm :
      ∀ n : ℕ, ‖appendixFHoleHsharpTerm HF zK Y n‖ ≤ M n) :
    (∑' i : ℕ,
        ‖appendixFHoleHsharpTerm HF zK Y (i + N)‖) ≤
      ∑' i : ℕ, M (i + N) := by
  have hMtail : Summable (fun i : ℕ => M (i + N)) :=
    (summable_nat_add_iff N).2 hM
  have htailNorm :
      Summable
        (fun i : ℕ =>
          ‖appendixFHoleHsharpTerm HF zK Y (i + N)‖) :=
    hMtail.of_nonneg_of_le
      (fun i => norm_nonneg
        (appendixFHoleHsharpTerm HF zK Y (i + N)))
      (fun i => hterm (i + N))
  exact htailNorm.tsum_le_tsum (fun i => hterm (i + N)) hMtail

/-- The finite truncation error is bounded by the shifted tail of any summable
termwise majorant. -/
theorem norm_appendixFHoleHsharp_sub_partial_le_majorant_tail
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (N : ℕ)
    (M : ℕ → ℝ)
    (hM : Summable M)
    (hterm :
      ∀ n : ℕ, ‖appendixFHoleHsharpTerm HF zK Y n‖ ≤ M n) :
    ‖appendixFHoleHsharp HF zK Y -
        appendixFHoleHsharpPartial HF zK N Y‖ ≤
      ∑' i : ℕ, M (i + N) := by
  have hMtail : Summable (fun i : ℕ => M (i + N)) :=
    (summable_nat_add_iff N).2 hM
  have htailNorm :
      Summable
        (fun i : ℕ =>
          ‖appendixFHoleHsharpTerm HF zK Y (i + N)‖) :=
    hMtail.of_nonneg_of_le
      (fun i => norm_nonneg
        (appendixFHoleHsharpTerm HF zK Y (i + N)))
      (fun i => hterm (i + N))
  exact
    (norm_appendixFHoleHsharp_sub_partial_le_tail_norm_tsum
      HF zK Y N htailNorm).trans
      (appendixFHoleHsharp_tail_norm_tsum_le_majorant_tail
        HF zK Y N M hM hterm)

/-- A source-supplied termwise majorant whose finite sums obey the residual
profile yields the total `H#` residual estimate.  This is the exact bridge from
a future second-Ursell majorant proof to the pointwise total residual consumer. -/
theorem norm_appendixFHoleHsharp_le_residual_of_term_majorant
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (M : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hM :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Summable (M t k P))
    (hterm :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        ‖appendixFHoleHsharpTerm HF (zK t k) P.val n‖ ≤
          M t k P n)
    (hmajorantPartial :
      ∀ N t k (P : OmegaPolymerType HF zCarrier),
        (∑ n ∈ Finset.range N, M t k P n) ≤
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
  exact norm_appendixFHoleHsharp_le_residual_of_summable_terms
    HF zCarrier zK g
    (fun t k P =>
      summable_appendixFHoleHsharpTerm_of_norm_le_majorant
        HF (zK t k) P.val (M t k P) (hM t k P)
        (fun n => hterm t k P n))
    (fun N t k P =>
      (norm_appendixFHoleHsharpPartial_le_majorant_sum
        HF (zK t k) P.val N (M t k P)
        (fun n => hterm t k P n)).trans
        (hmajorantPartial N t k P))

/-- Real-part omega-rooted UV consumer fed directly by a termwise second-Ursell
majorant and the sufficient residual margin `κ ≥ 4κ₀ + 3`. -/
theorem
    singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_term_majorant
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (M : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℕ → ℝ)
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
    (hM :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        Summable (M t k P))
    (hterm :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        ‖appendixFHoleHsharpTerm HF (zK t k) P.val n‖ ≤
          M t k P n)
    (hmajorantPartial :
      ∀ N t k (P : OmegaPolymerType HF zCarrier),
        (∑ n ∈ Finset.range N, M t k P n) ≤
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
      (norm_appendixFHoleHsharp_le_residual_of_term_majorant
        HF zCarrier zK g M hM hterm hmajorantPartial)
      hdisj hnoedges hholes_ne hCq

end YangMills.RG
