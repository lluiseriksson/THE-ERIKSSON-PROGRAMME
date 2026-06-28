/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpGeometricMajorant

/-!
# Appendix F: certified finite-prefix / geometric-tail majorants for `H#`

This module is a small `hRpoly`-frontier step inspired by finite certificate +
tail-budget workflows: instead of asking a caller to provide a summable
second-Ursell majorant `M` and a closed `tsum` residual bound, it accepts the
more checkable certificate

* a finite prefix budget `∑ n < N, M n ≤ P`, and
* a geometric tail budget `M (i + N) ≤ A q^i`, with `0 ≤ q < 1`.

Lean then constructs both the `Summable M` proof and the closed total bound

`∑' n, M n ≤ P + A * (1 - q)⁻¹`,

and feeds the existing `H# → SingleScaleUVDecay` consumer.

Honest scope: this proves no Yang--Mills source estimate and no Dimock
Appendix-F inequality.  It only removes the external summability/`tsum`
bookkeeping once a finite-prefix/geometric-tail certificate has been supplied.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- A finite-prefix/geometric-tail certificate produces summability and a closed
`tsum` bound.

This is the scalar bookkeeping lemma behind the certified-tail `H#` endpoints:
if the prefix up to `N` is bounded by `B`, and the shifted tail is bounded by
`A q^i` with `0 ≤ q < 1`, then the whole sequence is summable and its total
mass is bounded by `B + A/(1-q)`. -/
theorem prefix_geometric_tail_summable_and_tsum_le
    (M : ℕ → ℝ) (N : ℕ) {B A q : ℝ}
    (hM_nonneg : ∀ n : ℕ, 0 ≤ M n)
    (hprefix : (∑ n ∈ Finset.range N, M n) ≤ B)
    (_hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (htail : ∀ i : ℕ, M (i + N) ≤ A * q ^ i) :
    Summable M ∧ ∑' n : ℕ, M n ≤ B + A * (1 - q)⁻¹ := by
  have hgeom : Summable (fun i : ℕ => A * q ^ i) :=
    summable_geometric_majorant (A := A) hq0 hq1
  have htailSumm : Summable (fun i : ℕ => M (i + N)) :=
    hgeom.of_nonneg_of_le
      (fun i => hM_nonneg (i + N))
      (fun i => htail i)
  have hM : Summable M := (summable_nat_add_iff N).1 htailSumm
  have htailLe : (∑' i : ℕ, M (i + N)) ≤ A * (1 - q)⁻¹ := by
    calc
      (∑' i : ℕ, M (i + N)) ≤ ∑' i : ℕ, A * q ^ i :=
        htailSumm.tsum_le_tsum (fun i => htail i) hgeom
      _ = A * (1 - q)⁻¹ := tsum_geometric_majorant (A := A) hq0 hq1
  refine ⟨hM, ?_⟩
  calc
    (∑' n : ℕ, M n)
        = (∑ n ∈ Finset.range N, M n) + ∑' i : ℕ, M (i + N) := by
          exact (hM.sum_add_tsum_nat_add N).symm
    _ ≤ B + A * (1 - q)⁻¹ := add_le_add hprefix htailLe

/-- A finite-prefix/geometric-tail certificate for a target-sensitive second-
Ursell majorant yields the total pointwise `H#` residual estimate.

Compared with `norm_appendixFHoleHsharp_le_residual_of_sizeMajorant`, callers no
longer supply `Summable (M t k P)` or a separate `tsum` residual bound.  They
supply finite prefix budgets and geometric tails, which Lean closes into those
two obligations. -/
theorem norm_appendixFHoleHsharp_le_residual_of_prefixTailMajorant
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (M : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℕ → ℝ)
    (N : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℕ)
    (prefixBudget tailAmp tailRatio :
      ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hM_nonneg :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n, 0 ≤ M t k P n)
    (hprefix :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        (∑ n ∈ Finset.range (N t k P), M t k P n) ≤ prefixBudget t k P)
    (htailAmp_nonneg :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ tailAmp t k P)
    (htailRatio_nonneg :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ tailRatio t k P)
    (htailRatio_lt_one :
      ∀ t k (P : OmegaPolymerType HF zCarrier), tailRatio t k P < 1)
    (htail :
      ∀ t k (P : OmegaPolymerType HF zCarrier) i,
        M t k P (i + N t k P) ≤ tailAmp t k P * tailRatio t k P ^ i)
    (hterm :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        ‖appendixFHoleHsharpTerm HF (zK t k) P.val n‖ ≤
          M t k P n)
    (hbudget :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        prefixBudget t k P + tailAmp t k P * (1 - tailRatio t k P)⁻¹ ≤
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
  exact norm_appendixFHoleHsharp_le_residual_of_sizeMajorant
    HF zCarrier zK g M
    (fun t k P =>
      (prefix_geometric_tail_summable_and_tsum_le
        (M t k P) (N t k P)
        (hM_nonneg t k P)
        (hprefix t k P)
        (htailAmp_nonneg t k P)
        (htailRatio_nonneg t k P)
        (htailRatio_lt_one t k P)
        (fun i => htail t k P i)).1)
    hterm
    (fun t k P =>
      ((prefix_geometric_tail_summable_and_tsum_le
        (M t k P) (N t k P)
        (hM_nonneg t k P)
        (hprefix t k P)
        (htailAmp_nonneg t k P)
        (htailRatio_nonneg t k P)
        (htailRatio_lt_one t k P)
        (fun i => htail t k P i)).2).trans
        (hbudget t k P))

/-- Real-part omega-rooted UV consumer fed directly by a certified finite-prefix
/ geometric-tail second-Ursell majorant and the sufficient residual margin
`κ ≥ 4κ₀ + 3`.

This is the `hRpoly`-shaped endpoint: it removes the external
`Summable`/`tsum` majorant obligations from the `H#` route and returns the
scalar `SingleScaleUVDecay` consumed by the UV assembly. -/
theorem
    singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_prefixTailMajorant
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (M : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℕ → ℝ)
    (N : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℕ)
    (prefixBudget tailAmp tailRatio :
      ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ)
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
    (hM_nonneg :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n, 0 ≤ M t k P n)
    (hprefix :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        (∑ n ∈ Finset.range (N t k P), M t k P n) ≤ prefixBudget t k P)
    (htailAmp_nonneg :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ tailAmp t k P)
    (htailRatio_nonneg :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ tailRatio t k P)
    (htailRatio_lt_one :
      ∀ t k (P : OmegaPolymerType HF zCarrier), tailRatio t k P < 1)
    (htail :
      ∀ t k (P : OmegaPolymerType HF zCarrier) i,
        M t k P (i + N t k P) ≤ tailAmp t k P * tailRatio t k P ^ i)
    (hterm :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        ‖appendixFHoleHsharpTerm HF (zK t k) P.val n‖ ≤
          M t k P n)
    (hbudget :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        prefixBudget t k P + tailAmp t k P * (1 - tailRatio t k P)⁻¹ ≤
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
      (norm_appendixFHoleHsharp_le_residual_of_prefixTailMajorant
        HF zCarrier zK g M N prefixBudget tailAmp tailRatio
        hM_nonneg hprefix htailAmp_nonneg htailRatio_nonneg
        htailRatio_lt_one htail hterm hbudget)
      hdisj hnoedges hholes_ne hCq

end YangMills.RG
