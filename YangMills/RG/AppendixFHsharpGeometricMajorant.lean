/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpMajorant

/-!
# Appendix F: geometric majorants for `H#`

This module specializes the termwise-majorant interface to the closed-form
geometric profile expected from a second-Ursell/KP estimate.  If a future
source proof supplies

`‖appendixFHoleHsharpTerm ... n‖ ≤ A * q^n`, with `0 ≤ A`, `0 ≤ q < 1`,

then Lean now obtains the summability, finite-partial bound, shifted-tail
bound, and total residual consumer from explicit closed-form geometric sums.

No source estimate is proved here; the module only removes the remaining
series bookkeeping once such a geometric majorant has been supplied.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- A finite partial sum of a nonnegative summable real sequence is bounded by
the total `tsum`. -/
theorem sum_range_le_tsum_of_nonneg
    (f : ℕ → ℝ)
    (hf : Summable f)
    (hf_nonneg : ∀ n : ℕ, 0 ≤ f n)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, f n) ≤ ∑' n : ℕ, f n := by
  calc
    (∑ n ∈ Finset.range N, f n)
        ≤ (∑ n ∈ Finset.range N, f n) +
            ∑' i : ℕ, f (i + N) := by
          exact le_add_of_nonneg_right
            (tsum_nonneg (fun i => hf_nonneg (i + N)))
    _ = ∑' n : ℕ, f n := hf.sum_add_tsum_nat_add N

/-- The closed-form geometric majorant is summable for `0 ≤ q < 1`. -/
theorem summable_geometric_majorant
    {A q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    Summable (fun n : ℕ => A * q ^ n) := by
  have hqnorm : ‖q‖ < 1 := by
    simpa [Real.norm_of_nonneg hq0] using hq1
  exact (summable_geometric_of_norm_lt_one (K := ℝ) hqnorm).mul_left A

/-- Closed form for the total geometric majorant. -/
theorem tsum_geometric_majorant
    {A q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    (∑' n : ℕ, A * q ^ n) = A * (1 - q)⁻¹ := by
  have hqnorm : ‖q‖ < 1 := by
    simpa [Real.norm_of_nonneg hq0] using hq1
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hqnorm]

/-- Every finite geometric partial sum is bounded by the closed total
geometric sum. -/
theorem sum_range_geometric_majorant_le_closed
    {A q : ℝ}
    (hA : 0 ≤ A)
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, A * q ^ n) ≤ A * (1 - q)⁻¹ := by
  have hsum : Summable (fun n : ℕ => A * q ^ n) :=
    summable_geometric_majorant hq0 hq1
  have hnonneg : ∀ n : ℕ, 0 ≤ A * q ^ n := fun n =>
    mul_nonneg hA (pow_nonneg hq0 n)
  calc
    (∑ n ∈ Finset.range N, A * q ^ n)
        ≤ ∑' n : ℕ, A * q ^ n :=
          sum_range_le_tsum_of_nonneg
            (fun n : ℕ => A * q ^ n) hsum hnonneg N
    _ = A * (1 - q)⁻¹ := tsum_geometric_majorant hq0 hq1

/-- Closed form for the shifted tail of a geometric majorant. -/
theorem tsum_geometric_majorant_tail
    {A q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (N : ℕ) :
    (∑' i : ℕ, A * q ^ (i + N)) =
      A * q ^ N * (1 - q)⁻¹ := by
  have hqnorm : ‖q‖ < 1 := by
    simpa [Real.norm_of_nonneg hq0] using hq1
  calc
    (∑' i : ℕ, A * q ^ (i + N))
        = ∑' i : ℕ, (A * q ^ N) * q ^ i := by
          congr 1
          ext i
          rw [pow_add]
          ring
    _ = (A * q ^ N) * ∑' i : ℕ, q ^ i := by
          rw [tsum_mul_left]
    _ = A * q ^ N * (1 - q)⁻¹ := by
          rw [tsum_geometric_of_norm_lt_one hqnorm]

/-- The finite truncation error for `H#` is bounded by a closed-form geometric
tail whenever the term norms are bounded by `A * q^n`. -/
theorem norm_appendixFHoleHsharp_sub_partial_le_geometric_tail
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (N : ℕ)
    {A q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (hterm :
      ∀ n : ℕ,
        ‖appendixFHoleHsharpTerm HF zK Y n‖ ≤ A * q ^ n) :
    ‖appendixFHoleHsharp HF zK Y -
        appendixFHoleHsharpPartial HF zK N Y‖ ≤
      A * q ^ N * (1 - q)⁻¹ := by
  have hM : Summable (fun n : ℕ => A * q ^ n) :=
    summable_geometric_majorant hq0 hq1
  calc
    ‖appendixFHoleHsharp HF zK Y -
        appendixFHoleHsharpPartial HF zK N Y‖
        ≤ ∑' i : ℕ, A * q ^ (i + N) :=
          norm_appendixFHoleHsharp_sub_partial_le_majorant_tail
            HF zK Y N (fun n : ℕ => A * q ^ n) hM hterm
    _ = A * q ^ N * (1 - q)⁻¹ :=
          tsum_geometric_majorant_tail hq0 hq1 N

/-- A closed-form geometric termwise majorant whose total geometric sum obeys
the residual profile yields the total `H#` residual estimate. -/
theorem norm_appendixFHoleHsharp_le_residual_of_geometric_term_majorant
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (A q : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hA :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ A t k P)
    (hq0 :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ q t k P)
    (hq1 :
      ∀ t k (P : OmegaPolymerType HF zCarrier), q t k P < 1)
    (hterm :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        ‖appendixFHoleHsharpTerm HF (zK t k) P.val n‖ ≤
          A t k P * q t k P ^ n)
    (hgeomResidual :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        A t k P * (1 - q t k P)⁻¹ ≤
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
  exact norm_appendixFHoleHsharp_le_residual_of_term_majorant
    HF zCarrier zK g
    (fun t k P n => A t k P * q t k P ^ n)
    (fun t k P => summable_geometric_majorant (hq0 t k P) (hq1 t k P))
    hterm
    (fun N t k P =>
      (sum_range_geometric_majorant_le_closed
        (hA t k P) (hq0 t k P) (hq1 t k P) N).trans
        (hgeomResidual t k P))

/-- Real-part omega-rooted UV consumer fed directly by a closed-form geometric
second-Ursell majorant and the sufficient residual margin `κ ≥ 4κ₀ + 3`. -/
theorem
    singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_geometric_term_majorant
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (A q : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ)
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
    (hA :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ A t k P)
    (hq0 :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ q t k P)
    (hq1 :
      ∀ t k (P : OmegaPolymerType HF zCarrier), q t k P < 1)
    (hterm :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        ‖appendixFHoleHsharpTerm HF (zK t k) P.val n‖ ≤
          A t k P * q t k P ^ n)
    (hgeomResidual :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        A t k P * (1 - q t k P)⁻¹ ≤
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
      (norm_appendixFHoleHsharp_le_residual_of_geometric_term_majorant
        HF zCarrier zK g A q hA hq0 hq1 hterm hgeomResidual)
      hdisj hnoedges hholes_ne hCq

end YangMills.RG
