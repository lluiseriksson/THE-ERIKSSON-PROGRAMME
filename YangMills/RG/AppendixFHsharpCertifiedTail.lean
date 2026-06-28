/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpGeometricMajorant
import YangMills.RG.AppendixFSecondUrsellWeightedTree

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

It also packages that certificate as `AppendixFHsharpCertifiedTailProfile`, so
future source extraction can construct one auditable record and then project
the majorant summability, closed `tsum` bound, residual estimate, and UV
consumer.

Finally, it instantiates the certified-tail endpoint in the source-normal
weighted-tree all-tail case `N = 0`: one root factor `Croot*epsilon`, leaf
ratio `Cleaf*epsilon`, and target-sensitive modified-metric decay.

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

/-- A source-facing package for a certified finite-prefix/geometric-tail
majorant of the Appendix-F second-Ursell `H#` terms.

The fields are exactly the data consumed by
`norm_appendixFHoleHsharp_le_residual_of_prefixTailMajorant`: a nonnegative
majorant, an audited finite prefix, a geometric shifted tail with ratio below
one, a termwise domination of `appendixFHoleHsharpTerm`, and the closed
residual comparison.  Constructing this record is the remaining
source/certificate task; the projections below discharge the infinite-series
bookkeeping and feed the UV consumer. -/
structure AppendixFHsharpCertifiedTailProfile
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (C H₀ c₀ κ κ₀ : ℝ) where
  M : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℕ → ℝ
  N : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℕ
  prefixBudget : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ
  tailAmp : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ
  tailRatio : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ
  M_nonneg :
    ∀ t k (P : OmegaPolymerType HF zCarrier) n, 0 ≤ M t k P n
  prefix_bound :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      (∑ n ∈ Finset.range (N t k P), M t k P n) ≤
        prefixBudget t k P
  tailAmp_nonneg :
    ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ tailAmp t k P
  tailRatio_nonneg :
    ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ tailRatio t k P
  tailRatio_lt_one :
    ∀ t k (P : OmegaPolymerType HF zCarrier), tailRatio t k P < 1
  tail_bound :
    ∀ t k (P : OmegaPolymerType HF zCarrier) i,
      M t k P (i + N t k P) ≤
        tailAmp t k P * tailRatio t k P ^ i
  term_bound :
    ∀ t k (P : OmegaPolymerType HF zCarrier) n,
      ‖appendixFHoleHsharpTerm HF (zK t k) P.val n‖ ≤
        M t k P n
  closed_total_le_residual :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      prefixBudget t k P +
          tailAmp t k P * (1 - tailRatio t k P)⁻¹ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))

namespace AppendixFHsharpCertifiedTailProfile

variable
    {HF : HoleFamily d L}
    {zCarrier : Finset (Cube d L) → ℂ}
    {zK : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {g : ℕ → ℝ}
    {C H₀ c₀ κ κ₀ : ℝ}

/-- A certified-tail profile supplies summability of its scalar majorant for
each fixed scale and target. -/
theorem summable_majorant
    (profile :
      AppendixFHsharpCertifiedTailProfile HF zCarrier zK g
        C H₀ c₀ κ κ₀)
    (t k : ℕ)
    (P : OmegaPolymerType HF zCarrier) :
    Summable (profile.M t k P) :=
  (prefix_geometric_tail_summable_and_tsum_le
    (profile.M t k P) (profile.N t k P)
    (profile.M_nonneg t k P)
    (profile.prefix_bound t k P)
    (profile.tailAmp_nonneg t k P)
    (profile.tailRatio_nonneg t k P)
    (profile.tailRatio_lt_one t k P)
    (profile.tail_bound t k P)).1

/-- A certified-tail profile supplies the closed scalar `tsum` bound for its
majorant. -/
theorem tsum_majorant_bound
    (profile :
      AppendixFHsharpCertifiedTailProfile HF zCarrier zK g
        C H₀ c₀ κ κ₀)
    (t k : ℕ)
    (P : OmegaPolymerType HF zCarrier) :
    (∑' n : ℕ, profile.M t k P n) ≤
      profile.prefixBudget t k P +
        profile.tailAmp t k P * (1 - profile.tailRatio t k P)⁻¹ :=
  (prefix_geometric_tail_summable_and_tsum_le
    (profile.M t k P) (profile.N t k P)
    (profile.M_nonneg t k P)
    (profile.prefix_bound t k P)
    (profile.tailAmp_nonneg t k P)
    (profile.tailRatio_nonneg t k P)
    (profile.tailRatio_lt_one t k P)
    (profile.tail_bound t k P)).2

/-- A certified-tail profile supplies the total pointwise residual estimate for
`H#`. -/
theorem residual_bound
    (profile :
      AppendixFHsharpCertifiedTailProfile HF zCarrier zK g
        C H₀ c₀ κ κ₀) :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  exact norm_appendixFHoleHsharp_le_residual_of_prefixTailMajorant
    HF zCarrier zK g
    profile.M profile.N profile.prefixBudget profile.tailAmp profile.tailRatio
    profile.M_nonneg profile.prefix_bound profile.tailAmp_nonneg
    profile.tailRatio_nonneg profile.tailRatio_lt_one profile.tail_bound
    profile.term_bound profile.closed_total_le_residual

/-- Real-part omega-rooted UV consumer fed by a packaged certified-tail `H#`
profile and the sufficient residual margin `κ ≥ 4κ₀ + 3`. -/
theorem singleScaleUVDecay
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
    (profile :
      AppendixFHsharpCertifiedTailProfile HF zCarrier zK g
        C H₀ c₀ κ κ₀)
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
      (residual_bound profile)
      hdisj hnoedges hholes_ne hCq

end AppendixFHsharpCertifiedTailProfile

/-- All-tail certified-tail instantiation of the source-normal weighted-tree
Appendix-F shape.

This theorem implements the `N = 0` certificate route: a source leaf-summation
bound on the weighted tree term, together with the pointwise activity-size
extraction `‖zK Q‖ ≤ epsilon * w Q`, yields the residual `H#` estimate from the
closed scalar comparison

`(Croot * epsilon) * (1 - Cleaf * epsilon)⁻¹ ≤ C * H₀ * exp(-c₀ t) * g k^κ₀`.

It proves only the finite/tree/certified-tail bookkeeping.  The source theorem
must still supply `hleaf_dimockF`, `hactivity`, smallness, and the closed scalar
budget. -/
theorem norm_appendixFHoleHsharp_le_residual_of_appendixF_weightedTree_certifiedTail
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (w : ∀ t k, OmegaPolymerType HF (zK t k) → ℝ)
    (epsilon Croot Cleaf : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hε0 : ∀ t k, 0 ≤ epsilon t k)
    (hCroot0 : ∀ t k, 0 ≤ Croot t k)
    (hCleaf0 : ∀ t k, 0 ≤ Cleaf t k)
    (hw :
      ∀ t k (Q : OmegaPolymerType HF (zK t k)),
        0 ≤ w t k Q)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF (zK t k)),
        ‖zK t k Q.val‖ ≤ epsilon t k * w t k Q)
    (hleaf_dimockF :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpWeightedTreeTerm
            HF (zK t k) (w t k) P.val n ≤
          Croot t k *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) *
            Cleaf t k ^ n)
    (hsmall :
      ∀ t k, Cleaf t k * epsilon t k < 1)
    (hbudget :
      ∀ t k,
        (Croot t k * epsilon t k) *
            (1 - Cleaf t k * epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  let decay : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ :=
    fun _t _k P =>
      Real.exp
        (-(polymerClusterResidualRate κ κ₀ *
          ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))
  let M : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℕ → ℝ :=
    fun t k P n =>
      (Croot t k * epsilon t k * decay t k P) *
        (Cleaf t k * epsilon t k) ^ n
  exact
    norm_appendixFHoleHsharp_le_residual_of_prefixTailMajorant
      HF zCarrier zK g M
      (fun _t _k _P => 0)
      (fun _t _k _P => 0)
      (fun t k P => Croot t k * epsilon t k * decay t k P)
      (fun t k _P => Cleaf t k * epsilon t k)
      (by
        intro t k P n
        have hdecay0 : 0 ≤ decay t k P := le_of_lt (Real.exp_pos _)
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (hCroot0 t k) (hε0 t k)) hdecay0)
          (pow_nonneg (mul_nonneg (hCleaf0 t k) (hε0 t k)) n))
      (by
        intro t k P
        simp)
      (by
        intro t k P
        have hdecay0 : 0 ≤ decay t k P := le_of_lt (Real.exp_pos _)
        exact mul_nonneg (mul_nonneg (hCroot0 t k) (hε0 t k)) hdecay0)
      (by
        intro t k P
        exact mul_nonneg (hCleaf0 t k) (hε0 t k))
      (by
        intro t k P
        exact hsmall t k)
      (by
        intro t k P i
        simp [M])
      (by
        intro t k P n
        calc
          ‖appendixFHoleHsharpTerm HF (zK t k) P.val n‖
              ≤ appendixFHoleHsharpAbsTerm HF (zK t k) P.val n :=
                norm_appendixFHoleHsharpTerm_le_absTerm HF (zK t k) P.val n
          _ ≤ appendixFHoleHsharpTreeTerm HF (zK t k) P.val n :=
                appendixFHoleHsharpAbsTerm_le_treeTerm HF (zK t k) P.val n
          _ ≤ M t k P n := by
                simpa [M, decay] using
                  appendixFHoleHsharpTreeTerm_le_factorized_of_weighted_bound
                    HF (zK t k) (w t k) P.val n
                    (epsilon t k) (Croot t k) (Cleaf t k) (decay t k P)
                    (hε0 t k) (hw t k) (hactivity t k)
                    (hleaf_dimockF t k P n))
      (by
        intro t k P
        have hdecay0 : 0 ≤ decay t k P := le_of_lt (Real.exp_pos _)
        have hmul :=
          mul_le_mul_of_nonneg_right (hbudget t k) hdecay0
        calc
          0 + (Croot t k * epsilon t k * decay t k P) *
                (1 - Cleaf t k * epsilon t k)⁻¹
              = ((Croot t k * epsilon t k) *
                  (1 - Cleaf t k * epsilon t k)⁻¹) * decay t k P := by
                    ring
          _ ≤
              (C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) *
                decay t k P := hmul
          _ =
              C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
                Real.exp
                  (-(polymerClusterResidualRate κ κ₀ *
                    ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
                    simp [decay])

end YangMills.RG
