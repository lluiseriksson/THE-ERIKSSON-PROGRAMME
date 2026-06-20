/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpGeometricMajorant

/-!
# Appendix F: source-facing geometric `H#` profiles

This module packages the closed-form geometric `H#` majorant contract into a
single structure.  A later KP/Ursell source proof should be able to construct
one such profile by supplying amplitudes `A`, ratios `q`, the termwise bound

`‖appendixFHoleHsharpTerm ... n‖ ≤ A * q^n`,

and the residual comparison for the closed total `A*(1-q)⁻¹`.

The theorems below then expose the already-verified summability, tail,
pointwise residual, and omega-rooted UV consumers from that single profile.
No source estimate is proved here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

variable {d L : ℕ} [NeZero L]

/-- A source-facing package for the geometric majorant expected from the
second-Ursell/KP estimate for `H#`.  The fields are exactly the data consumed by
`AppendixFHsharpGeometricMajorant`: nonnegative amplitudes, ratios strictly
below one, the termwise cluster-size bound, and the comparison of the closed
geometric total with the residual profile. -/
structure AppendixFHsharpGeometricMajorantProfile
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (C H₀ c₀ κ κ₀ : ℝ) where
  A : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ
  q : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ
  A_nonneg :
    ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ A t k P
  q_nonneg :
    ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ q t k P
  q_lt_one :
    ∀ t k (P : OmegaPolymerType HF zCarrier), q t k P < 1
  term_bound :
    ∀ t k (P : OmegaPolymerType HF zCarrier) n,
      ‖appendixFHoleHsharpTerm HF (zK t k) P.val n‖ ≤
        A t k P * q t k P ^ n
  closed_total_le_residual :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      A t k P * (1 - q t k P)⁻¹ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))

namespace AppendixFHsharpGeometricMajorantProfile

variable
    {HF : HoleFamily d L}
    {zCarrier : Finset (Cube d L) → ℂ}
    {zK : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {g : ℕ → ℝ}
    {C H₀ c₀ κ κ₀ : ℝ}

/-- A geometric profile supplies fixed-target summability of the `H#`
cluster-size terms. -/
theorem summable_terms
    (profile :
      AppendixFHsharpGeometricMajorantProfile HF zCarrier zK g
        C H₀ c₀ κ κ₀)
    (t k : ℕ)
    (P : OmegaPolymerType HF zCarrier) :
    Summable (fun n : ℕ =>
      appendixFHoleHsharpTerm HF (zK t k) P.val n) := by
  exact summable_appendixFHoleHsharpTerm_of_norm_le_majorant
    HF (zK t k) P.val
    (fun n : ℕ => profile.A t k P * profile.q t k P ^ n)
    (summable_geometric_majorant
      (profile.q_nonneg t k P) (profile.q_lt_one t k P))
    (profile.term_bound t k P)

/-- A geometric profile supplies the closed shifted-tail error estimate for
finite `H#` truncations. -/
theorem tail_bound
    (profile :
      AppendixFHsharpGeometricMajorantProfile HF zCarrier zK g
        C H₀ c₀ κ κ₀)
    (t k : ℕ)
    (P : OmegaPolymerType HF zCarrier)
    (N : ℕ) :
    ‖appendixFHoleHsharp HF (zK t k) P.val -
        appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
      profile.A t k P * profile.q t k P ^ N *
        (1 - profile.q t k P)⁻¹ := by
  exact norm_appendixFHoleHsharp_sub_partial_le_geometric_tail
    HF (zK t k) P.val N
    (profile.q_nonneg t k P)
    (profile.q_lt_one t k P)
    (profile.term_bound t k P)

/-- A geometric profile supplies the pointwise total residual estimate for
`H#`. -/
theorem residual_bound
    (profile :
      AppendixFHsharpGeometricMajorantProfile HF zCarrier zK g
        C H₀ c₀ κ κ₀) :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  exact norm_appendixFHoleHsharp_le_residual_of_geometric_term_majorant
    HF zCarrier zK g profile.A profile.q
    profile.A_nonneg profile.q_nonneg profile.q_lt_one
    profile.term_bound profile.closed_total_le_residual

/-- Real-part omega-rooted UV consumer fed by a packaged geometric `H#`
majorant profile and the sufficient residual margin `κ ≥ 4κ₀ + 3`. -/
theorem singleScaleUVDecay_of_profile
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
      AppendixFHsharpGeometricMajorantProfile HF zCarrier zK g
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
    singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_geometric_term_majorant
      HF zCarrier r zK Rsc g profile.A profile.q
      hC hH₀ hg hκ hR
      profile.A_nonneg profile.q_nonneg profile.q_lt_one
      profile.term_bound profile.closed_total_le_residual
      hdisj hnoedges hholes_ne hCq

end AppendixFHsharpGeometricMajorantProfile

end YangMills.RG
