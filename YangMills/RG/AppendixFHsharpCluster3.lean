/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpSourceMajorant

/-!
# Appendix F: source-facing `cluster3` contract for `H#`

Dimock II, Appendix F, theorem `cluster3` gives a closed with-holes
cluster-expansion estimate for the second-Ursell activity `H#`, after the
ultralocal integration of the first connected activity.  This module exposes
that theorem shape as an explicit source contract.

The contract deliberately does not prove Dimock's theorem, the leaf summation,
or any Yang--Mills raw-activity estimate.  It records the semantic hypotheses
as named proof obligations and consumes only the closed residual `H#` bound.
The coefficientwise tree-term route remains available in
`AppendixFSecondUrsellSource`; this file is the parallel source-faithful route
when one wants to consume Appendix F theorem `cluster3` directly.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- Source-facing closed Appendix-F contract corresponding to Dimock II
Appendix F, theorem `cluster3`.

The first four proposition fields are the obligations that must later be
instantiated by a concrete Yang--Mills/Balaban activity construction.  The final
field is the closed `H#` residual estimate, in the repository's shifted
modified-metric normalization used by the rooted summability consumers. -/
structure AppendixFHsharpCluster3Contract
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (C H₀ c₀ κ κ₀ : ℝ) where
  input_decay : Prop
  input_decay_holds : input_decay
  ultralocal_independence : Prop
  ultralocal_independence_holds : ultralocal_independence
  local_dependence : Prop
  local_dependence_holds : local_dependence
  local_influence : Prop
  local_influence_holds : local_influence
  cluster3_margin : 3 * κ₀ + 3 ≤ κ
  hsharp_residual_bound :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))

namespace AppendixFHsharpCluster3Contract

variable
    {HF : HoleFamily d L}
    {zCarrier : Finset (Cube d L) → ℂ}
    {zK : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {g : ℕ → ℝ}
    {C H₀ c₀ κ κ₀ : ℝ}

/-- Convert a source statement written with the unshifted modified metric
`exp (-r d_M(P))` into the repository's shifted rooted-consumer normalization
`exp (-r (d_M(P)+1))`.  The conversion is exact after paying the constant
factor `exp r`, where `r = κ - 3κ₀ - 3`. -/
def of_unshifted_residual_bound
    (hinput : Prop) (hinput_holds : hinput)
    (hultralocal : Prop) (hultralocal_holds : hultralocal)
    (hlocal : Prop) (hlocal_holds : hlocal)
    (hinfluence : Prop) (hinfluence_holds : hinfluence)
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hraw :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                (discreteModifiedMetric HF P.val : ℝ)))) :
    AppendixFHsharpCluster3Contract HF zCarrier zK g
      (C * Real.exp (polymerClusterResidualRate κ κ₀)) H₀ c₀ κ κ₀ where
  input_decay := hinput
  input_decay_holds := hinput_holds
  ultralocal_independence := hultralocal
  ultralocal_independence_holds := hultralocal_holds
  local_dependence := hlocal
  local_dependence_holds := hlocal_holds
  local_influence := hinfluence
  local_influence_holds := hinfluence_holds
  cluster3_margin := hmargin
  hsharp_residual_bound := by
    intro t k P
    have hshift :
        Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              (discreteModifiedMetric HF P.val : ℝ))) =
          Real.exp (polymerClusterResidualRate κ κ₀) *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    calc
      ‖appendixFHoleHsharp HF (zK t k) P.val‖
          ≤ C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
              Real.exp
                (-(polymerClusterResidualRate κ κ₀ *
                  (discreteModifiedMetric HF P.val : ℝ))) :=
        hraw t k P
      _ =
          (C * Real.exp (polymerClusterResidualRate κ κ₀)) * H₀ *
              Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
                Real.exp
                  (-(polymerClusterResidualRate κ κ₀ *
                    ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
        rw [hshift]
        ring

/-- The closed residual estimate carried by a `cluster3` source contract. -/
theorem residual_bound
    (hsrc :
      AppendixFHsharpCluster3Contract
        HF zCarrier zK g C H₀ c₀ κ κ₀) :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) :=
  hsrc.hsharp_residual_bound

end AppendixFHsharpCluster3Contract

/-- A `cluster3` source contract feeds directly into the existing residual
consumer for the totalized Appendix-F `H#` activity. -/
theorem norm_appendixFHoleHsharp_le_residual_of_cluster3_contract
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpCluster3Contract
        HF zCarrier zK g C H₀ c₀ κ κ₀) :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) :=
  hsrc.hsharp_residual_bound

/-- Integrated-`K#` specialization of the closed `cluster3` contract. -/
theorem norm_appendixFHoleHsharpOfIntegratedKsharp_le_residual_of_cluster3_contract
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Hraw : ∀ t k,
      OmegaPolymerType HF (z t k) →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : ℕ → ℕ → MeasureTheory.Measure γ)
    (ν : ℕ → ℕ → MeasureTheory.Measure β)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpCluster3Contract HF zCarrier
        (fun t k Y =>
          appendixFHoleIntegratedKsharpActivityFamily
            HF z Λ Hraw μ ν t k Y)
        g C H₀ c₀ κ κ₀)
    (t k : ℕ)
    (P : OmegaPolymerType HF zCarrier) :
    ‖appendixFHoleHsharpOfIntegratedKsharp
        HF (z t k) (Λ t k) (Hraw t k) (μ t k) (ν t k) P.val‖ ≤
      C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
        Real.exp
          (-(polymerClusterResidualRate κ κ₀ *
            ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  change
    ‖appendixFHoleHsharp HF
        (appendixFHoleIntegratedKsharpActivity
          HF (z t k) (Λ t k) (Hraw t k) (μ t k) (ν t k)) P.val‖ ≤
      C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
        Real.exp
          (-(polymerClusterResidualRate κ κ₀ *
            ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))
  exact hsrc.hsharp_residual_bound t k P

/-- Real-part omega-rooted UV consumer fed by a closed `cluster3` source
contract and the sufficient residual margin `κ ≥ 4κ₀ + 3`.

This theorem consumes the final Appendix-F `H#` estimate directly.  It does not
assert that the Yang--Mills activities satisfy the `cluster3` input hypotheses;
those remain the named obligations inside the contract. -/
theorem
    singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_cluster3_contract
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpCluster3Contract
        HF zCarrier zK g C H₀ c₀ κ κ₀)
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
      c₀ κ₀ :=
  singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin
    HF zCarrier r zK Rsc g hC hH₀ hg hκ hR
    hsrc.hsharp_residual_bound hdisj hnoedges hholes_ne hCq

/-- Integrated-`K#` real-part UV consumer fed by the closed `cluster3`
contract. -/
theorem
    singleScaleUVDecay_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_cluster3_contract
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Hraw : ∀ t k,
      OmegaPolymerType HF (z t k) →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : ℕ → ℕ → MeasureTheory.Measure γ)
    (ν : ℕ → ℕ → MeasureTheory.Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpCluster3Contract HF zCarrier
        (fun t k Y =>
          appendixFHoleIntegratedKsharpActivityFamily
            HF z Λ Hraw μ ν t k Y)
        g C H₀ c₀ κ κ₀)
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
              (appendixFHoleHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (Hraw t k)
                (μ t k) (ν t k) P.val.val))
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
  refine
    singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_cluster3_contract
      HF zCarrier r
      (fun t k Y =>
        appendixFHoleIntegratedKsharpActivityFamily
          HF z Λ Hraw μ ν t k Y)
      Rsc g hsrc hC hH₀ hg hκ ?_
      hdisj hnoedges hholes_ne hCq
  intro t k
  change
    Rsc t k =
      ∑' P : { P : OmegaPolymerType HF zCarrier //
          r ∈ skeleton HF P.val },
        Complex.re
          (appendixFHoleHsharp HF
            (appendixFHoleIntegratedKsharpActivity
              HF (z t k) (Λ t k) (Hraw t k) (μ t k) (ν t k))
            P.val.val)
  exact hR t k

end YangMills.RG
