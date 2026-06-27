/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SecondGasAdapter
import YangMills.RG.AppendixFSecondUrsellSource
import YangMills.RG.AppendixFHsharpCluster3

/-!
# Balaban CMP116 to the Appendix-F `H#` consumers

This module specializes the existing source-facing `H#` machinery to the
CMP116 first-activity adapter.  The only specialization made here is the
fluctuation measure: the abstract first integration measure is fixed to
Balaban's product Gaussian `dmu0`, formalized as
`balabanCMP116BondGaussian`.

No leaf summation, cluster3 theorem, small-field estimate, or Yang--Mills
source bound is proved here.  Those remain explicit source hypotheses in the
majorant and contract arguments below.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators

/-! ## CMP116 evaluated `K#` as a second-Ursell `H#` input -/

/-- The CMP116 evaluated `H#` normal form before spectator integration: the
second-Ursell `H#` applied to the evaluated CMP116 `K#` activity at a spectator
field. -/
noncomputable def balabanCMP116AppendixFHsharpOfKsharp
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (ψ : ∀ x, Ψ x)
    (Y : Finset (Cube d L)) : ℂ :=
  appendixFHoleHsharpOfKsharp HF z Λ F.activity
    (balabanCMP116BondGaussian lieDim) ψ Y

@[simp] theorem balabanCMP116AppendixFHsharpOfKsharp_eq_hsharp
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (ψ : ∀ x, Ψ x)
    (Y : Finset (Cube d L)) :
    balabanCMP116AppendixFHsharpOfKsharp HF z Λ F ψ Y =
      appendixFHoleHsharp HF
        (balabanCMP116AppendixFSecondGasActivity HF z Λ F ψ) Y := by
  rfl

/-- Full-target spectator dependency for the CMP116 evaluated `H#` object.
The only source support input is the existing CMP116 Appendix-F support
package; it supplies the raw activity spectator support inclusion consumed by
the generic Appendix-F `H#` wrapper. -/
theorem balabanCMP116AppendixFHsharpOfKsharp_eq_of_agreeOn
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F)
    {ψ₁ ψ₂ : ∀ x, Ψ x}
    (hψ : AgreeOn Y ψ₁ ψ₂) :
    balabanCMP116AppendixFHsharpOfKsharp HF z Λ F ψ₁ Y =
      balabanCMP116AppendixFHsharpOfKsharp HF z Λ F ψ₂ Y := by
  exact appendixFHoleHsharpOfKsharp_eq_of_agreeOn
    HF z Λ F.activity (balabanCMP116BondGaussian lieDim) Y
    h.spectatorSupport_subset_full hψ

/-- Active-skeleton spectator dependency for the CMP116 evaluated `H#` object. -/
theorem balabanCMP116AppendixFHsharpOfKsharp_eq_of_agreeOn_skeleton
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F)
    {ψ₁ ψ₂ : ∀ x, Ψ x}
    (hψ : AgreeOn (skeleton HF Y) ψ₁ ψ₂) :
    balabanCMP116AppendixFHsharpOfKsharp HF z Λ F ψ₁ Y =
      balabanCMP116AppendixFHsharpOfKsharp HF z Λ F ψ₂ Y := by
  exact appendixFHoleHsharpOfKsharp_eq_of_agreeOn_skeleton
    HF z Λ F.activity (balabanCMP116BondGaussian lieDim) Y
    h.spectatorSupport_subset_skeleton hψ

/-! ## Scale-indexed CMP116 integrated first activity -/

/-- Scale-indexed spectator-integrated CMP116 first activity, with Balaban's
fluctuation Gaussian fixed and the spectator law left as an explicit measure
family. -/
noncomputable def balabanCMP116AppendixFIntegratedKsharpActivityFamily
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (t k : ℕ)
    (Y : Finset (Cube d L)) : ℂ :=
  balabanCMP116AppendixFIntegratedKsharpActivity
    HF (z t k) (Λ t k) (F t k) (ν t k) Y

@[simp] theorem balabanCMP116AppendixFIntegratedKsharpActivityFamily_eq
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (t k : ℕ)
    (Y : Finset (Cube d L)) :
    balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t k Y =
      appendixFHoleIntegratedKsharpActivityFamily
        HF z Λ (fun t k => (F t k).activity)
        (fun _ _ => balabanCMP116BondGaussian lieDim) ν t k Y := by
  rfl

/-- Scale-indexed CMP116 integrated first-activity estimate at the canonical
first-gas `K#` rate, derived from the rooted raw-metric estimate.

This theorem produces exactly the pointwise `K#` activity hypothesis consumed by
the leaf-summation wrappers when `epsilon t k = 2 * H₀ t k * K₀ t k`.  The raw
decay, rooted first-cover budget, spectator probability measure, and
fluctuation integrability remain explicit source hypotheses. -/
theorem
    balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_rooted
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (H₀ K₀ : ℕ → ℕ → ℝ)
    {κ κ₀ : ℝ}
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hH₀ : ∀ t k, 0 ≤ H₀ t k)
    (hH₀_one : ∀ t k, H₀ t k ≤ 1)
    (hK₀ : ∀ t k, 0 ≤ K₀ t k)
    (hsmall : ∀ t k, 2 * H₀ t k * K₀ t k ≤ 1)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ t k r,
      (∑ X ∈ (Λ t k).filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀ t k)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        H₀ t k * appendixFHoleExpWeight HF κ X.val)
    (hint : ∀ t k Y,
      Y ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k) →
      ∀ ψ : (∀ _ : Cube d L, β),
        Integrable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            (balabanCMP116AppendixFConnectedLocalActivity
              HF (z t k) (Λ t k) (F t k) Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim)) :
    ∀ t k (Q : OmegaPolymerType HF
      (balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t k)),
      ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Q.val‖ ≤
        (2 * H₀ t k * K₀ t k) *
          appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Q.val := by
  intro t k Q
  by_cases hQ :
      Q.val ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF (z t k) => skeleton HF X.val)
        (fun X : OmegaPolymerType HF (z t k) => X.val)
        (Λ t k)
  · haveI : IsProbabilityMeasure (ν t k) := hν t k
    simpa [balabanCMP116AppendixFIntegratedKsharpActivityFamily] using
      (norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_rawMetricDecay_rooted
        HF (z t k) (Λ t k) (F t k) (ν t k) hQ
        (hH₀ t k) (hH₀_one t k) (hK₀ t k) (hsmall t k)
        hκ₀ hκ (hroot t k) (hraw t k) (hint t k Q.val hQ))
  · have hzero :=
      balabanCMP116AppendixFIntegratedKsharpActivity_eq_zero_of_not_mem_targetRegion
        HF (z t k) (Λ t k) (F t k) (ν t k) Q.val hQ
    calc
      ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Q.val‖ = 0 := by
        change
          ‖balabanCMP116AppendixFIntegratedKsharpActivity
              HF (z t k) (Λ t k) (F t k) (ν t k) Q.val‖ = 0
        rw [hzero]
        simp
      _ ≤
          (2 * H₀ t k * K₀ t k) *
            appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Q.val :=
        mul_nonneg
          (mul_nonneg (mul_nonneg zero_le_two (hH₀ t k)) (hK₀ t k))
          (appendixFHoleExpWeight_nonneg HF
            (appendixFKsharpRate κ κ₀) Q.val)

/-- Source-package form of
`balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_rooted`.

The bound has the same rooted raw-decay and smallness assumptions, but the
fluctuation-integrability argument is generated from the localized CMP116
measurability fields scale by scale. -/
theorem
    balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_rooted_of_source
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (H₀ K₀ : ℕ → ℕ → ℝ)
    {κ κ₀ : ℝ}
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hH₀ : ∀ t k, 0 ≤ H₀ t k)
    (hH₀_one : ∀ t k, H₀ t k ≤ 1)
    (hK₀ : ∀ t k, 0 ≤ K₀ t k)
    (hsmall : ∀ t k, 2 * H₀ t k * K₀ t k ≤ 1)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ t k r,
      (∑ X ∈ (Λ t k).filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀ t k)
    (hraw : ∀ t k ψ φ X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval ψ φ‖ ≤
        H₀ t k * appendixFHoleExpWeight HF κ X.val) :
    ∀ t k (Q : OmegaPolymerType HF
      (balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t k)),
      ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Q.val‖ ≤
        (2 * H₀ t k * K₀ t k) *
          appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Q.val :=
  balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_rooted
    HF z Λ F ν H₀ K₀ hν hH₀ hH₀_one hK₀ hsmall hκ₀ hκ hroot hraw
    (fun t k _Y hY ψ =>
      integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted_of_source
        HF (z t k) (Λ t k) (F t k) hY ψ
        (hH₀ t k) (hH₀_one t k) (hK₀ t k) hκ₀ hκ (hroot t k)
        (fun φ X hX => hraw t k ψ φ X hX))

/-- The CMP116 integrated `H#` normal form: the second-Ursell `H#` applied to
the spectator-integrated CMP116 first activity. -/
noncomputable def balabanCMP116AppendixFHsharpOfIntegratedKsharp
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β)
    (Y : Finset (Cube d L)) : ℂ :=
  appendixFHoleHsharpOfIntegratedKsharp HF z Λ F.activity
    (balabanCMP116BondGaussian lieDim) ν Y

@[simp] theorem balabanCMP116AppendixFHsharpOfIntegratedKsharp_eq_hsharp
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β)
    (Y : Finset (Cube d L)) :
    balabanCMP116AppendixFHsharpOfIntegratedKsharp HF z Λ F ν Y =
      appendixFHoleHsharp HF
        (balabanCMP116AppendixFIntegratedKsharpActivity HF z Λ F ν) Y := by
  rfl

/-! ## Source-majorant constructors specialized to CMP116 -/

/-- CMP116 specialization of the integrated absolute-term source-majorant
constructor.  The finite source estimate is still supplied explicitly. -/
noncomputable def
    balabanCMP116AppendixFHsharpSourceMajorant_of_absTerm_geometric
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (g : ℕ → ℝ)
    (A q : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hA :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ A t k P)
    (hq0 :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ q t k P)
    (hq1 :
      ∀ t k (P : OmegaPolymerType HF zCarrier), q t k P < 1)
    (habs :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpAbsTerm HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k) P.val n ≤
          A t k P * q t k P ^ n)
    (hclosed :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        A t k P * (1 - q t k P)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    AppendixFHsharpSourceMajorant HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C H₀ c₀ κ κ₀ := by
  simpa [balabanCMP116AppendixFIntegratedKsharpActivityFamily] using
    (appendixFHsharpSourceMajorant_of_integratedKsharp_absTerm_geometric
      HF zCarrier z Λ (fun t k => (F t k).activity)
      (fun _ _ => balabanCMP116BondGaussian lieDim) ν
      g A q hA hq0 hq1 habs hclosed)

/-- CMP116 specialization of the factorized absolute-term source-majorant
constructor. -/
noncomputable def
    balabanCMP116AppendixFHsharpSourceMajorant_of_factorized_absTerm_geometric
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (g : ℕ → ℝ)
    (B ρ : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hB0 : ∀ t k, 0 ≤ B t k)
    (hρ0 : ∀ t k, 0 ≤ ρ t k)
    (hρ1 : ∀ t k, ρ t k < 1)
    (habs :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpAbsTerm HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k) P.val n ≤
          (B t k *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) *
            ρ t k ^ n)
    (hBclosed :
      ∀ t k,
        B t k * (1 - ρ t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    AppendixFHsharpSourceMajorant HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C H₀ c₀ κ κ₀ := by
  simpa [balabanCMP116AppendixFIntegratedKsharpActivityFamily] using
    (appendixFHsharpSourceMajorant_of_integratedKsharp_factorized_absTerm_geometric
      HF zCarrier z Λ (fun t k => (F t k).activity)
      (fun _ _ => balabanCMP116BondGaussian lieDim) ν
      g B ρ hB0 hρ0 hρ1 habs hBclosed)

/-- CMP116 specialization of the integrated finite tree-term source-majorant
constructor. -/
noncomputable def
    balabanCMP116AppendixFHsharpSourceMajorant_of_treeTerm_geometric
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (g : ℕ → ℝ)
    (A q : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hA :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ A t k P)
    (hq0 :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ q t k P)
    (hq1 :
      ∀ t k (P : OmegaPolymerType HF zCarrier), q t k P < 1)
    (htree :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpTreeTerm HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k) P.val n ≤
          A t k P * q t k P ^ n)
    (hclosed :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        A t k P * (1 - q t k P)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    AppendixFHsharpSourceMajorant HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C H₀ c₀ κ κ₀ := by
  simpa [balabanCMP116AppendixFIntegratedKsharpActivityFamily] using
    (appendixFHsharpSourceMajorant_of_integratedKsharp_treeTerm_geometric
      HF zCarrier z Λ (fun t k => (F t k).activity)
      (fun _ _ => balabanCMP116BondGaussian lieDim) ν
      g A q hA hq0 hq1 htree hclosed)

/-- CMP116 specialization of the factorized finite tree-term source-majorant
constructor. -/
noncomputable def
    balabanCMP116AppendixFHsharpSourceMajorant_of_factorized_treeTerm_geometric
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (g : ℕ → ℝ)
    (B ρ : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hB0 : ∀ t k, 0 ≤ B t k)
    (hρ0 : ∀ t k, 0 ≤ ρ t k)
    (hρ1 : ∀ t k, ρ t k < 1)
    (htree :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpTreeTerm HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k) P.val n ≤
          (B t k *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) *
            ρ t k ^ n)
    (hBclosed :
      ∀ t k,
        B t k * (1 - ρ t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    AppendixFHsharpSourceMajorant HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C H₀ c₀ κ κ₀ := by
  simpa [balabanCMP116AppendixFIntegratedKsharpActivityFamily] using
    (appendixFHsharpSourceMajorant_of_integratedKsharp_factorized_treeTerm_geometric
      HF zCarrier z Λ (fun t k => (F t k).activity)
      (fun _ _ => balabanCMP116BondGaussian lieDim) ν
      g B ρ hB0 hρ0 hρ1 htree hBclosed)

/-! ## Closed residual and UV consumers specialized to CMP116 -/

/-- The packaged source-majorant residual consumer for the CMP116 integrated
`H#` object. -/
theorem
    norm_balabanCMP116AppendixFHsharpOfIntegratedKsharp_le_residual_of_source_majorant
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpSourceMajorant HF zCarrier
        (fun t k Y =>
          balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Y)
        g C H₀ c₀ κ κ₀)
    (t k : ℕ)
    (P : OmegaPolymerType HF zCarrier) :
    ‖balabanCMP116AppendixFHsharpOfIntegratedKsharp
        HF (z t k) (Λ t k) (F t k) (ν t k) P.val‖ ≤
      C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
        Real.exp
          (-(polymerClusterResidualRate κ κ₀ *
            ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  simpa [balabanCMP116AppendixFIntegratedKsharpActivityFamily,
    balabanCMP116AppendixFHsharpOfIntegratedKsharp] using
    (norm_appendixFHoleHsharpOfIntegratedKsharp_le_residual_of_source_majorant
      HF zCarrier z Λ (fun t k => (F t k).activity)
      (fun _ _ => balabanCMP116BondGaussian lieDim) ν g hsrc t k P)

/-- Real-part rooted absolute summability for the CMP116 integrated `H#`
object, fed by the packaged source-majorant contract. -/
theorem
    summable_abs_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_source_majorant
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpSourceMajorant HF zCarrier
        (fun t k Y =>
          balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Y)
        g C H₀ c₀ κ κ₀)
    (hC : 0 ≤ C)
    (hH₀ : 0 ≤ H₀)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ) :
    ∀ t k,
      Summable
        (fun P : { P : OmegaPolymerType HF zCarrier //
            r ∈ skeleton HF P.val } =>
          |Complex.re
            (balabanCMP116AppendixFHsharpOfIntegratedKsharp
              HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val)|) := by
  intro t k
  simpa [balabanCMP116AppendixFHsharpOfIntegratedKsharp] using
    (summable_abs_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_source_majorant
      HF zCarrier r z Λ (fun t k => (F t k).activity)
      (fun _ _ => balabanCMP116BondGaussian lieDim) ν
      g hsrc hC hH₀ hg hκ t k)

/-- The closed `cluster3` contract residual consumer for the CMP116 integrated
`H#` object. -/
theorem
    norm_balabanCMP116AppendixFHsharpOfIntegratedKsharp_le_residual_of_cluster3_contract
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpCluster3Contract HF zCarrier
        (fun t k Y =>
          balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Y)
        g C H₀ c₀ κ κ₀)
    (t k : ℕ)
    (P : OmegaPolymerType HF zCarrier) :
    ‖balabanCMP116AppendixFHsharpOfIntegratedKsharp
        HF (z t k) (Λ t k) (F t k) (ν t k) P.val‖ ≤
      C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
        Real.exp
          (-(polymerClusterResidualRate κ κ₀ *
            ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  simpa [balabanCMP116AppendixFIntegratedKsharpActivityFamily,
    balabanCMP116AppendixFHsharpOfIntegratedKsharp] using
    (norm_appendixFHoleHsharpOfIntegratedKsharp_le_residual_of_cluster3_contract
      HF zCarrier z Λ (fun t k => (F t k).activity)
      (fun _ _ => balabanCMP116BondGaussian lieDim) ν g hsrc t k P)

/-- Real-part omega-rooted UV decay for the CMP116 integrated `H#` object,
fed by the packaged source-majorant contract. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_source_majorant
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpSourceMajorant HF zCarrier
        (fun t k Y =>
          balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Y)
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
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val))
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
    singleScaleUVDecay_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_source_majorant
      HF zCarrier r z Λ (fun t k => (F t k).activity)
      (fun _ _ => balabanCMP116BondGaussian lieDim) ν
      Rsc g hsrc hC hH₀ hg hκ ?_
      hdisj hnoedges hholes_ne hCq
  intro t k
  simpa [balabanCMP116AppendixFHsharpOfIntegratedKsharp] using hR t k

/-- Real-part omega-rooted UV decay for the CMP116 integrated `H#` object,
fed by the closed `cluster3` contract. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_cluster3_contract
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpCluster3Contract HF zCarrier
        (fun t k Y =>
          balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Y)
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
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val))
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
    singleScaleUVDecay_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_cluster3_contract
      HF zCarrier r z Λ (fun t k => (F t k).activity)
      (fun _ _ => balabanCMP116BondGaussian lieDim) ν
      Rsc g hsrc hC hH₀ hg hκ ?_
      hdisj hnoedges hholes_ne hCq
  intro t k
  simpa [balabanCMP116AppendixFHsharpOfIntegratedKsharp] using hR t k

end YangMills.RG
