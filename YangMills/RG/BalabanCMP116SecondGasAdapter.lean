/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116KsharpAdapter
import YangMills.RG.AppendixFSecondGas
import YangMills.RG.PhysicalGaugeCMP116ActivityAdapter

/-!
# Balaban CMP116 to the second Appendix-F gas

This file lifts the CMP116-specialized `K#` adapter one step further, to the
source-facing second hard-core gas used by the later `H#` layer.  The
fluctuation measure remains the product Gaussian `dmu0`; spectator integration
is left as an explicit product measure `nu`, because the Yang-Mills source
still has to identify and bound the corresponding spectator-field law.

No new analytic estimate is introduced here.  KP smallness and source decay
remain hypotheses of the existing Appendix-F interfaces; source-package
wrappers below discharge the fluctuation integrability side condition from the
localized CMP116 measurability fields.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators

/-! ## Evaluated first activity as a second gas -/

/-- The evaluated CMP116-specialized first integrated activity, regarded as the
scalar activity of the second Appendix-F hard-core gas. -/
noncomputable def balabanCMP116AppendixFSecondGasActivity
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (ψ : ∀ x, Ψ x)
    (Y : Finset (Cube d L)) : ℂ :=
  (balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ

/-- The second hard-core gas obtained by evaluating the CMP116-specialized
`K#` at a spectator field. -/
noncomputable def balabanCMP116AppendixFSecondGas
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (ψ : ∀ x, Ψ x) :
    KP.PolymerSystem :=
  appendixFHoleSecondGas HF z Λ F.activity
    (balabanCMP116BondGaussian lieDim) ψ

noncomputable instance balabanCMP116AppendixFSecondGas_fintype
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (ψ : ∀ x, Ψ x) :
    Fintype (balabanCMP116AppendixFSecondGas HF z Λ F ψ).Polymer :=
  inferInstanceAs (Fintype
    (appendixFHoleSecondGas HF z Λ F.activity
      (balabanCMP116BondGaussian lieDim) ψ).Polymer)

@[simp] theorem balabanCMP116AppendixFSecondGas_activity
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (ψ : ∀ x, Ψ x)
    (Y : (balabanCMP116AppendixFSecondGas HF z Λ F ψ).Polymer) :
    (balabanCMP116AppendixFSecondGas HF z Λ F ψ).activity Y =
      (balabanCMP116AppendixFKsharp HF z Λ F Y.val).globalEval ψ := by
  rfl

/-- The evaluated CMP116 second-gas activity is zero away from the first
connected-cover target region. -/
theorem balabanCMP116AppendixFSecondGasActivity_eq_zero_of_not_mem_targetRegion
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (ψ : ∀ x, Ψ x)
    (Y : Finset (Cube d L))
    (hY : Y ∉ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ) :
    balabanCMP116AppendixFSecondGasActivity HF z Λ F ψ Y = 0 := by
  unfold balabanCMP116AppendixFSecondGasActivity balabanCMP116AppendixFKsharp
  change
    appendixFHoleSecondGasActivity HF z Λ F.activity
      (balabanCMP116BondGaussian lieDim) ψ Y = 0
  exact appendixFHoleSecondGasActivity_eq_zero_of_not_mem_targetRegion
    HF z Λ F.activity (balabanCMP116BondGaussian lieDim) ψ Y hY

/-- Full-target dependency for the evaluated CMP116 second-gas activity. -/
theorem balabanCMP116AppendixFSecondGasActivity_eq_of_agreeOn
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
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
    balabanCMP116AppendixFSecondGasActivity HF z Λ F ψ₁ Y =
      balabanCMP116AppendixFSecondGasActivity HF z Λ F ψ₂ Y := by
  exact balabanCMP116AppendixFKsharp_globalEval_eq_of_agreeOn
    HF z Λ F Y h hψ

/-- Active-skeleton dependency for the evaluated CMP116 second-gas activity. -/
theorem balabanCMP116AppendixFSecondGasActivity_eq_of_agreeOn_skeleton
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
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
    balabanCMP116AppendixFSecondGasActivity HF z Λ F ψ₁ Y =
      balabanCMP116AppendixFSecondGasActivity HF z Λ F ψ₂ Y := by
  exact balabanCMP116AppendixFKsharp_globalEval_eq_of_agreeOn_skeleton
    HF z Λ F Y h hψ

/-- KP-ready pointwise majorant for the evaluated CMP116 second gas. -/
def BalabanCMP116AppendixFSecondGasKPMajorant
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (ψ : ∀ x, Ψ x)
    (t q A : ℝ) : Prop :=
  AppendixFHoleSecondGasKPMajorant HF z Λ F.activity
    (balabanCMP116BondGaussian lieDim) ψ t q A

/-- The evaluated CMP116 second gas satisfies the standard hard-core KP
criterion whenever the existing KP-ready majorant is supplied. -/
theorem balabanCMP116AppendixFSecondGas_KPCriterion_of_majorant
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (ψ : ∀ x, Ψ x)
    (t q A : ℝ)
    (hA0 : 0 ≤ A)
    (hK : BalabanCMP116AppendixFSecondGasKPMajorant HF z Λ F ψ t q A)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hq0 : 0 ≤ q)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (q * 2 ^ (3 ^ d + 1)) < 1)
    (hsmall :
      A * (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (q * 2 ^ (3 ^ d + 1)))⁻¹ ≤ 1) :
    KP.KPCriterion
      ((balabanCMP116AppendixFSecondGas HF z Λ F ψ).scaleActivity
        (Real.exp t))
      (fun Y => (Y.val.card : ℝ)) := by
  simpa [balabanCMP116AppendixFSecondGas,
    BalabanCMP116AppendixFSecondGasKPMajorant] using
    (appendixFHoleSecondGas_KPCriterion_of_majorant
      HF z Λ F.activity (balabanCMP116BondGaussian lieDim) ψ
      t q A hA0 hK hdisj hnoedges hholes_ne hq0 hCq hsmall)

/-! ## Spectator-integrated CMP116 `K#` activity -/

/-- The spectator-integrated scalar CMP116 first activity.  The spectator
measure `nu` is explicit; this file does not identify it with any Yang-Mills
continuum measure. -/
noncomputable def balabanCMP116AppendixFIntegratedKsharpActivity
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
  appendixFHoleIntegratedKsharpActivity HF z Λ F.activity
    (balabanCMP116BondGaussian lieDim) ν Y

@[simp] theorem balabanCMP116AppendixFIntegratedKsharpActivity_eq_integral
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
    balabanCMP116AppendixFIntegratedKsharpActivity HF z Λ F ν Y =
      ∫ ψ : (∀ _ : Cube d L, β),
        (balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ
        ∂(Measure.pi fun _ : Cube d L => ν) := by
  rfl

/-- Spectator-integrated CMP116 `K#` scalar estimate at the canonical first-gas
rate, derived from the rooted raw-metric estimate.

The theorem still carries the genuine source obligations explicitly: raw
pointwise decay for every spectator field, fluctuation integrability for every
spectator field, and probability normalization of the spectator measure. -/
theorem norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_rawMetricDecay_rooted
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β) [IsProbabilityMeasure ν]
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hsmall : 2 * H₀ * K₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ ψ φ X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hint : ∀ ψ : (∀ _ : Cube d L, β),
      Integrable
        (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
          (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).globalEval
            ψ φ)
        (balabanCMP116Dmu0 (Cube d L) lieDim)) :
    ‖balabanCMP116AppendixFIntegratedKsharpActivity HF z Λ F ν Y‖ ≤
      (2 * H₀ * K₀) *
        appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  simpa [balabanCMP116AppendixFIntegratedKsharpActivity,
    balabanCMP116AppendixFKsharp] using
    (norm_appendixFHoleIntegratedKsharpActivity_le_of_globalEval_bound
      HF z Λ F.activity (balabanCMP116BondGaussian lieDim) ν Y
      (B := (2 * H₀ * K₀) *
        appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y)
      (fun ψ =>
        norm_balabanCMP116AppendixFKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted
          HF z Λ F hY ψ hH₀ hH₀_one hK₀ hsmall hκ₀ hκ hroot
          (fun φ X hX => hraw ψ φ X hX)
          (hint ψ)))

/-- Source-package form of the spectator-integrated CMP116 `K#` scalar
estimate.

This removes the explicit fluctuation-integrability hypothesis from
`norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_rawMetricDecay_rooted`:
the needed integrability is compiled from the localized CMP116 source
measurability fields together with the same rooted raw-metric decay estimate.
-/
theorem
    norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_rawMetricDecay_rooted_of_source
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β) [IsProbabilityMeasure ν]
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hsmall : 2 * H₀ * K₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ ψ φ X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val) :
    ‖balabanCMP116AppendixFIntegratedKsharpActivity HF z Λ F ν Y‖ ≤
      (2 * H₀ * K₀) *
        appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y :=
  norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_rawMetricDecay_rooted
    HF z Λ F ν hY hH₀ hH₀_one hK₀ hsmall hκ₀ hκ hroot hraw
    (fun ψ =>
      integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted_of_source
        HF z Λ F hY ψ hH₀ hH₀_one hK₀ hκ₀ hκ hroot
        (fun φ X hX => hraw ψ φ X hX))

/-- Transport-package form of the spectator-integrated CMP116 `K#` estimate.

This removes the independent localized family and `hraw` arguments from the
single-scale K# call site.  They are projected from the supplied
`PhysicalGaugeCMP116ActivityTransport`; all probability, rooted leaf budget,
smallness, and rate-margin hypotheses remain explicit. -/
theorem norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_transport
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    {Λ : Finset (OmegaPolymerType HF z)}
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound H0 κ : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      OmegaPolymerType HF z → PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      OmegaPolymerType HF z → Finset (PhysicalBond dPhys N)}
    {amplitude weight : OmegaPolymerType HF z → ℝ}
    {sourceConstruction : Prop}
    (T :
      PhysicalGaugeCMP116ActivityTransport
        (lieDim := lieDim) (Ψ := fun _ : Cube d L => β)
        HF z Λ precision covariance root covNormBound rootNormBound
        covWeight rootWeight physicalActivity physicalActiveSupport
        amplitude weight H0 κ sourceConstruction)
    (ν : Measure β) [IsProbabilityMeasure ν]
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    {K0 κ0 : ℝ}
    (hH0 : 0 ≤ H0)
    (hH0_one : H0 ≤ 1)
    (hK0 : 0 ≤ K0)
    (hsmall : 2 * H0 * K0 ≤ 1)
    (hκ0 : 0 ≤ κ0)
    (hκ : κ0 ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ0 X.val) ≤ K0) :
    ‖balabanCMP116AppendixFIntegratedKsharpActivity
        HF z Λ T.family ν Y‖ ≤
      (2 * H0 * K0) *
        appendixFHoleExpWeight HF (appendixFKsharpRate κ κ0) Y :=
  norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_rawMetricDecay_rooted_of_source
    HF z Λ T.family ν hY hH0 hH0_one hK0 hsmall hκ0 hκ hroot
    (balabanCMP116_hraw_of_physicalGaugeCMP116ActivityTransport T hH0)

/-- The spectator-integrated CMP116 activity vanishes away from the first
connected-cover target region. -/
theorem balabanCMP116AppendixFIntegratedKsharpActivity_eq_zero_of_not_mem_targetRegion
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β)
    (Y : Finset (Cube d L))
    (hY : Y ∉ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ) :
    balabanCMP116AppendixFIntegratedKsharpActivity HF z Λ F ν Y = 0 := by
  simpa [balabanCMP116AppendixFIntegratedKsharpActivity] using
    (appendixFHoleIntegratedKsharpActivity_eq_zero_of_not_mem_targetRegion
      HF z Λ F.activity (balabanCMP116BondGaussian lieDim) ν Y hY)

/-- The second hard-core gas formed from the spectator-integrated CMP116
`K#` activity. -/
noncomputable def balabanCMP116AppendixFIntegratedSecondGas
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β) :
    KP.PolymerSystem :=
  appendixFHoleIntegratedSecondGas HF z Λ F.activity
    (balabanCMP116BondGaussian lieDim) ν

noncomputable instance balabanCMP116AppendixFIntegratedSecondGas_fintype
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β) :
    Fintype (balabanCMP116AppendixFIntegratedSecondGas HF z Λ F ν).Polymer :=
  inferInstanceAs (Fintype
    (appendixFHoleIntegratedSecondGas HF z Λ F.activity
      (balabanCMP116BondGaussian lieDim) ν).Polymer)

@[simp] theorem balabanCMP116AppendixFIntegratedSecondGas_activity
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β)
    (Y : (balabanCMP116AppendixFIntegratedSecondGas HF z Λ F ν).Polymer) :
    (balabanCMP116AppendixFIntegratedSecondGas HF z Λ F ν).activity Y =
      balabanCMP116AppendixFIntegratedKsharpActivity HF z Λ F ν Y.val := by
  rfl

/-- KP-ready pointwise majorant for the spectator-integrated scalar CMP116
second gas. -/
def BalabanCMP116AppendixFIntegratedSecondGasKPMajorant
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β)
    (t q A : ℝ) : Prop :=
  AppendixFHoleIntegratedSecondGasKPMajorant HF z Λ F.activity
    (balabanCMP116BondGaussian lieDim) ν t q A

/-- CMP116 wrapper for the with-holes KP criterion of the spectator-integrated
scalar second gas. -/
theorem balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_majorant
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β)
    (t q A : ℝ)
    (hA0 : 0 ≤ A)
    (hK : BalabanCMP116AppendixFIntegratedSecondGasKPMajorant
      HF z Λ F ν t q A)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hq0 : 0 ≤ q)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (q * 2 ^ (3 ^ d + 1)) < 1)
    (hsmall :
      A * (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (q * 2 ^ (3 ^ d + 1)))⁻¹ ≤ 1) :
    KP.KPCriterion
      ((balabanCMP116AppendixFIntegratedSecondGas HF z Λ F ν).scaleActivity
        (Real.exp t))
      (fun Y => (Y.val.card : ℝ)) := by
  simpa [balabanCMP116AppendixFIntegratedSecondGas,
    BalabanCMP116AppendixFIntegratedSecondGasKPMajorant] using
    (appendixFHoleIntegratedSecondGas_KPCriterion_of_majorant
      HF z Λ F.activity (balabanCMP116BondGaussian lieDim) ν
      t q A hA0 hK hdisj hnoedges hholes_ne hq0 hCq hsmall)

/-- Source-package route from rooted raw-metric decay to the KP-ready majorant
for the spectator-integrated scalar CMP116 second gas.

The only remaining quantitative input is the explicit scalar profile
`hprofile`: it absorbs the KP tilt `exp t`, the full target-cardinality factor,
and the conversion from the first-gas rate to the chosen `A,q` metric profile.
-/
theorem
    BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β) [IsProbabilityMeasure ν]
    {H₀ K₀ κ κ₀ t q A : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hsmall : 2 * H₀ * K₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ ψ φ X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hprofile :
      ∀ Y : (balabanCMP116AppendixFIntegratedSecondGas HF z Λ F ν).Polymer,
        Real.exp t *
            ((2 * H₀ * K₀) *
              appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y.val) *
            Real.exp (Y.val.card : ℝ)
          ≤ A * q ^ (discreteModifiedMetric HF Y.val + 1)) :
    BalabanCMP116AppendixFIntegratedSecondGasKPMajorant
      HF z Λ F ν t q A := by
  refine
    appendixFHoleIntegratedSecondGasKPMajorant_of_norm_bound
      HF z Λ F.activity (balabanCMP116BondGaussian lieDim) ν
      t q A
      (fun Y =>
        (2 * H₀ * K₀) *
          appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y.val)
      ?_ hprofile
  intro Y
  by_cases hY : Y.val ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ
  · simpa [balabanCMP116AppendixFIntegratedSecondGas_activity] using
      (norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_rawMetricDecay_rooted_of_source
        HF z Λ F ν hY hH₀ hH₀_one hK₀ hsmall hκ₀ hκ hroot hraw)
  · have hzero :=
      balabanCMP116AppendixFIntegratedKsharpActivity_eq_zero_of_not_mem_targetRegion
        HF z Λ F ν Y.val hY
    have hactivity_zero :
        (balabanCMP116AppendixFIntegratedSecondGas HF z Λ F ν).activity Y = 0 := by
      simpa [balabanCMP116AppendixFIntegratedSecondGas_activity] using hzero
    have hB_nonneg :
        0 ≤ (2 * H₀ * K₀) *
          appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y.val := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg zero_le_two hH₀) hK₀)
        (appendixFHoleExpWeight_nonneg HF (appendixFKsharpRate κ κ₀) Y.val)
    change
      ‖(balabanCMP116AppendixFIntegratedSecondGas HF z Λ F ν).activity Y‖ ≤
        (2 * H₀ * K₀) *
          appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y.val
    rw [hactivity_zero]
    simpa using hB_nonneg

/-- Source-package route to the spectator-integrated scalar CMP116 second-gas
majorant when the remaining scalar profile is supplied by a full-cardinality
budget against the shifted modified metric.

The hypothesis `hcard` is intentionally explicit: Appendix-F geometry controls
the active skeleton by `d_M+1`, but the KP tilt here contains the full target
cardinality.  Any source theorem that thickens skeletons through holes must
instantiate this budget. -/
theorem
    BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source_of_card_le_metric
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β) [IsProbabilityMeasure ν]
    {H₀ K₀ κ κ₀ t q A θ : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hsmall : 2 * H₀ * K₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ ψ φ X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hA : Real.exp t * (2 * H₀ * K₀) ≤ A)
    (hq : q = Real.exp (-(appendixFKsharpRate κ κ₀ - θ)))
    (hcard :
      ∀ Y : (balabanCMP116AppendixFIntegratedSecondGas HF z Λ F ν).Polymer,
        (Y.val.card : ℝ) ≤ θ *
          (((discreteModifiedMetric HF Y.val + 1 : ℕ) : ℝ))) :
    BalabanCMP116AppendixFIntegratedSecondGasKPMajorant
      HF z Λ F ν t q A := by
  refine
    BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source
      HF z Λ F ν hH₀ hH₀_one hK₀ hsmall hκ₀ hκ hroot hraw ?_
  intro Y
  exact
    appendixFHoleExpWeight_tilted_profile_le_of_card_le_metric
      HF (appendixFKsharpRate κ κ₀) θ t (2 * H₀ * K₀) A q Y.val
      (mul_nonneg (mul_nonneg zero_le_two hH₀) hK₀) hA hq (hcard Y)

/-- Full KP-criterion consumer obtained from rooted raw-metric CMP116 decay
once the full-cardinality tilt is controlled by the shifted modified metric.

This theorem is still conditional on the source-side cardinality budget and KP
smallness constants.  Its purpose is to keep the remaining scalar profile
obligation visible while avoiding repeated proof assembly at later call sites. -/
theorem
    balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_rawMetricDecay_rooted_of_source_of_card_le_metric
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β) [IsProbabilityMeasure ν]
    {H₀ K₀ κ κ₀ t q A θ : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hsourceSmall : 2 * H₀ * K₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ ψ φ X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hA0 : 0 ≤ A)
    (hA : Real.exp t * (2 * H₀ * K₀) ≤ A)
    (hq : q = Real.exp (-(appendixFKsharpRate κ κ₀ - θ)))
    (hcard :
      ∀ Y : (balabanCMP116AppendixFIntegratedSecondGas HF z Λ F ν).Polymer,
        (Y.val.card : ℝ) ≤ θ *
          (((discreteModifiedMetric HF Y.val + 1 : ℕ) : ℝ)))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (q * 2 ^ (3 ^ d + 1)) < 1)
    (hkpSmall :
      A * (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (q * 2 ^ (3 ^ d + 1)))⁻¹ ≤ 1) :
    KP.KPCriterion
      ((balabanCMP116AppendixFIntegratedSecondGas HF z Λ F ν).scaleActivity
        (Real.exp t))
      (fun Y => (Y.val.card : ℝ)) := by
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact Real.exp_nonneg _
  exact
    balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_majorant
      HF z Λ F ν t q A hA0
      (BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source_of_card_le_metric
        HF z Λ F ν hH₀ hH₀_one hK₀ hsourceSmall hκ₀ hκ hroot hraw
        hA hq hcard)
      hdisj hnoedges hholes_ne hq0 hCq hkpSmall

/-- Finite target-family spectator integration, specialized to the CMP116
`K#` adapter and rewritten in terms of the CMP116 scalar `z_K` activity. -/
theorem integral_sum_balabanCMP116AppendixFKsharp_eq_sum_prod_integratedKsharpActivity
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β] [Nonempty β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF z))
    (ν : Measure β) [IsProbabilityMeasure ν]
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F)
    (hint : ∀ targets,
      targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ →
        Integrable
          (fun ψ : (∀ _ : Cube d L, β) =>
            ∏ Y ∈ targets,
              (balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ)
          (Measure.pi fun _ : Cube d L => ν)) :
    ∫ ψ : (∀ _ : Cube d L, β),
        (∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
          ∏ Y ∈ targets,
            (balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ)
        ∂(Measure.pi fun _ : Cube d L => ν)
      =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets,
          balabanCMP116AppendixFIntegratedKsharpActivity HF z Λ F ν Y := by
  simpa [balabanCMP116AppendixFKsharp,
    balabanCMP116AppendixFIntegratedKsharpActivity] using
    (integral_sum_appendixFHoleKsharp_eq_sum_prod_integratedKsharpActivity_of_admissibleTargetFamilies
      HF z Λ F.activity (balabanCMP116BondGaussian lieDim) ν
      h.spectatorSupport_subset_skeleton
      (by
        intro targets htargets
        simpa [balabanCMP116AppendixFKsharp] using hint targets htargets))

end YangMills.RG
