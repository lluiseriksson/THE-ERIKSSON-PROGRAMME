/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Localization
import YangMills.RG.AppendixFKsharpEstimate

/-!
# Balaban CMP116 to Appendix-F `K#`

This module specializes the first Appendix-F connected-activity compiler to the
CMP116 localized activity package.  The product fluctuation measure is the
source-shaped `dmu0`; the only remaining support input is the promised
localization theorem saying that each Balaban active support is contained in
the full Appendix-F polymer, and, for the skeleton consumers, in its active
hole skeleton.

No estimate from Balaban's random-walk expansion is proved here.  The raw
pointwise decay, integrability, and support localization statements remain
explicit hypotheses.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators

/-- The source-localization obligations needed to feed a CMP116 localized
family into the source-facing Appendix-F hole compiler.

`activeSupport_subset_full` is the full-support statement needed for target
union bookkeeping.  `activeSupport_subset_skeleton` is the stronger active
statement consumed by the hard-core/factorization layer.  Both are kept
explicit because they are source theorems about Balaban's localized square-root
covariance expansion, not finite combinatorics. -/
structure BalabanCMP116AppendixFSupportHypotheses
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z)) : Prop where
  activeSupport_subset_full :
    ∀ X, X ∈ Λ → F.activeSupport X ⊆ X.val
  activeSupport_subset_skeleton :
    ∀ X, X ∈ Λ → F.activeSupport X ⊆ skeleton HF X.val

namespace BalabanCMP116AppendixFSupportHypotheses

variable {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
variable {HF : HoleFamily d L} {z : Finset (Cube d L) → ℂ}
variable {Λ : Finset (OmegaPolymerType HF z)}
variable {F :
  BalabanCMP116LocalizedActivityFamily
    (Cube d L) lieDim Ψ (OmegaPolymerType HF z)}

/-- CMP116 spectator locality, converted to the full Appendix-F target support. -/
theorem spectatorSupport_subset_full
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    ∀ X, X ∈ Λ → (F.activity X).spectatorSupport ⊆ X.val := by
  intro X hX x hx
  exact h.activeSupport_subset_full X hX (F.spectatorSupport_subset X hx)

/-- CMP116 fluctuation locality, converted to the full Appendix-F target
support. -/
theorem fluctuationSupport_subset_full
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    ∀ X, X ∈ Λ → (F.activity X).fluctuationSupport ⊆ X.val := by
  intro X hX x hx
  exact h.activeSupport_subset_full X hX
    ((Finset.mem_inter.mp (F.fluctuationSupport_subset X hx)).2)

/-- CMP116 spectator locality, converted to the Appendix-F active skeleton. -/
theorem spectatorSupport_subset_skeleton
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    ∀ X, X ∈ Λ → (F.activity X).spectatorSupport ⊆ skeleton HF X.val := by
  intro X hX x hx
  exact h.activeSupport_subset_skeleton X hX (F.spectatorSupport_subset X hx)

/-- CMP116 fluctuation locality, converted to the Appendix-F active skeleton. -/
theorem fluctuationSupport_subset_skeleton
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    ∀ X, X ∈ Λ → (F.activity X).fluctuationSupport ⊆ skeleton HF X.val := by
  intro X hX x hx
  exact h.activeSupport_subset_skeleton X hX
    ((Finset.mem_inter.mp (F.fluctuationSupport_subset X hx)).2)

end BalabanCMP116AppendixFSupportHypotheses

/-- The CMP116-specialized first connected Appendix-F local activity. -/
noncomputable def balabanCMP116AppendixFConnectedLocalActivity
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L)) :
    LocalActivity (Cube d L) Ψ (fun _ => Fin lieDim -> Real) ℂ :=
  appendixFHoleConnectedLocalActivity HF z Λ F.activity Y

/-- The CMP116-specialized first integrated activity `K#`, using the
source-shaped product fluctuation measure `dmu0`. -/
noncomputable def balabanCMP116AppendixFKsharp
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L)) :
    LocalFunctional (Cube d L) Ψ ℂ :=
  appendixFHoleKsharp HF z Λ F.activity (balabanCMP116BondGaussian lieDim) Y

@[simp] theorem balabanCMP116AppendixFConnectedLocalActivity_globalEval
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x)
    (φ : ∀ _ : Cube d L, Fin lieDim -> Real) :
    (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).globalEval ψ φ =
      appendixFHoleConnectedMayerActivity HF z Λ
        (fun X => Complex.exp ((F.activity X).globalEval ψ φ) - 1) Y := by
  simp [balabanCMP116AppendixFConnectedLocalActivity]

@[simp] theorem balabanCMP116AppendixFKsharp_globalEval
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x) :
    (balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ =
      ∫ φ : (∀ _ : Cube d L, Fin lieDim -> Real),
        (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).globalEval ψ φ
        ∂(balabanCMP116Dmu0 (Cube d L) lieDim) := by
  rfl

/-- Direct raw-Mayer integral form of the CMP116-specialized `K#`. -/
theorem balabanCMP116AppendixFKsharp_globalEval_eq_integral_connectedMayerActivity
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x) :
    (balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ =
      ∫ φ : (∀ _ : Cube d L, Fin lieDim -> Real),
        appendixFHoleConnectedMayerActivity HF z Λ
          (fun X => Complex.exp ((F.activity X).globalEval ψ φ) - 1) Y
        ∂(balabanCMP116Dmu0 (Cube d L) lieDim) := by
  rw [balabanCMP116AppendixFKsharp, balabanCMP116Dmu0]
  exact appendixFHoleKsharp_globalEval_eq_integral_connectedMayerActivity
    HF z Λ F.activity (balabanCMP116BondGaussian lieDim) Y ψ

/-- Full-support locality for the CMP116-specialized connected activity. -/
theorem balabanCMP116AppendixFConnectedLocalActivity_spectatorSupport_subset
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).spectatorSupport ⊆ Y := by
  exact appendixFHoleConnectedLocalActivity_spectatorSupport_subset
    HF z Λ F.activity Y h.spectatorSupport_subset_full

/-- Full-support fluctuation locality for the CMP116-specialized connected
activity. -/
theorem balabanCMP116AppendixFConnectedLocalActivity_fluctuationSupport_subset
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).fluctuationSupport ⊆ Y := by
  exact appendixFHoleConnectedLocalActivity_fluctuationSupport_subset
    HF z Λ F.activity Y h.fluctuationSupport_subset_full

/-- Active-skeleton spectator locality for the CMP116-specialized connected
activity. -/
theorem balabanCMP116AppendixFConnectedLocalActivity_spectatorSupport_subset_skeleton
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).spectatorSupport ⊆
      skeleton HF Y := by
  exact appendixFHoleConnectedLocalActivity_spectatorSupport_subset_skeleton
    HF z Λ F.activity Y h.spectatorSupport_subset_skeleton

/-- Active-skeleton fluctuation locality for the CMP116-specialized connected
activity. -/
theorem balabanCMP116AppendixFConnectedLocalActivity_fluctuationSupport_subset_skeleton
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).fluctuationSupport ⊆
      skeleton HF Y := by
  exact appendixFHoleConnectedLocalActivity_fluctuationSupport_subset_skeleton
    HF z Λ F.activity Y h.fluctuationSupport_subset_skeleton

/-- Full-target support for the CMP116-specialized `K#`. -/
theorem balabanCMP116AppendixFKsharp_support_subset
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    (balabanCMP116AppendixFKsharp HF z Λ F Y).support ⊆ Y := by
  exact appendixFHoleKsharp_support_subset
    HF z Λ F.activity (balabanCMP116BondGaussian lieDim) Y
    h.spectatorSupport_subset_full

/-- Active-skeleton support for the CMP116-specialized `K#`. -/
theorem balabanCMP116AppendixFKsharp_support_subset_skeleton
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    (balabanCMP116AppendixFKsharp HF z Λ F Y).support ⊆ skeleton HF Y := by
  exact appendixFHoleKsharp_support_subset_skeleton
    HF z Λ F.activity (balabanCMP116BondGaussian lieDim) Y
    h.spectatorSupport_subset_skeleton

/-- The finite target-family first-integration identity, specialized to the
CMP116 product Gaussian. -/
theorem integral_sum_balabanCMP116AppendixFConnectedLocalActivity_eq_sum_prod_Ksharp
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (ψ : ∀ x, Ψ x)
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F)
    (hint : ∀ targets,
      targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ →
        Integrable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            ∏ Y ∈ targets,
              (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim)) :
    ∫ φ : (∀ _ : Cube d L, Fin lieDim -> Real),
        (∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
          ∏ Y ∈ targets,
            (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).globalEval ψ φ)
        ∂(balabanCMP116Dmu0 (Cube d L) lieDim)
      =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets,
          (balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  simpa [balabanCMP116AppendixFConnectedLocalActivity,
    balabanCMP116AppendixFKsharp, balabanCMP116Dmu0] using
    (integral_sum_appendixFHoleConnectedLocalActivity_eq_sum_prod_Ksharp_of_local_fluctuationSupport_subset_skeleton
      HF z Λ F.activity (balabanCMP116BondGaussian lieDim) ψ
      h.fluctuationSupport_subset_skeleton
      (by
        intro targets htargets
        simpa [balabanCMP116AppendixFConnectedLocalActivity,
          balabanCMP116Dmu0] using hint targets htargets))

/-- Source-shaped rooted first-activity estimate, specialized to CMP116
`dmu0`.  The raw pointwise decay and integrability hypotheses are exactly the
analytic/source obligations still missing from the Yang-Mills RG input. -/
theorem norm_balabanCMP116AppendixFKsharp_globalEval_le_expSubOne_of_rawMetricDecay_rooted
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀) (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hκ₀ : 0 ≤ κ₀) (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hint : Integrable
      (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
        (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).globalEval ψ φ)
      (balabanCMP116Dmu0 (Cube d L) lieDim)) :
    ‖(balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ‖
      ≤
    appendixFHoleExpWeight HF (κ - κ₀) Y *
      (Real.exp
        (2 * H₀ * K₀ *
          (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ))) - 1) := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  simpa [balabanCMP116AppendixFKsharp] using
    (norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay_rooted
      HF z Λ F.activity (balabanCMP116BondGaussian lieDim) hY ψ
      hH₀ hH₀_one hK₀ hκ₀ hκ hroot hraw
      (by
        simpa [balabanCMP116AppendixFConnectedLocalActivity,
          balabanCMP116Dmu0] using hint))

end YangMills.RG
