/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116HsharpAdapter
import YangMills.RG.AppendixFHsharpProfile

/-!
# Source-facing CMP116 contracts for Appendix-F `H#`

`BalabanCMP116HsharpAdapter` specializes the verified `H#` consumers to the
CMP116 integrated first activity.  This file turns the remaining source-facing
obligations around: it lets an external Balaban/Dimock theorem state its bound
directly on the named CMP116 object
`balabanCMP116AppendixFHsharpOfIntegratedKsharp`, then packages that theorem
into the generic Appendix-F contracts.

No `cluster3`, leaf-summation, raw-activity decay, or spectator-measure theorem
is proved here.  The point is to expose their exact Lean target shape without
asking a source extractor to rewrite through the generic `zK` family by hand.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open MeasureTheory

/-! ## CMP116 source residuals as `cluster3` contracts -/

/-- Package a source theorem stated directly for the CMP116 integrated `H#`
activity into the generic `AppendixFHsharpCluster3Contract`.

The four proposition arguments are deliberately opaque source obligations:
they should later be instantiated by the precise CMP116/CMP119/CMP122
locality, independence, decay, and influence theorems. -/
noncomputable def
    balabanCMP116AppendixFHsharpCluster3Contract_of_residual_bound
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
    (hinput : Prop) (hinput_holds : hinput)
    (hultralocal : Prop) (hultralocal_holds : hultralocal)
    (hlocal : Prop) (hlocal_holds : hlocal)
    (hinfluence : Prop) (hinfluence_holds : hinfluence)
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hres :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖balabanCMP116AppendixFHsharpOfIntegratedKsharp
            HF (z t k) (Λ t k) (F t k) (ν t k) P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    AppendixFHsharpCluster3Contract HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C H₀ c₀ κ κ₀ where
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
    change
      ‖balabanCMP116AppendixFHsharpOfIntegratedKsharp
          HF (z t k) (Λ t k) (F t k) (ν t k) P.val‖ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))
    exact hres t k P

/-- Same constructor as
`balabanCMP116AppendixFHsharpCluster3Contract_of_residual_bound`, but for
source theorems stated with the unshifted metric `exp (-r d_M(P))`.  The
generic contract's shifted normalization is recovered by paying
`exp r`, where `r = κ - 3κ₀ - 3`. -/
noncomputable def
    balabanCMP116AppendixFHsharpCluster3Contract_of_unshifted_residual_bound
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
    (hinput : Prop) (hinput_holds : hinput)
    (hultralocal : Prop) (hultralocal_holds : hultralocal)
    (hlocal : Prop) (hlocal_holds : hlocal)
    (hinfluence : Prop) (hinfluence_holds : hinfluence)
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hres :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        ‖balabanCMP116AppendixFHsharpOfIntegratedKsharp
            HF (z t k) (Λ t k) (F t k) (ν t k) P.val‖ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                (discreteModifiedMetric HF P.val : ℝ)))) :
    AppendixFHsharpCluster3Contract HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g (C * Real.exp (polymerClusterResidualRate κ κ₀)) H₀ c₀ κ κ₀ := by
  refine
    AppendixFHsharpCluster3Contract.of_unshifted_residual_bound
      (HF := HF) (zCarrier := zCarrier)
      (zK := fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      (g := g) (C := C) (H₀ := H₀) (c₀ := c₀)
      (κ := κ) (κ₀ := κ₀)
      hinput hinput_holds hultralocal hultralocal_holds
      hlocal hlocal_holds hinfluence hinfluence_holds hmargin ?_
  intro t k P
  change
    ‖balabanCMP116AppendixFHsharpOfIntegratedKsharp
        HF (z t k) (Λ t k) (F t k) (ν t k) P.val‖ ≤
      C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
        Real.exp
          (-(polymerClusterResidualRate κ κ₀ *
            (discreteModifiedMetric HF P.val : ℝ)))
  exact hres t k P

/-! ## CMP116 source profiles -/

/-- The generic geometric `H#` profile specialized to the CMP116 integrated
first activity.  A source proof may construct this profile from finite
second-Ursell tree/absolute estimates, then immediately consume the verified
tail, residual, and UV theorems below. -/
abbrev BalabanCMP116AppendixFHsharpGeometricMajorantProfile
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
    (C H₀ c₀ κ κ₀ : ℝ) :=
  AppendixFHsharpGeometricMajorantProfile HF zCarrier
    (fun t k Y =>
      balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t k Y)
    g C H₀ c₀ κ κ₀

/-- A CMP116 geometric profile supplies the pointwise residual estimate for the
named CMP116 integrated `H#` activity. -/
theorem
    norm_balabanCMP116AppendixFHsharpOfIntegratedKsharp_le_residual_of_profile
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
    (profile :
      BalabanCMP116AppendixFHsharpGeometricMajorantProfile
        HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀)
    (t k : ℕ)
    (P : OmegaPolymerType HF zCarrier) :
    ‖balabanCMP116AppendixFHsharpOfIntegratedKsharp
        HF (z t k) (Λ t k) (F t k) (ν t k) P.val‖ ≤
      C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
        Real.exp
          (-(polymerClusterResidualRate κ κ₀ *
            ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  change
    ‖appendixFHoleHsharp HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k) P.val‖ ≤
      C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
        Real.exp
          (-(polymerClusterResidualRate κ κ₀ *
            ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))
  exact
    AppendixFHsharpGeometricMajorantProfile.residual_bound
      (HF := HF) (zCarrier := zCarrier)
      (zK := fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      (g := g) (C := C) (H₀ := H₀) (c₀ := c₀)
      (κ := κ) (κ₀ := κ₀) profile t k P

/-- A CMP116 geometric profile can be repackaged as a `cluster3` contract when
the source also supplies the four semantic obligations and the cluster3 margin.
This is a convenience bridge for consumers that standardize on the closed
`AppendixFHsharpCluster3Contract` interface. -/
noncomputable def
    balabanCMP116AppendixFHsharpCluster3Contract_of_profile
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
    (hinput : Prop) (hinput_holds : hinput)
    (hultralocal : Prop) (hultralocal_holds : hultralocal)
    (hlocal : Prop) (hlocal_holds : hlocal)
    (hinfluence : Prop) (hinfluence_holds : hinfluence)
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (profile :
      BalabanCMP116AppendixFHsharpGeometricMajorantProfile
        HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀) :
    AppendixFHsharpCluster3Contract HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpCluster3Contract_of_residual_bound
    HF zCarrier z Λ F ν g
    hinput hinput_holds hultralocal hultralocal_holds
    hlocal hlocal_holds hinfluence hinfluence_holds hmargin
    (fun t k P =>
      norm_balabanCMP116AppendixFHsharpOfIntegratedKsharp_le_residual_of_profile
        HF zCarrier z Λ F ν g profile t k P)

/-- Real-part omega-rooted UV decay for the CMP116 integrated `H#` object,
fed directly by a packaged CMP116 geometric profile. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_profile
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
    (profile :
      BalabanCMP116AppendixFHsharpGeometricMajorantProfile
        HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀)
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
    AppendixFHsharpGeometricMajorantProfile.singleScaleUVDecay_of_profile
      HF zCarrier r
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      Rsc g hC hH₀ hg hκ ?_ profile
      hdisj hnoedges hholes_ne hCq
  intro t k
  change
    Rsc t k =
      ∑' P : { P : OmegaPolymerType HF zCarrier //
          r ∈ skeleton HF P.val },
        Complex.re
          (appendixFHoleHsharp HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k) P.val.val)
  exact hR t k

end YangMills.RG
