/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116HsharpAdapter
import YangMills.RG.AppendixFHsharpProfile
import YangMills.RG.AppendixFSecondUrsellWeightedTree

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

/-- Direct constructor for a CMP116 geometric `H#` profile from a termwise
bound on the finite fixed-union second-Ursell terms.  This is the exact profile
shape consumed by the tail, residual, and UV theorems below. -/
noncomputable def
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_term_geometric
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
    (hterm :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        ‖appendixFHoleHsharpTerm HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k) P.val n‖ ≤
          A t k P * q t k P ^ n)
    (hclosed :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        A t k P * (1 - q t k P)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    BalabanCMP116AppendixFHsharpGeometricMajorantProfile
      HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀ where
  A := A
  q := q
  A_nonneg := hA
  q_nonneg := hq0
  q_lt_one := hq1
  term_bound := hterm
  closed_total_le_residual := hclosed

/-- Build the CMP116 geometric profile from a bound on the finite absolute
fixed-union term.  The only formal step here is the already-proved triangle
inequality
`‖appendixFHoleHsharpTerm‖ ≤ appendixFHoleHsharpAbsTerm`. -/
noncomputable def
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_absTerm_geometric
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
    BalabanCMP116AppendixFHsharpGeometricMajorantProfile
      HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_term_geometric
    HF zCarrier z Λ F ν g A q hA hq0 hq1
    (fun t k P n =>
      (norm_appendixFHoleHsharpTerm_le_absTerm
        HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k) P.val n).trans
        (habs t k P n))
    hclosed

/-- Build the CMP116 geometric profile from a finite Penrose tree-term bound.
This is the preferred source-extraction target when the analytic theorem gives
tree/leaf estimates rather than the exact absolute fixed-union term. -/
noncomputable def
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_treeTerm_geometric
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
    BalabanCMP116AppendixFHsharpGeometricMajorantProfile
      HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_absTerm_geometric
    HF zCarrier z Λ F ν g A q hA hq0 hq1
    (fun t k P n =>
      (appendixFHoleHsharpAbsTerm_le_treeTerm
        HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k) P.val n).trans
        (htree t k P n))
    hclosed

/-- Repackage the older CMP116 `AppendixFHsharpSourceMajorant` interface as
the newer geometric profile consumed by the closed tail/residual/UV theorems
below.  This keeps the two source-facing endpoints synchronized: anything
already proved in the source-majorant form can immediately feed the profile
consumer stack. -/
noncomputable def
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_source_majorant
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
        g C H₀ c₀ κ κ₀) :
    BalabanCMP116AppendixFHsharpGeometricMajorantProfile
      HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀ where
  A := hsrc.A
  q := hsrc.q
  A_nonneg := hsrc.A_nonneg
  q_nonneg := hsrc.q_nonneg
  q_lt_one := hsrc.q_lt_one
  term_bound := hsrc.term_le
  closed_total_le_residual := hsrc.closed_le_residual

/-- Factorized absolute-term constructor for the CMP116 geometric profile.
The source supplies only a scale amplitude `B t k`, a cluster-order ratio
`ρ t k`, and the explicit modified-metric exponential. -/
noncomputable def
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_factorized_absTerm_geometric
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
    BalabanCMP116AppendixFHsharpGeometricMajorantProfile
      HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_source_majorant
    HF zCarrier z Λ F ν g
    (balabanCMP116AppendixFHsharpSourceMajorant_of_factorized_absTerm_geometric
      HF zCarrier z Λ F ν g B ρ hB0 hρ0 hρ1 habs hBclosed)

/-- Factorized finite-tree constructor for the CMP116 geometric profile.  This
is the source-normal form expected from a finite Penrose/tree estimate before
the analytic leaf summation is supplied. -/
noncomputable def
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_factorized_treeTerm_geometric
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
    BalabanCMP116AppendixFHsharpGeometricMajorantProfile
      HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_source_majorant
    HF zCarrier z Λ F ν g
    (balabanCMP116AppendixFHsharpSourceMajorant_of_factorized_treeTerm_geometric
      HF zCarrier z Λ F ν g B ρ hB0 hρ0 hρ1 htree hBclosed)

/-- Weighted-tree constructor for the CMP116 geometric profile.  The source
may now prove the purely weighted leaf estimate and the first-activity bound
separately; the verified finite algebra below turns them into the factorized
tree estimate consumed by the existing profile machinery. -/
noncomputable def
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_weighted_tree_geometric
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
    (w : ∀ t k,
      OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k) → ℝ)
    (epsilon Croot Cleaf : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hCroot0 : ∀ t k, 0 ≤ Croot t k)
    (hCleaf0 : ∀ t k, 0 ≤ Cleaf t k)
    (hρ1 : ∀ t k, Cleaf t k * epsilon t k < 1)
    (hw :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)), 0 ≤ w t k Q)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤ epsilon t k * w t k Q)
    (hleaf :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpWeightedTreeTerm HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k) (w t k) P.val n ≤
          Croot t k *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) *
            Cleaf t k ^ n)
    (hBclosed :
      ∀ t k,
        (Croot t k * epsilon t k) *
            (1 - Cleaf t k * epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    BalabanCMP116AppendixFHsharpGeometricMajorantProfile
      HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_factorized_treeTerm_geometric
    HF zCarrier z Λ F ν g
    (fun t k => Croot t k * epsilon t k)
    (fun t k => Cleaf t k * epsilon t k)
    (fun t k => mul_nonneg (hCroot0 t k) (hε t k))
    (fun t k => mul_nonneg (hCleaf0 t k) (hε t k))
    hρ1
    (fun t k P n =>
      appendixFHoleHsharpTreeTerm_le_factorized_of_weighted_bound
        HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)
        (w t k) P.val n (epsilon t k) (Croot t k) (Cleaf t k)
        (Real.exp
          (-(polymerClusterResidualRate κ κ₀ *
            ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))))
        (hε t k) (hw t k) (hactivity t k) (hleaf t k P n))
    hBclosed

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

/-- Source-normal `cluster3` constructor from a factorized finite tree-term
estimate.  This is the shortest closed CMP116 path from the preferred source
shape

`treeTerm ≤ (B t k * exp (-residualRate * (d_M(P)+1))) * ρ(t,k)^n`

to the `AppendixFHsharpCluster3Contract` consumers.  The analytic estimate and
the four semantic source obligations remain explicit hypotheses. -/
noncomputable def
    balabanCMP116AppendixFHsharpCluster3Contract_of_factorized_treeTerm_geometric
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
    (hinput : Prop) (hinput_holds : hinput)
    (hultralocal : Prop) (hultralocal_holds : hultralocal)
    (hlocal : Prop) (hlocal_holds : hlocal)
    (hinfluence : Prop) (hinfluence_holds : hinfluence)
    (hmargin : 3 * κ₀ + 3 ≤ κ)
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
    AppendixFHsharpCluster3Contract HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpCluster3Contract_of_profile
    HF zCarrier z Λ F ν g
    hinput hinput_holds hultralocal hultralocal_holds
    hlocal hlocal_holds hinfluence hinfluence_holds hmargin
    (balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_factorized_treeTerm_geometric
      HF zCarrier z Λ F ν g B ρ hB0 hρ0 hρ1 htree hBclosed)

/-- Source-normal `cluster3` constructor from the weighted finite tree
estimate plus a pointwise first-activity extraction.  The analytic leaf bound,
smallness, and semantic source obligations remain explicit hypotheses. -/
noncomputable def
    balabanCMP116AppendixFHsharpCluster3Contract_of_weighted_tree_geometric
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
    (w : ∀ t k,
      OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k) → ℝ)
    (epsilon Croot Cleaf : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hinput : Prop) (hinput_holds : hinput)
    (hultralocal : Prop) (hultralocal_holds : hultralocal)
    (hlocal : Prop) (hlocal_holds : hlocal)
    (hinfluence : Prop) (hinfluence_holds : hinfluence)
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hCroot0 : ∀ t k, 0 ≤ Croot t k)
    (hCleaf0 : ∀ t k, 0 ≤ Cleaf t k)
    (hρ1 : ∀ t k, Cleaf t k * epsilon t k < 1)
    (hw :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)), 0 ≤ w t k Q)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤ epsilon t k * w t k Q)
    (hleaf :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpWeightedTreeTerm HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k) (w t k) P.val n ≤
          Croot t k *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) *
            Cleaf t k ^ n)
    (hBclosed :
      ∀ t k,
        (Croot t k * epsilon t k) *
            (1 - Cleaf t k * epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    AppendixFHsharpCluster3Contract HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpCluster3Contract_of_profile
    HF zCarrier z Λ F ν g
    hinput hinput_holds hultralocal hultralocal_holds
    hlocal hlocal_holds hinfluence hinfluence_holds hmargin
    (balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_weighted_tree_geometric
      HF zCarrier z Λ F ν g w epsilon Croot Cleaf
      hε hCroot0 hCleaf0 hρ1 hw hactivity hleaf hBclosed)

/-- Real-part rooted absolute summability for the CMP116 integrated `H#`
object, fed directly by a packaged CMP116 geometric profile. -/
theorem
    summable_abs_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_profile
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
    (hC : 0 ≤ C)
    (hH₀ : 0 ≤ H₀)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (profile :
      BalabanCMP116AppendixFHsharpGeometricMajorantProfile
        HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀) :
    ∀ t k,
      Summable
        (fun P : { P : OmegaPolymerType HF zCarrier //
            r ∈ skeleton HF P.val } =>
          |Complex.re
            (balabanCMP116AppendixFHsharpOfIntegratedKsharp
              HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val)|) := by
  intro t k
  change
    Summable
      (fun P : { P : OmegaPolymerType HF zCarrier //
          r ∈ skeleton HF P.val } =>
        |Complex.re
          (appendixFHoleHsharp HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k) P.val.val)|)
  exact
    AppendixFHsharpGeometricMajorantProfile.summable_abs_re_of_profile
      HF zCarrier r
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g hC hH₀ hg hκ profile t k

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

/-- Real-part omega-rooted UV decay fed directly by the source-normal
factorized finite tree-term estimate.  This combines the factorized-tree
profile constructor with the profile UV consumer; all positivity, four-margin,
holes-geometry, and source tree estimates remain explicit hypotheses. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_factorized_treeTerm_geometric
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
    (B ρ : ℕ → ℕ → ℝ)
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
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀)
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
  singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_profile
    HF zCarrier r z Λ F ν Rsc g
    hC hH₀ hg hκ hR
    (balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_factorized_treeTerm_geometric
      HF zCarrier z Λ F ν g B ρ hB0 hρ0 hρ1 htree hBclosed)
    hdisj hnoedges hholes_ne hCq

/-- Real-part omega-rooted UV decay fed directly by the weighted finite tree
estimate plus pointwise first-activity extraction.  This is the source-facing
endpoint for the weighted tree theorem: Lean performs only finite algebra and
then reuses the existing geometric-profile UV consumer. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_weighted_tree_geometric
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
    (w : ∀ t k,
      OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k) → ℝ)
    (epsilon Croot Cleaf : ℕ → ℕ → ℝ)
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
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hCroot0 : ∀ t k, 0 ≤ Croot t k)
    (hCleaf0 : ∀ t k, 0 ≤ Cleaf t k)
    (hρ1 : ∀ t k, Cleaf t k * epsilon t k < 1)
    (hw :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)), 0 ≤ w t k Q)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤ epsilon t k * w t k Q)
    (hleaf :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpWeightedTreeTerm HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k) (w t k) P.val n ≤
          Croot t k *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) *
            Cleaf t k ^ n)
    (hBclosed :
      ∀ t k,
        (Croot t k * epsilon t k) *
            (1 - Cleaf t k * epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀)
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
  singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_profile
    HF zCarrier r z Λ F ν Rsc g
    hC hH₀ hg hκ hR
    (balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_weighted_tree_geometric
      HF zCarrier z Λ F ν g w epsilon Croot Cleaf
      hε hCroot0 hCleaf0 hρ1 hw hactivity hleaf hBclosed)
    hdisj hnoedges hholes_ne hCq

end YangMills.RG
