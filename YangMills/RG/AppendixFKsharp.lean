/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHoleTargetFamily
import YangMills.RG.OmegaConnectedCover
import YangMills.RG.UltralocalFactorization

/-!
# Appendix F: the first integrated activity `K#`

This module turns the already-proved finite with-holes connected Mayer scalar
activity into a type-local activity and then integrates the fluctuation field.

The purpose is the finite Dimock Appendix-F bridge

```
K(Y, psi, phi)  ->  K#(Y, psi) = ∫ K(Y, psi, phi) dmu(phi)
```

with integrability kept explicit in norm statements.  This is the first
defined-object layer needed before the second polymer gas and the Ursell
activity `H#`.  The finite target-family product and sum-under-integral
factorizations are proved below.  The Dimock (642) activity estimate, the
second Ursell expansion, and any concrete Yang--Mills raw activity bound remain
separate analytic obligations.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators

/-- The type-local first connected Appendix-F activity for source-facing hole
targets.  It sums the local Mayer-cover products over the skeleton-connected
cover fiber whose full target union is `Y`. -/
noncomputable def appendixFHoleConnectedLocalActivity
    {d L : ℕ} [NeZero L] {β : Type*} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (Y : Finset (Cube d L)) :
    LocalActivity (Cube d L) Ψ (fun _ => β) ℂ :=
  LocalActivity.finsetSum
    (appendixFTargetFiber
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y)
    (fun C => LocalActivity.mayerCoverActivity C H)

@[simp] theorem appendixFHoleConnectedLocalActivity_globalEval
    {d L : ℕ} [NeZero L] {β : Type*} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x) (φ : ∀ _ : Cube d L, β) :
    (appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ =
      appendixFHoleConnectedMayerActivity HF z Λ
        (fun X => Complex.exp ((H X).globalEval ψ φ) - 1) Y := by
  rw [appendixFHoleConnectedLocalActivity, LocalActivity.globalEval_finsetSum]
  unfold appendixFHoleConnectedMayerActivity appendixFConnectedMayerActivity
  refine Finset.sum_congr rfl ?_
  intro C _hC
  simpa using
    (Finset.prod_attach C
      (fun X : OmegaPolymerType HF z =>
        Complex.exp ((H X).globalEval ψ φ) - 1))

/-- Structural measurability of the connected first Appendix-F activity from
factorwise measurability of the raw one-polymer activities.

This is not an analytic source estimate: it only says the finite
connected-cover compiler preserves ordinary strong measurability through
finite sums, finite products, and the scalar map `z ↦ exp z - 1`.  The
model-specific source proof still has to provide the factorwise measurability
of each localized raw activity. -/
theorem appendixFHoleConnectedLocalActivity_globalEval_stronglyMeasurable
    {d L : ℕ} [NeZero L]
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z →
      LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x)
    (hmeas : ∀ X, X ∈ Λ →
      StronglyMeasurable
        (fun φ : (∀ _ : Cube d L, β) =>
          (H X).globalEval ψ φ)) :
    StronglyMeasurable
      (fun φ : (∀ _ : Cube d L, β) =>
        (appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ) := by
  classical
  let fiber := appendixFTargetFiber
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y
  have hs : StronglyMeasurable
      (fun φ : (∀ _ : Cube d L, β) =>
        ∑ C ∈ fiber, (LocalActivity.mayerCoverActivity C H).globalEval ψ φ) := by
    refine Finset.stronglyMeasurable_fun_sum fiber ?_
    intro C hC
    have hCdata :
        C ∈ appendixFConnectedCoverRegion
          (Finset.univ : Finset (Cube d L))
          (fun X : OmegaPolymerType HF z => skeleton HF X.val) Λ ∧
        appendixFCoverUnion
          (fun X : OmegaPolymerType HF z => X.val) C = Y := by
      simpa [fiber] using
        (mem_appendixFTargetFiber_iff
          (Finset.univ : Finset (Cube d L))
          (fun X : OmegaPolymerType HF z => skeleton HF X.val)
          (fun X : OmegaPolymerType HF z => X.val)
          Λ Y C).mp hC
    have hCsubset : C ⊆ Λ :=
      ((mem_appendixFConnectedCoverRegion_iff
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)
        Λ C).mp hCdata.1).1
    have hprod : StronglyMeasurable
        (fun φ : (∀ _ : Cube d L, β) =>
          ∏ X ∈ C, (Complex.exp ((H X).globalEval ψ φ) - 1)) := by
      refine Finset.stronglyMeasurable_fun_prod
        (s := C)
        (f := fun X (φ : (∀ _ : Cube d L, β)) =>
          Complex.exp ((H X).globalEval ψ φ) - 1) ?_
      intro X hX
      exact (Complex.continuous_exp.comp_stronglyMeasurable
        (hmeas X (hCsubset hX))).sub stronglyMeasurable_const
    convert hprod using 1
    funext φ
    rw [globalEval_mayerCoverActivity_eq_finsetProd]
  simpa [appendixFHoleConnectedLocalActivity, LocalActivity.globalEval_finsetSum, fiber]
    using hs

/-- If every raw activity only depends on spectator fields inside its full
source polymer, then the connected first activity over target union `Y` only
depends on spectator fields inside `Y`. -/
theorem appendixFHoleConnectedLocalActivity_spectatorSupport_subset
    {d L : ℕ} [NeZero L] {β : Type*} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (Y : Finset (Cube d L))
    (hsub : ∀ X, X ∈ Λ → (H X).spectatorSupport ⊆ X.val) :
    (appendixFHoleConnectedLocalActivity HF z Λ H Y).spectatorSupport ⊆ Y := by
  classical
  intro x hx
  rw [appendixFHoleConnectedLocalActivity, LocalActivity.finsetSum] at hx
  rcases Finset.mem_biUnion.mp hx with ⟨C, hC, hxC⟩
  rw [LocalActivity.mayerCoverActivity_spectatorSupport] at hxC
  rcases Finset.mem_biUnion.mp hxC with ⟨X, hX, hxX⟩
  have hCdata :
      C ∈ appendixFConnectedCoverRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val) Λ ∧
      appendixFCoverUnion
        (fun X : OmegaPolymerType HF z => X.val) C = Y := by
    simpa using
      (mem_appendixFTargetFiber_iff
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)
        (fun X : OmegaPolymerType HF z => X.val)
        Λ Y C).mp hC
  have hCsubset : C ⊆ Λ :=
    ((mem_appendixFConnectedCoverRegion_iff
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      Λ C).mp hCdata.1).1
  have hxFull : x ∈ X.val := hsub X (hCsubset hX) hxX
  have hxUnion :
      x ∈ appendixFCoverUnion
        (fun X : OmegaPolymerType HF z => X.val) C :=
    Finset.mem_biUnion.mpr ⟨X, hX, hxFull⟩
  rwa [hCdata.2] at hxUnion

/-- If every raw activity only depends on fluctuation fields inside its full
source polymer, then the connected first activity over target union `Y` only
depends on fluctuation fields inside `Y`. -/
theorem appendixFHoleConnectedLocalActivity_fluctuationSupport_subset
    {d L : ℕ} [NeZero L] {β : Type*} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (Y : Finset (Cube d L))
    (hsub : ∀ X, X ∈ Λ → (H X).fluctuationSupport ⊆ X.val) :
    (appendixFHoleConnectedLocalActivity HF z Λ H Y).fluctuationSupport ⊆ Y := by
  classical
  intro x hx
  rw [appendixFHoleConnectedLocalActivity, LocalActivity.finsetSum] at hx
  rcases Finset.mem_biUnion.mp hx with ⟨C, hC, hxC⟩
  rw [LocalActivity.mayerCoverActivity_fluctuationSupport] at hxC
  rcases Finset.mem_biUnion.mp hxC with ⟨X, hX, hxX⟩
  have hCdata :
      C ∈ appendixFConnectedCoverRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val) Λ ∧
      appendixFCoverUnion
        (fun X : OmegaPolymerType HF z => X.val) C = Y := by
    simpa using
      (mem_appendixFTargetFiber_iff
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)
        (fun X : OmegaPolymerType HF z => X.val)
        Λ Y C).mp hC
  have hCsubset : C ⊆ Λ :=
    ((mem_appendixFConnectedCoverRegion_iff
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      Λ C).mp hCdata.1).1
  have hxFull : x ∈ X.val := hsub X (hCsubset hX) hxX
  have hxUnion :
      x ∈ appendixFCoverUnion
        (fun X : OmegaPolymerType HF z => X.val) C :=
    Finset.mem_biUnion.mpr ⟨X, hX, hxFull⟩
  rwa [hCdata.2] at hxUnion

/-- The connected target activity depends on fluctuation fields only in the
active skeleton of the declared target, provided each input local activity has
its fluctuation support inside the active skeleton of its source polymer.

The source-local hypothesis is necessary because `H` is an arbitrary
type-local activity family in this interface; without it an input activity
could depend on unrelated fluctuation sites. -/
theorem appendixFHoleConnectedLocalActivity_fluctuationSupport_subset_skeleton
    {d L : ℕ} [NeZero L] {β : Type*} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (Y : Finset (Cube d L))
    (hHsub : ∀ X, X ∈ Λ → (H X).fluctuationSupport ⊆ skeleton HF X.val) :
    (appendixFHoleConnectedLocalActivity HF z Λ H Y).fluctuationSupport ⊆
      skeleton HF Y := by
  classical
  intro x hx
  rw [appendixFHoleConnectedLocalActivity] at hx
  change x ∈
    (appendixFTargetFiber
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y).biUnion
        (fun C => (LocalActivity.mayerCoverActivity C H).fluctuationSupport) at hx
  rcases Finset.mem_biUnion.mp hx with ⟨C, hC, hxC⟩
  rw [LocalActivity.mayerCoverActivity_fluctuationSupport] at hxC
  rcases Finset.mem_biUnion.mp hxC with ⟨X, hX, hxX⟩
  have hCfiber := (mem_appendixFTargetFiber_iff
    (Finset.univ : Finset (Cube d L))
    (fun X : OmegaPolymerType HF z => skeleton HF X.val)
    (fun X : OmegaPolymerType HF z => X.val)
    Λ Y C).mp hC
  have hCsubset : C ⊆ Λ :=
    ((mem_appendixFConnectedCoverRegion_iff
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      Λ C).mp hCfiber.1).1
  have hxSkelX : x ∈ skeleton HF X.val :=
    hHsub X (hCsubset hX) hxX
  have hxUnion :
      x ∈ appendixFCoverUnion
        (fun X : OmegaPolymerType HF z => skeleton HF X.val) C := by
    exact Finset.mem_biUnion.mpr ⟨X, hX, hxSkelX⟩
  have hUnion :
      appendixFCoverUnion
          (fun X : OmegaPolymerType HF z => skeleton HF X.val) C =
        skeleton HF Y := by
    calc
      appendixFCoverUnion
          (fun X : OmegaPolymerType HF z => skeleton HF X.val) C =
          skeleton HF
            (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C) := by
        exact (appendixFHoleCoverUnion_skeleton HF z C).symm
      _ = skeleton HF Y := by
        rw [hCfiber.2]
  simpa [hUnion] using hxUnion

/-- The connected target activity depends on spectator fields only in the
active skeleton of the declared target, provided each input local activity has
its spectator support inside the active skeleton of its source polymer.

This is the spectator-field analogue of
`appendixFHoleConnectedLocalActivity_fluctuationSupport_subset_skeleton`. -/
theorem appendixFHoleConnectedLocalActivity_spectatorSupport_subset_skeleton
    {d L : ℕ} [NeZero L] {β : Type*} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (Y : Finset (Cube d L))
    (hHsub : ∀ X, X ∈ Λ → (H X).spectatorSupport ⊆ skeleton HF X.val) :
    (appendixFHoleConnectedLocalActivity HF z Λ H Y).spectatorSupport ⊆
      skeleton HF Y := by
  classical
  intro x hx
  rw [appendixFHoleConnectedLocalActivity] at hx
  change x ∈
    (appendixFTargetFiber
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y).biUnion
        (fun C => (LocalActivity.mayerCoverActivity C H).spectatorSupport) at hx
  rcases Finset.mem_biUnion.mp hx with ⟨C, hC, hxC⟩
  rw [LocalActivity.mayerCoverActivity_spectatorSupport] at hxC
  rcases Finset.mem_biUnion.mp hxC with ⟨X, hX, hxX⟩
  have hCfiber := (mem_appendixFTargetFiber_iff
    (Finset.univ : Finset (Cube d L))
    (fun X : OmegaPolymerType HF z => skeleton HF X.val)
    (fun X : OmegaPolymerType HF z => X.val)
    Λ Y C).mp hC
  have hCsubset : C ⊆ Λ :=
    ((mem_appendixFConnectedCoverRegion_iff
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      Λ C).mp hCfiber.1).1
  have hxSkelX : x ∈ skeleton HF X.val :=
    hHsub X (hCsubset hX) hxX
  have hxUnion :
      x ∈ appendixFCoverUnion
        (fun X : OmegaPolymerType HF z => skeleton HF X.val) C := by
    exact Finset.mem_biUnion.mpr ⟨X, hX, hxSkelX⟩
  have hUnion :
      appendixFCoverUnion
          (fun X : OmegaPolymerType HF z => skeleton HF X.val) C =
        skeleton HF Y := by
    calc
      appendixFCoverUnion
          (fun X : OmegaPolymerType HF z => skeleton HF X.val) C =
          skeleton HF
            (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C) := by
        exact (appendixFHoleCoverUnion_skeleton HF z C).symm
      _ = skeleton HF Y := by
        rw [hCfiber.2]
  simpa [hUnion] using hxUnion

/-- The integrated first activity `K#(Y, psi)`: integrate the fluctuation
field of the connected local activity against the ultralocal product measure. -/
noncomputable def appendixFHoleKsharp
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (Y : Finset (Cube d L)) :
    LocalFunctional (Cube d L) Ψ ℂ :=
  (appendixFHoleConnectedLocalActivity HF z Λ H Y).integrateFluctuation μ

@[simp] theorem appendixFHoleKsharp_globalEval
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x) :
    (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ =
      ∫ φ : (∀ _ : Cube d L, β),
        (appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ
        ∂(Measure.pi fun _ : Cube d L => μ) := rfl

/-- A uniform bound on the first connected activity transfers to the integrated
activity `K#`.  The `Integrable` hypothesis is intentionally explicit: later
Appendix-F integration theorems must prove or carry it rather than relying on
Lean's totalized integral. -/
theorem norm_appendixFHoleKsharp_globalEval_le
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x) {B : ℝ}
    (hint : Integrable
      (fun φ : (∀ _ : Cube d L, β) =>
        (appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ)
      (Measure.pi fun _ : Cube d L => μ))
    (hK : ∀ φ : (∀ _ : Cube d L, β),
      ‖(appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ‖ ≤ B) :
    ‖(appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ‖ ≤ B := by
  exact LocalActivity.norm_globalEval_integrateFluctuation_le_of_norm_le
    μ (appendixFHoleConnectedLocalActivity HF z Λ H Y) ψ hint hK

/-- If every raw activity only depends on spectator fields inside its full
source polymer, then the integrated first activity `K#(Y)` has spectator
support contained in the target union `Y`. -/
theorem appendixFHoleKsharp_support_subset
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (Y : Finset (Cube d L))
    (hsub : ∀ X, X ∈ Λ → (H X).spectatorSupport ⊆ X.val) :
    (appendixFHoleKsharp HF z Λ H μ Y).support ⊆ Y := by
  exact appendixFHoleConnectedLocalActivity_spectatorSupport_subset
    HF z Λ H Y hsub

/-- The integrated first activity `K#(Y, psi)` depends on spectator fields only
inside the active skeleton of the declared target, provided the input
one-polymer activities have spectator support inside their own active
skeletons. -/
theorem appendixFHoleKsharp_support_subset_skeleton
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (Y : Finset (Cube d L))
    (hHsub : ∀ X, X ∈ Λ → (H X).spectatorSupport ⊆ skeleton HF X.val) :
    (appendixFHoleKsharp HF z Λ H μ Y).support ⊆ skeleton HF Y := by
  exact appendixFHoleConnectedLocalActivity_spectatorSupport_subset_skeleton
    HF z Λ H Y hHsub

/-- The integrated first activity `K#(Y)` only depends on spectator fields in
the full target `Y`, provided each input one-polymer activity has spectator
support inside its own full source polymer. -/
theorem appendixFHoleKsharp_globalEval_eq_of_agreeOn
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (Y : Finset (Cube d L))
    (hsub : ∀ X, X ∈ Λ → (H X).spectatorSupport ⊆ X.val)
    {ψ₁ ψ₂ : ∀ x, Ψ x}
    (hψ : AgreeOn Y ψ₁ ψ₂) :
    (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ₁ =
      (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ₂ := by
  refine LocalFunctional.globalEval_eq_of_agreeOn
    (appendixFHoleKsharp HF z Λ H μ Y) ?_
  intro x hx
  exact hψ x (appendixFHoleKsharp_support_subset HF z Λ H μ Y hsub hx)

/-- The integrated first activity `K#(Y)` only depends on spectator fields in
the active skeleton of `Y`, provided each input one-polymer activity has
spectator support inside its own active skeleton. -/
theorem appendixFHoleKsharp_globalEval_eq_of_agreeOn_skeleton
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (Y : Finset (Cube d L))
    (hHsub : ∀ X, X ∈ Λ → (H X).spectatorSupport ⊆ skeleton HF X.val)
    {ψ₁ ψ₂ : ∀ x, Ψ x}
    (hψ : AgreeOn (skeleton HF Y) ψ₁ ψ₂) :
    (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ₁ =
      (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ₂ := by
  refine LocalFunctional.globalEval_eq_of_agreeOn
    (appendixFHoleKsharp HF z Λ H μ Y) ?_
  intro x hx
  exact hψ x
    (appendixFHoleKsharp_support_subset_skeleton HF z Λ H μ Y hHsub hx)

/-- In an admissible target family, the integrated first activities `K#(Y)`
have pairwise-disjoint spectator supports as soon as each source one-polymer
activity has spectator support inside its own active skeleton. -/
theorem appendixFHoleKsharp_pairwise_disjoint_support_of_admissibleTargetFamilies
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    {targets : Finset (Finset (Cube d L))}
    (htargets : targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ)
    (hHsub : ∀ X, X ∈ Λ → (H X).spectatorSupport ⊆ skeleton HF X.val) :
    ∀ Y, Y ∈ targets → ∀ Z, Z ∈ targets → Y ≠ Z →
      Disjoint
        (appendixFHoleKsharp HF z Λ H μ Y).support
        (appendixFHoleKsharp HF z Λ H μ Z).support := by
  intro Y hY Z hZ hYZ
  have htargetData :=
    (mem_appendixFHoleAdmissibleTargetFamilies_iff HF z Λ targets).mp htargets
  have hskel : Disjoint (skeleton HF Y) (skeleton HF Z) :=
    htargetData.2 Y hY Z hZ hYZ
  have hYsub :
      (appendixFHoleKsharp HF z Λ H μ Y).support ⊆ skeleton HF Y :=
    appendixFHoleKsharp_support_subset_skeleton HF z Λ H μ Y hHsub
  have hZsub :
      (appendixFHoleKsharp HF z Λ H μ Z).support ⊆ skeleton HF Z :=
    appendixFHoleKsharp_support_subset_skeleton HF z Λ H μ Z hHsub
  rw [Finset.disjoint_left]
  intro x hxY hxZ
  exact (Finset.disjoint_left.mp hskel (hYsub hxY)) (hZsub hxZ)

/-- Direct scalar form of `K#`: the fluctuation integral of the connected
target-fiber Mayer activity with the pointwise raw factors `exp (H X) - 1`. -/
theorem appendixFHoleKsharp_globalEval_eq_integral_connectedMayerActivity
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x) :
    (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ =
      ∫ φ : (∀ _ : Cube d L, β),
        appendixFHoleConnectedMayerActivity HF z Λ
          (fun X => Complex.exp ((H X).globalEval ψ φ) - 1) Y
        ∂(Measure.pi fun _ : Cube d L => μ) := by
  rw [appendixFHoleKsharp_globalEval]
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro φ
  exact appendixFHoleConnectedLocalActivity_globalEval HF z Λ H Y ψ φ

/-- Pairwise-disjoint target connected activities factorize after fluctuation
integration.  This is the `K#`-level ultralocal factorization step with the
actual fluctuation-support hypothesis kept explicit. -/
theorem integral_prod_appendixFHoleConnectedLocalActivity_eq_prod_Ksharp_of_pairwise_disjoint_fluctuationSupport
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β] [Nonempty β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    (targets : Finset (Finset (Cube d L)))
    (ψ : ∀ x, Ψ x)
    (hdisj : ∀ Y, Y ∈ targets → ∀ Z, Z ∈ targets → Y ≠ Z →
      Disjoint
        (appendixFHoleConnectedLocalActivity HF z Λ H Y).fluctuationSupport
        (appendixFHoleConnectedLocalActivity HF z Λ H Z).fluctuationSupport) :
    ∫ φ : (∀ _ : Cube d L, β),
        ∏ Y ∈ targets,
          (appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ
        ∂(Measure.pi fun _ : Cube d L => μ)
      =
      ∏ Y ∈ targets,
        (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ := by
  let Ftarget : Finset (Cube d L) →
      LocalActivity (Cube d L) Ψ (fun _ => β) ℂ :=
    fun Y => appendixFHoleConnectedLocalActivity HF z Λ H Y
  have hfactor :=
    LocalActivity.integral_finsetProd_of_pairwise_disjoint_fluctuationSupport
      μ targets Ftarget ψ hdisj
  have hleft :
      (∫ φ : (∀ _ : Cube d L, β),
          ∏ Y ∈ targets, (Ftarget Y).globalEval ψ φ
          ∂(Measure.pi fun _ : Cube d L => μ))
        =
      ∫ φ : (∀ _ : Cube d L, β),
        (LocalActivity.finsetProd targets Ftarget).globalEval ψ φ
          ∂(Measure.pi fun _ : Cube d L => μ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro φ
    rw [LocalActivity.globalEval_finsetProd]
    exact (Finset.prod_attach targets
      (fun Y => (Ftarget Y).globalEval ψ φ)).symm
  calc
    (∫ φ : (∀ _ : Cube d L, β),
        ∏ Y ∈ targets, (appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ
        ∂(Measure.pi fun _ : Cube d L => μ))
        =
      ∫ φ : (∀ _ : Cube d L, β),
        (LocalActivity.finsetProd targets Ftarget).globalEval ψ φ
          ∂(Measure.pi fun _ : Cube d L => μ) := by
          simpa [Ftarget] using hleft
    _ =
      ∏ Y ∈ targets,
        ∫ φ : (∀ _ : Cube d L, β), (Ftarget Y).globalEval ψ φ
          ∂(Measure.pi fun _ : Cube d L => μ) := hfactor
    _ =
      ∏ Y ∈ targets,
        (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ := by
          refine Finset.prod_congr rfl ?_
          intro Y _hY
          exact (appendixFHoleKsharp_globalEval HF z Λ H μ Y ψ).symm

/-- Admissible Appendix-F target families factorize at the `K#` level once each
target connected activity's actual fluctuation support is contained in the
target's active skeleton.  The theorem keeps that support bridge explicit
instead of replacing the physical dependency proof by target-family
combinatorics. -/
theorem integral_prod_appendixFHoleConnectedLocalActivity_eq_prod_Ksharp
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β] [Nonempty β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    {targets : Finset (Finset (Cube d L))}
    (htargets : targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ)
    (ψ : ∀ x, Ψ x)
    (hsub : ∀ Y, Y ∈ targets →
      (appendixFHoleConnectedLocalActivity HF z Λ H Y).fluctuationSupport ⊆
        skeleton HF Y) :
    ∫ φ : (∀ _ : Cube d L, β),
        ∏ Y ∈ targets,
          (appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ
        ∂(Measure.pi fun _ : Cube d L => μ)
      =
      ∏ Y ∈ targets,
        (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ := by
  refine
    integral_prod_appendixFHoleConnectedLocalActivity_eq_prod_Ksharp_of_pairwise_disjoint_fluctuationSupport
      HF z Λ H μ targets ψ ?_
  intro Y hY Z hZ hYZ
  have htargetData :=
    (mem_appendixFHoleAdmissibleTargetFamilies_iff HF z Λ targets).mp htargets
  have hskel : Disjoint (skeleton HF Y) (skeleton HF Z) :=
    htargetData.2 Y hY Z hZ hYZ
  rw [Finset.disjoint_left]
  intro x hxY hxZ
  exact (Finset.disjoint_left.mp hskel (hsub Y hY hxY)) (hsub Z hZ hxZ)

/-- Source-local support form of the admissible Appendix-F `K#` product
factorization.  The target-level containment hypothesis is derived from the
input condition that every one-polymer activity depends only on fluctuation
sites in that polymer's active skeleton. -/
theorem integral_prod_appendixFHoleConnectedLocalActivity_eq_prod_Ksharp_of_local_fluctuationSupport_subset_skeleton
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β] [Nonempty β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    {targets : Finset (Finset (Cube d L))}
    (htargets : targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ)
    (ψ : ∀ x, Ψ x)
    (hHsub : ∀ X, X ∈ Λ → (H X).fluctuationSupport ⊆ skeleton HF X.val) :
    ∫ φ : (∀ _ : Cube d L, β),
        ∏ Y ∈ targets,
          (appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ
        ∂(Measure.pi fun _ : Cube d L => μ)
      =
      ∏ Y ∈ targets,
        (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ := by
  exact integral_prod_appendixFHoleConnectedLocalActivity_eq_prod_Ksharp
    HF z Λ H μ htargets ψ
    (fun Y _hY =>
      appendixFHoleConnectedLocalActivity_fluctuationSupport_subset_skeleton
        HF z Λ H Y hHsub)

/-- If the source one-polymer activities are spectator-local in their active
skeletons, then `K#` activities indexed by an admissible target family
factorize under a further ultralocal product measure on the spectator field.

This is only a support/factorization bridge; the source-locality hypothesis is
still explicit and no Appendix-F activity estimate is inferred. -/
theorem integral_prod_appendixFHoleKsharp_eq_prod_integral_of_admissibleTargetFamilies
    {d L : ℕ} [NeZero L] {β γ : Type*}
    [MeasurableSpace β] [MeasurableSpace γ] [Nonempty β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : Measure γ)
    (ν : Measure β) [IsProbabilityMeasure ν]
    {targets : Finset (Finset (Cube d L))}
    (htargets : targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ)
    (hHsub : ∀ X, X ∈ Λ → (H X).spectatorSupport ⊆ skeleton HF X.val) :
    ∫ ψ : (∀ _ : Cube d L, β),
        ∏ Y ∈ targets,
          (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ
        ∂(Measure.pi fun _ : Cube d L => ν)
      =
      ∏ Y ∈ targets,
        ∫ ψ : (∀ _ : Cube d L, β),
          (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ
          ∂(Measure.pi fun _ : Cube d L => ν) := by
  classical
  let Ftarget : Finset (Cube d L) →
      LocalFunctional (Cube d L) (fun _ => β) ℂ :=
    fun Y => appendixFHoleKsharp HF z Λ H μ Y
  have hfactor :=
    LocalFunctional.integral_finsetProd_of_pairwise_disjoint_support
      ν targets Ftarget
      (appendixFHoleKsharp_pairwise_disjoint_support_of_admissibleTargetFamilies
        HF z Λ H μ htargets hHsub)
  have hleft :
      (∫ ψ : (∀ _ : Cube d L, β),
          ∏ Y ∈ targets, (Ftarget Y).globalEval ψ
          ∂(Measure.pi fun _ : Cube d L => ν))
        =
      ∫ ψ : (∀ _ : Cube d L, β),
        (LocalFunctional.finsetProd targets Ftarget).globalEval ψ
          ∂(Measure.pi fun _ : Cube d L => ν) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ψ
    rw [LocalFunctional.globalEval_finsetProd]
    exact (Finset.prod_attach targets
      (fun Y => (Ftarget Y).globalEval ψ)).symm
  calc
    (∫ ψ : (∀ _ : Cube d L, β),
        ∏ Y ∈ targets,
          (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ
        ∂(Measure.pi fun _ : Cube d L => ν))
        =
      ∫ ψ : (∀ _ : Cube d L, β),
        (LocalFunctional.finsetProd targets Ftarget).globalEval ψ
          ∂(Measure.pi fun _ : Cube d L => ν) := by
          simpa [Ftarget] using hleft
    _ =
      ∏ Y ∈ targets,
        ∫ ψ : (∀ _ : Cube d L, β), (Ftarget Y).globalEval ψ
          ∂(Measure.pi fun _ : Cube d L => ν) := hfactor
    _ =
      ∏ Y ∈ targets,
        ∫ ψ : (∀ _ : Cube d L, β),
          (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ
          ∂(Measure.pi fun _ : Cube d L => ν) := by
          rfl

/-- Finite target-family Fubini for the first Appendix-F fluctuation
integration.  The summands are connected target-family products before the
fluctuation integral; the right-hand side is the same finite target-family
partition sum with each connected target replaced by `K#`.

The theorem is purely finite: per-target-family integrability is an explicit
hypothesis, and the source-local support bridge is stated separately from the
combinatorics. -/
theorem integral_sum_appendixFHoleConnectedLocalActivity_eq_sum_prod_Ksharp_of_local_fluctuationSupport_subset_skeleton
    {d L : ℕ} [NeZero L] {β : Type*} [MeasurableSpace β] [Nonempty β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    (ψ : ∀ x, Ψ x)
    (hHsub : ∀ X, X ∈ Λ → (H X).fluctuationSupport ⊆ skeleton HF X.val)
    (hint : ∀ targets,
      targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ →
        Integrable
          (fun φ : (∀ _ : Cube d L, β) =>
            ∏ Y ∈ targets,
              (appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ)
          (Measure.pi fun _ : Cube d L => μ)) :
    ∫ φ : (∀ _ : Cube d L, β),
        (∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
          ∏ Y ∈ targets,
            (appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ)
        ∂(Measure.pi fun _ : Cube d L => μ)
      =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets,
          (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ := by
  classical
  calc
    (∫ φ : (∀ _ : Cube d L, β),
        (∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
          ∏ Y ∈ targets,
            (appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ)
        ∂(Measure.pi fun _ : Cube d L => μ))
        =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∫ φ : (∀ _ : Cube d L, β),
          ∏ Y ∈ targets,
            (appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ
          ∂(Measure.pi fun _ : Cube d L => μ) := by
        exact MeasureTheory.integral_finset_sum
          (appendixFHoleAdmissibleTargetFamilies HF z Λ) hint
    _ =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets,
          (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ := by
        refine Finset.sum_congr rfl ?_
        intro targets htargets
        exact
          integral_prod_appendixFHoleConnectedLocalActivity_eq_prod_Ksharp_of_local_fluctuationSupport_subset_skeleton
            HF z Λ H μ htargets ψ hHsub

/-- Finite target-family Fubini after the first integration.  For an admissible
target family, the product of `K#` activities factorizes under a spectator
product measure; summing those finite identities gives the integrated
target-family partition identity.

This is the finite algebraic/measure-theoretic bridge behind the Appendix-F
`K#`-to-integrated-target-family step.  It does not assert any bound on the
resulting single-target integrals. -/
theorem integral_sum_appendixFHoleKsharp_eq_sum_prod_integral_of_admissibleTargetFamilies
    {d L : ℕ} [NeZero L] {β γ : Type*}
    [MeasurableSpace β] [MeasurableSpace γ] [Nonempty β]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z → LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : Measure γ)
    (ν : Measure β) [IsProbabilityMeasure ν]
    (hHsub : ∀ X, X ∈ Λ → (H X).spectatorSupport ⊆ skeleton HF X.val)
    (hint : ∀ targets,
      targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ →
        Integrable
          (fun ψ : (∀ _ : Cube d L, β) =>
            ∏ Y ∈ targets,
              (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ)
          (Measure.pi fun _ : Cube d L => ν)) :
    ∫ ψ : (∀ _ : Cube d L, β),
        (∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
          ∏ Y ∈ targets,
            (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ)
        ∂(Measure.pi fun _ : Cube d L => ν)
      =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets,
          ∫ ψ : (∀ _ : Cube d L, β),
            (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ
            ∂(Measure.pi fun _ : Cube d L => ν) := by
  classical
  calc
    (∫ ψ : (∀ _ : Cube d L, β),
        (∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
          ∏ Y ∈ targets,
            (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ)
        ∂(Measure.pi fun _ : Cube d L => ν))
        =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∫ ψ : (∀ _ : Cube d L, β),
          ∏ Y ∈ targets,
            (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ
          ∂(Measure.pi fun _ : Cube d L => ν) := by
        exact MeasureTheory.integral_finset_sum
          (appendixFHoleAdmissibleTargetFamilies HF z Λ) hint
    _ =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets,
          ∫ ψ : (∀ _ : Cube d L, β),
            (appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ
            ∂(Measure.pi fun _ : Cube d L => ν) := by
        refine Finset.sum_congr rfl ?_
        intro targets htargets
        exact
          integral_prod_appendixFHoleKsharp_eq_prod_integral_of_admissibleTargetFamilies
            HF z Λ H μ ν htargets hHsub

end YangMills.RG
