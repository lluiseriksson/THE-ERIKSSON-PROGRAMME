/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHoleTargetFamily
import YangMills.RG.OmegaConnectedCover

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
activity `H#`.  It does not prove the n-ary target-family factorization, the
Dimock (642) activity estimate, the second Ursell expansion, or any concrete
Yang--Mills raw activity bound.

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

end YangMills.RG
