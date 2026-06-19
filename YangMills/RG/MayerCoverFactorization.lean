/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.OmegaConnectedCover
import YangMills.RG.UltralocalFactorization

/-!
# Ultralocal factorization for Mayer-cover products

This module connects the type-local Mayer-cover substrate to the finite
product-measure independence theorem.

If two finite Mayer-cover products depend on disjoint fluctuation supports,
then the integral of their product under an explicit ultralocal product
probability measure factorizes.  A pairwise-disjoint support version is also
provided, since that is the shape a disconnected-cover compiler naturally
produces.

Honest scope: this is still finite product-measure independence.  It does not
prove Dimock Appendix F, the renormalized activity estimate, the Yang--Mills
fluctuation integral, a continuum limit, or OS/Wightman reconstruction.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators

namespace LocalActivity

/-- Pairwise disjoint fluctuation supports imply disjoint support unions for
two finite Mayer covers. -/
theorem fluctuationSupport_biUnion_disjoint_of_pairwise
    {Site ι κ : Type*} [DecidableEq Site]
    {Ψ Φ : Site → Type*}
    (I : Finset ι) (J : Finset κ)
    (H : ι → LocalActivity Site Ψ Φ ℂ)
    (K : κ → LocalActivity Site Ψ Φ ℂ)
    (hpair : ∀ i, i ∈ I → ∀ j, j ∈ J →
      Disjoint (H i).fluctuationSupport (K j).fluctuationSupport) :
    Disjoint (I.biUnion fun i => (H i).fluctuationSupport)
      (J.biUnion fun j => (K j).fluctuationSupport) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [Finset.mem_biUnion] at hx hy
  rcases hx with ⟨i, hi, hxi⟩
  rcases hy with ⟨j, hj, hxj⟩
  exact (Finset.disjoint_left.mp (hpair i hi j hj)) hxi hxj

/-- Two Mayer-cover products with disjoint fluctuation-support unions
factorize under an ultralocal product probability measure, with the spectator
field held fixed. -/
theorem mayerCoverActivity_integral_mul_of_disjoint_fluctuationSupport
    {Site β ι κ : Type*} [Fintype Site] [DecidableEq Site]
    [MeasurableSpace β] [Nonempty β]
    {Ψ : Site → Type*}
    (μ : Measure β) [IsProbabilityMeasure μ]
    (I : Finset ι) (J : Finset κ)
    (H : ι → LocalActivity Site Ψ (fun _ => β) ℂ)
    (K : κ → LocalActivity Site Ψ (fun _ => β) ℂ)
    (ψ : ∀ x, Ψ x)
    (hdisj : Disjoint (I.biUnion fun i => (H i).fluctuationSupport)
      (J.biUnion fun j => (K j).fluctuationSupport)) :
    ∫ φ, (mayerCoverActivity I H).globalEval ψ φ *
        (mayerCoverActivity J K).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)
      =
      (∫ φ, (mayerCoverActivity I H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)) *
      ∫ φ, (mayerCoverActivity J K).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ) := by
  exact integral_mul_of_disjoint_fluctuationSupport μ
    (mayerCoverActivity I H) (mayerCoverActivity J K) ψ hdisj

/-- Pairwise-disjoint form of Mayer-cover product factorization. -/
theorem mayerCoverActivity_integral_mul_of_pairwise_disjoint_fluctuationSupport
    {Site β ι κ : Type*} [Fintype Site] [DecidableEq Site]
    [MeasurableSpace β] [Nonempty β]
    {Ψ : Site → Type*}
    (μ : Measure β) [IsProbabilityMeasure μ]
    (I : Finset ι) (J : Finset κ)
    (H : ι → LocalActivity Site Ψ (fun _ => β) ℂ)
    (K : κ → LocalActivity Site Ψ (fun _ => β) ℂ)
    (ψ : ∀ x, Ψ x)
    (hpair : ∀ i, i ∈ I → ∀ j, j ∈ J →
      Disjoint (H i).fluctuationSupport (K j).fluctuationSupport) :
    ∫ φ, (mayerCoverActivity I H).globalEval ψ φ *
        (mayerCoverActivity J K).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)
      =
      (∫ φ, (mayerCoverActivity I H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)) *
      ∫ φ, (mayerCoverActivity J K).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ) :=
  mayerCoverActivity_integral_mul_of_disjoint_fluctuationSupport μ I J H K ψ
    (fluctuationSupport_biUnion_disjoint_of_pairwise I J H K hpair)

end LocalActivity

namespace OmegaConnectedCover

/-- Two Ω-connected Mayer activities with disjoint fluctuation-support unions
factorize under an ultralocal product probability measure, with the spectator
field held fixed.  The Ω-connectedness certificates travel with the covers;
the independence input is the disjointness of the actual fluctuation
dependencies. -/
theorem mayerActivity_integral_mul_of_disjoint_fluctuationSupport
    {Site β ι κ : Type*} [Fintype Site] [DecidableEq Site]
    [MeasurableSpace β] [Nonempty β]
    {Ψ : Site → Type*}
    (μ : Measure β) [IsProbabilityMeasure μ]
    (C : OmegaConnectedCover Site ι) (D : OmegaConnectedCover Site κ)
    (H : ι → LocalActivity Site Ψ (fun _ => β) ℂ)
    (K : κ → LocalActivity Site Ψ (fun _ => β) ℂ)
    (ψ : ∀ x, Ψ x)
    (hdisj : Disjoint (C.index.biUnion fun i => (H i).fluctuationSupport)
      (D.index.biUnion fun j => (K j).fluctuationSupport)) :
    ∫ φ, (C.mayerActivity H).globalEval ψ φ *
        (D.mayerActivity K).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)
      =
      (∫ φ, (C.mayerActivity H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)) *
      ∫ φ, (D.mayerActivity K).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ) := by
  exact LocalActivity.integral_mul_of_disjoint_fluctuationSupport μ
    (C.mayerActivity H) (D.mayerActivity K) ψ hdisj

/-- Pairwise-disjoint form of Ω-connected Mayer-activity factorization. -/
theorem mayerActivity_integral_mul_of_pairwise_disjoint_fluctuationSupport
    {Site β ι κ : Type*} [Fintype Site] [DecidableEq Site]
    [MeasurableSpace β] [Nonempty β]
    {Ψ : Site → Type*}
    (μ : Measure β) [IsProbabilityMeasure μ]
    (C : OmegaConnectedCover Site ι) (D : OmegaConnectedCover Site κ)
    (H : ι → LocalActivity Site Ψ (fun _ => β) ℂ)
    (K : κ → LocalActivity Site Ψ (fun _ => β) ℂ)
    (ψ : ∀ x, Ψ x)
    (hpair : ∀ i, i ∈ C.index → ∀ j, j ∈ D.index →
      Disjoint (H i).fluctuationSupport (K j).fluctuationSupport) :
    ∫ φ, (C.mayerActivity H).globalEval ψ φ *
        (D.mayerActivity K).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)
      =
      (∫ φ, (C.mayerActivity H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)) *
      ∫ φ, (D.mayerActivity K).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ) :=
  mayerActivity_integral_mul_of_disjoint_fluctuationSupport μ C D H K ψ
    (LocalActivity.fluctuationSupport_biUnion_disjoint_of_pairwise
      C.index D.index H K hpair)

end OmegaConnectedCover

end YangMills.RG
