/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.PolymerFactorization

/-!
# Edge factorization over the product measure (area law, AL4 substrate)

The per-edge Haar integration of the Wilson-loop expansion needs the
two-block independence factorization for **complex-valued**
observables (the entry monomials are `ℂ`-valued), plus its
single-coordinate corollary:

* `integral_mul_of_disjoint_deps_complex` — `∫ F·G = ∫F · ∫G` under a
  product probability measure when `F` and `G` depend on disjoint
  coordinate blocks (the `ℂ` twin of `integral_mul_of_disjoint_deps`);
* `integral_single_coord_marginal` — a factor depending on ONE
  coordinate splits off: `∫ F₀(x e₀)·F₁(x) = ∫ F₀(x e₀) · ∫ F₁` when
  `F₁` ignores the `e₀`-coordinate.  Iterating this over the edges is
  AL4's per-edge integration.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory

/-- **Two-block independence for product measures, `ℂ`-valued:** if
`F` depends only on the coordinates satisfying `p` and `G` only on
those violating it, then `∫ F·G = ∫F · ∫G` under any product
probability measure. -/
theorem integral_mul_of_disjoint_deps_complex {ι : Type*} [Fintype ι]
    {β : Type*} [MeasurableSpace β] [Nonempty β]
    (μ : Measure β) [IsProbabilityMeasure μ]
    (p : ι → Prop) [DecidablePred p] (F G : (ι → β) → ℂ)
    (hF : ∀ x y : ι → β, (∀ i, p i → x i = y i) → F x = F y)
    (hG : ∀ x y : ι → β, (∀ i, ¬ p i → x i = y i) → G x = G y) :
    ∫ x, F x * G x ∂(Measure.pi fun _ : ι => μ)
      = (∫ x, F x ∂(Measure.pi fun _ : ι => μ)) *
        ∫ x, G x ∂(Measure.pi fun _ : ι => μ) := by
  classical
  obtain ⟨b₀⟩ := (inferInstance : Nonempty β)
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => β) p with hedef
  have hmp : MeasurePreserving e (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : {i // p i} => μ).prod
        (Measure.pi fun _ : {i // ¬ p i} => μ)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p
  have hcoord : ∀ (a : {i // p i} → β) (b : {i // ¬ p i} → β) (i : ι),
      e.symm (a, b) i = if h : p i then a ⟨i, h⟩ else b ⟨i, h⟩ := by
    intro a b i
    simp [hedef, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]
  set F₁ : ({i // p i} → β) → ℂ := fun a => F (e.symm (a, fun _ => b₀))
    with hF₁def
  set G₁ : ({i // ¬ p i} → β) → ℂ := fun b => G (e.symm (fun _ => b₀, b))
    with hG₁def
  have hFsplit : ∀ (a : {i // p i} → β) (b : {i // ¬ p i} → β),
      F (e.symm (a, b)) = F₁ a := by
    intro a b
    refine hF _ _ fun i hi => ?_
    rw [hcoord, hcoord, dif_pos hi, dif_pos hi]
  have hGsplit : ∀ (a : {i // p i} → β) (b : {i // ¬ p i} → β),
      G (e.symm (a, b)) = G₁ b := by
    intro a b
    refine hG _ _ fun i hi => ?_
    rw [hcoord, hcoord, dif_neg hi, dif_neg hi]
  have htrans : ∀ H : (ι → β) → ℂ,
      ∫ x, H x ∂(Measure.pi fun _ : ι => μ)
        = ∫ z, H (e.symm z)
            ∂((Measure.pi fun _ : {i // p i} => μ).prod
              (Measure.pi fun _ : {i // ¬ p i} => μ)) := by
    intro H
    have hmp' := hmp.symm e
    rw [← hmp'.map_eq, MeasureTheory.integral_map_equiv]
  rw [htrans (fun x => F x * G x), htrans F, htrans G]
  have hptFG : (fun z : ({i // p i} → β) × ({i // ¬ p i} → β) =>
      F (e.symm z) * G (e.symm z)) = fun z => F₁ z.1 * G₁ z.2 := by
    funext z
    rw [show z = (z.1, z.2) from rfl, hFsplit z.1 z.2, hGsplit z.1 z.2]
  have hptF : (fun z : ({i // p i} → β) × ({i // ¬ p i} → β) =>
      F (e.symm z)) = fun z => F₁ z.1 := by
    funext z
    rw [show z = (z.1, z.2) from rfl, hFsplit z.1 z.2]
  have hptG : (fun z : ({i // p i} → β) × ({i // ¬ p i} → β) =>
      G (e.symm z)) = fun z => G₁ z.2 := by
    funext z
    rw [show z = (z.1, z.2) from rfl, hGsplit z.1 z.2]
  rw [hptFG, hptF, hptG]
  -- `rw [integral_prod_mul]` fails on hidden instance arguments here, so we
  -- compose the equalities in term mode (defeq checking, not keyed matching).
  have hmul := MeasureTheory.integral_prod_mul
    (μ := Measure.pi fun _ : {i // p i} => μ)
    (ν := Measure.pi fun _ : {i // ¬ p i} => μ) F₁ G₁
  have h1F := MeasureTheory.integral_prod_mul
    (μ := Measure.pi fun _ : {i // p i} => μ)
    (ν := Measure.pi fun _ : {i // ¬ p i} => μ) F₁ (fun _ => (1 : ℂ))
  have h1G := MeasureTheory.integral_prod_mul
    (μ := Measure.pi fun _ : {i // p i} => μ)
    (ν := Measure.pi fun _ : {i // ¬ p i} => μ) (fun _ => (1 : ℂ)) G₁
  simp at h1F h1G
  exact hmul.trans (congrArg₂ (· * ·) h1F.symm h1G.symm)

/-- **Single-coordinate marginalization:** a factor depending on one
coordinate splits off the product integral — the per-edge integration
step of the Wilson-loop expansion.  Iterate over the edges of the
lattice. -/
theorem integral_single_coord_marginal {ι : Type*} [Fintype ι]
    {β : Type*} [MeasurableSpace β] [Nonempty β]
    (μ : Measure β) [IsProbabilityMeasure μ] (e₀ : ι)
    (F₀ : β → ℂ) (F₁ : (ι → β) → ℂ)
    (hF₁ : ∀ x y : ι → β, (∀ i, i ≠ e₀ → x i = y i) → F₁ x = F₁ y) :
    ∫ x, F₀ (x e₀) * F₁ x ∂(Measure.pi fun _ : ι => μ)
      = (∫ x, F₀ (x e₀) ∂(Measure.pi fun _ : ι => μ)) *
        ∫ x, F₁ x ∂(Measure.pi fun _ : ι => μ) := by
  classical
  refine integral_mul_of_disjoint_deps_complex μ (fun i => i = e₀)
    (fun x => F₀ (x e₀)) F₁ ?_ ?_
  · intro x y hxy
    show F₀ (x e₀) = F₀ (y e₀)
    rw [hxy e₀ rfl]
  · intro x y hxy
    exact hF₁ x y hxy

end YangMills
