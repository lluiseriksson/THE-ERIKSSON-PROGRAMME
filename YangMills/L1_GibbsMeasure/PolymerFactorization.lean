/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Polymer representation, step 2 (core) — independence over disjoint supports

The abstract factorization that makes polymer activities multiplicative: for
a product probability measure, the integral of a product of two observables
**depending on disjoint coordinate sets** factorizes:

  `∫ F·G  =  ∫F · ∫G`.

Proof: split the coordinate space along the predicate
(`MeasurableEquiv.piEquivPiSubtypeProd`, measure-preserving onto the product
of the two marginal product measures), observe each factor depends on only
one block, and apply the unconditional product-integral identity
(`integral_prod_mul`).  No integrability hypotheses are needed.

Applied to the lattice (next slice): Mayer-weight products over plaquette
sets with disjoint supports (`prod_plaquetteWeight_congr` is exactly the
dependency hypothesis) have multiplicative gauge expectations — the polymer
activity factorization over connected components.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory

/-- **Two-block independence for product measures:** if `F` depends only on
the coordinates satisfying `p` and `G` only on those violating it, then
`∫ F·G = ∫F · ∫G` under any product probability measure.  No integrability
hypotheses. -/
theorem integral_mul_of_disjoint_deps {ι : Type*} [Fintype ι]
    {β : Type*} [MeasurableSpace β] [Nonempty β]
    (μ : Measure β) [IsProbabilityMeasure μ]
    (p : ι → Prop) [DecidablePred p] (F G : (ι → β) → ℝ)
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
  -- coordinates of the inverse equivalence
  have hcoord : ∀ (a : {i // p i} → β) (b : {i // ¬ p i} → β) (i : ι),
      e.symm (a, b) i = if h : p i then a ⟨i, h⟩ else b ⟨i, h⟩ := by
    intro a b i
    simp [hedef, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]
  -- the block restrictions
  set F₁ : ({i // p i} → β) → ℝ := fun a => F (e.symm (a, fun _ => b₀))
    with hF₁def
  set G₁ : ({i // ¬ p i} → β) → ℝ := fun b => G (e.symm (fun _ => b₀, b))
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
  -- integral transport along the (inverse) equivalence
  have htrans : ∀ H : (ι → β) → ℝ,
      ∫ x, H x ∂(Measure.pi fun _ : ι => μ)
        = ∫ z, H (e.symm z)
            ∂((Measure.pi fun _ : {i // p i} => μ).prod
              (Measure.pi fun _ : {i // ¬ p i} => μ)) := by
    intro H
    have hmp' := hmp.symm e
    rw [← hmp'.map_eq, MeasureTheory.integral_map_equiv]
  -- the three transported integrals and the product split
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
  rw [hptFG, hptF, hptG, MeasureTheory.integral_prod_mul]
  congr 1
  · have h1 := MeasureTheory.integral_prod_mul
      (μ := Measure.pi fun _ : {i // p i} => μ)
      (ν := Measure.pi fun _ : {i // ¬ p i} => μ) F₁ (fun _ => (1 : ℝ))
    simp only [mul_one] at h1
    rw [h1]
    simp
  · have h1 := MeasureTheory.integral_prod_mul
      (μ := Measure.pi fun _ : {i // p i} => μ)
      (ν := Measure.pi fun _ : {i // ¬ p i} => μ) (fun _ => (1 : ℝ)) G₁
    simp only [one_mul] at h1
    rw [h1]
    simp

end YangMills
