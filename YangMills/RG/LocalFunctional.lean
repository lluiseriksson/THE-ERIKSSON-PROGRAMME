/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib

/-!
# Local functionals with support in the type

Dimock's Appendix-F compiler should not represent a local activity as a global
field functional plus a later `DependsOnlyOn` proof.  This file provides the
type-level substrate: a local functional can only inspect a restricted field on
its finite support.

The key bridge is `globalEval_eq_of_agreeOn`: once a local functional is
adapted back to global fields, changing the global field outside the support is
definitionally irrelevant.  The finite-product constructor uses support unions,
which is the algebraic skeleton needed for the future connected-cover activity
`K(Y) = Σ ∏_X (exp H_X - 1)`.

Honest scope: this file proves the locality algebra only.  It does not define
Dimock's Mayer transform, ultralocal integration, Appendix F, Yang--Mills raw
activity decay, or any continuum/OS reconstruction statement.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators

/-- A field restricted to the finite support `S`.  The type of the value may
depend on the site. -/
abbrev RestrictedField {Site : Type*} (S : Finset Site) (V : Site → Type*) :=
  ∀ x : {x // x ∈ S}, V x.1

/-- Restrict a global field to a finite support. -/
def restrictGlobal {Site : Type*} (S : Finset Site) {V : Site → Type*}
    (φ : ∀ x, V x) : RestrictedField S V :=
  fun x => φ x.1

/-- Restrict a field on a larger finite support to a smaller one. -/
def restrictRestricted {Site : Type*} {S T : Finset Site} {V : Site → Type*}
    (hST : S ⊆ T) (φ : RestrictedField T V) : RestrictedField S V :=
  fun x => φ ⟨x.1, hST x.2⟩

/-- Equality of global fields on a finite support. -/
def AgreeOn {Site : Type*} (S : Finset Site) {V : Site → Type*}
    (φ ψ : ∀ x, V x) : Prop :=
  ∀ x, x ∈ S → φ x = ψ x

theorem restrictGlobal_eq_of_agreeOn {Site : Type*} {S : Finset Site}
    {V : Site → Type*} {φ ψ : ∀ x, V x} (h : AgreeOn S φ ψ) :
    restrictGlobal S φ = restrictGlobal S ψ := by
  funext x
  exact h x.1 x.2

/-- A functional whose field dependency is confined to `support` by its type. -/
structure LocalFunctional (Site : Type*) (V : Site → Type*) (α : Type*) where
  support : Finset Site
  eval : RestrictedField support V → α

namespace LocalFunctional

variable {Site : Type*} {V : Site → Type*} {α β : Type*}

/-- Adapt a type-local functional back to global fields. -/
def globalEval (F : LocalFunctional Site V α) (φ : ∀ x, V x) : α :=
  F.eval (restrictGlobal F.support φ)

theorem globalEval_eq_of_agreeOn (F : LocalFunctional Site V α)
    {φ ψ : ∀ x, V x} (h : AgreeOn F.support φ ψ) :
    F.globalEval φ = F.globalEval ψ := by
  unfold globalEval
  rw [restrictGlobal_eq_of_agreeOn h]

/-- Postcompose a local functional without changing its support. -/
def map (f : α → β) (F : LocalFunctional Site V α) :
    LocalFunctional Site V β where
  support := F.support
  eval φ := f (F.eval φ)

@[simp] theorem globalEval_map (f : α → β) (F : LocalFunctional Site V α)
    (φ : ∀ x, V x) :
    (F.map f).globalEval φ = f (F.globalEval φ) := rfl

/-- Enlarge the support of a local functional.  The larger restricted field is
immediately restricted back to the original support before evaluation. -/
def extendSupport (F : LocalFunctional Site V α) {T : Finset Site}
    (hFT : F.support ⊆ T) : LocalFunctional Site V α where
  support := T
  eval φ := F.eval (restrictRestricted hFT φ)

@[simp] theorem globalEval_extendSupport (F : LocalFunctional Site V α)
    {T : Finset Site} (hFT : F.support ⊆ T) (φ : ∀ x, V x) :
    (F.extendSupport hFT).globalEval φ = F.globalEval φ := rfl

/-- Sum of two local functionals, supported on the union. -/
def add [DecidableEq Site] [Add α] (F G : LocalFunctional Site V α) :
    LocalFunctional Site V α where
  support := F.support ∪ G.support
  eval φ :=
    F.eval (restrictRestricted (by intro x hx; exact Finset.mem_union_left _ hx) φ) +
    G.eval (restrictRestricted (by intro x hx; exact Finset.mem_union_right _ hx) φ)

@[simp] theorem globalEval_add [DecidableEq Site] [Add α] (F G : LocalFunctional Site V α)
    (φ : ∀ x, V x) :
    (F.add G).globalEval φ = F.globalEval φ + G.globalEval φ := rfl

/-- Product of two local functionals, supported on the union. -/
def mul [DecidableEq Site] [Mul α] (F G : LocalFunctional Site V α) :
    LocalFunctional Site V α where
  support := F.support ∪ G.support
  eval φ :=
    F.eval (restrictRestricted (by intro x hx; exact Finset.mem_union_left _ hx) φ) *
    G.eval (restrictRestricted (by intro x hx; exact Finset.mem_union_right _ hx) φ)

@[simp] theorem globalEval_mul [DecidableEq Site] [Mul α] (F G : LocalFunctional Site V α)
    (φ : ∀ x, V x) :
    (F.mul G).globalEval φ = F.globalEval φ * G.globalEval φ := rfl

/-- Finite product of local functionals, supported on the union of their
supports.  This is the product constructor needed by Mayer-cover activities. -/
noncomputable def finsetProd [DecidableEq Site] [CommMonoid α] {ι : Type*}
    (I : Finset ι) (F : ι → LocalFunctional Site V α) :
    LocalFunctional Site V α where
  support := I.biUnion fun i => (F i).support
  eval φ :=
    ∏ i : {i // i ∈ I},
      (F i.1).eval
        (restrictRestricted
          (by
            intro x hx
            exact Finset.mem_biUnion.mpr ⟨i.1, i.2, hx⟩)
          φ)

@[simp] theorem globalEval_finsetProd [DecidableEq Site] [CommMonoid α]
    {ι : Type*} (I : Finset ι) (F : ι → LocalFunctional Site V α)
    (φ : ∀ x, V x) :
    (finsetProd I F).globalEval φ =
      ∏ i : {i // i ∈ I}, (F i.1).globalEval φ := rfl

end LocalFunctional

/-- A two-field local activity, with separate spectator and fluctuation
supports.  This mirrors the Appendix-F shape while keeping both dependencies
type-local. -/
structure LocalActivity (Site : Type*) (Ψ Φ : Site → Type*) (α : Type*) where
  spectatorSupport : Finset Site
  fluctuationSupport : Finset Site
  eval :
    RestrictedField spectatorSupport Ψ →
    RestrictedField fluctuationSupport Φ →
    α

namespace LocalActivity

variable {Site : Type*} {Ψ Φ : Site → Type*} {α β : Type*}

/-- Adapt a two-field local activity back to global spectator/fluctuation
fields. -/
def globalEval (F : LocalActivity Site Ψ Φ α)
    (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x) : α :=
  F.eval (restrictGlobal F.spectatorSupport ψ)
    (restrictGlobal F.fluctuationSupport φ)

theorem globalEval_eq_of_agreeOn (F : LocalActivity Site Ψ Φ α)
    {ψ₁ ψ₂ : ∀ x, Ψ x} {φ₁ φ₂ : ∀ x, Φ x}
    (hψ : AgreeOn F.spectatorSupport ψ₁ ψ₂)
    (hφ : AgreeOn F.fluctuationSupport φ₁ φ₂) :
    F.globalEval ψ₁ φ₁ = F.globalEval ψ₂ φ₂ := by
  unfold globalEval
  rw [restrictGlobal_eq_of_agreeOn hψ, restrictGlobal_eq_of_agreeOn hφ]

/-- Postcompose a local activity without changing either support. -/
def map (f : α → β) (F : LocalActivity Site Ψ Φ α) :
    LocalActivity Site Ψ Φ β where
  spectatorSupport := F.spectatorSupport
  fluctuationSupport := F.fluctuationSupport
  eval ψ φ := f (F.eval ψ φ)

@[simp] theorem globalEval_map (f : α → β) (F : LocalActivity Site Ψ Φ α)
    (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x) :
    (F.map f).globalEval ψ φ = f (F.globalEval ψ φ) := rfl

/-- Reindex a local activity along a site map.

The target activity has supports equal to the images of the source supports.
Its evaluation pulls target spectator/fluctuation fields back to the original
source support before applying the source activity. -/
def reindex {Source Target : Type*} [DecidableEq Target]
    {ΨS ΦS : Source → Type*} {ΨT ΦT : Target → Type*}
    (site : Source → Target)
    (pullΨ : ∀ s, ΨT (site s) → ΨS s)
    (pullΦ : ∀ s, ΦT (site s) → ΦS s)
    (F : LocalActivity Source ΨS ΦS α) :
    LocalActivity Target ΨT ΦT α where
  spectatorSupport := F.spectatorSupport.image site
  fluctuationSupport := F.fluctuationSupport.image site
  eval ψ φ :=
    F.eval
      (fun s =>
        pullΨ s.1
          (ψ ⟨site s.1, Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩⟩))
      (fun s =>
        pullΦ s.1
          (φ ⟨site s.1, Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩⟩))

@[simp] theorem spectatorSupport_reindex
    {Source Target : Type*} [DecidableEq Target]
    {ΨS ΦS : Source → Type*} {ΨT ΦT : Target → Type*}
    (site : Source → Target)
    (pullΨ : ∀ s, ΨT (site s) → ΨS s)
    (pullΦ : ∀ s, ΦT (site s) → ΦS s)
    (F : LocalActivity Source ΨS ΦS α) :
    (F.reindex site pullΨ pullΦ).spectatorSupport =
      F.spectatorSupport.image site := rfl

@[simp] theorem fluctuationSupport_reindex
    {Source Target : Type*} [DecidableEq Target]
    {ΨS ΦS : Source → Type*} {ΨT ΦT : Target → Type*}
    (site : Source → Target)
    (pullΨ : ∀ s, ΨT (site s) → ΨS s)
    (pullΦ : ∀ s, ΦT (site s) → ΦS s)
    (F : LocalActivity Source ΨS ΦS α) :
    (F.reindex site pullΨ pullΦ).fluctuationSupport =
      F.fluctuationSupport.image site := rfl

@[simp] theorem globalEval_reindex
    {Source Target : Type*} [DecidableEq Target]
    {ΨS ΦS : Source → Type*} {ΨT ΦT : Target → Type*}
    (site : Source → Target)
    (pullΨ : ∀ s, ΨT (site s) → ΨS s)
    (pullΦ : ∀ s, ΦT (site s) → ΦS s)
    (F : LocalActivity Source ΨS ΦS α)
    (ψ : ∀ t, ΨT t) (φ : ∀ t, ΦT t) :
    (F.reindex site pullΨ pullΦ).globalEval ψ φ =
      F.globalEval
        (fun s => pullΨ s (ψ (site s)))
        (fun s => pullΦ s (φ (site s))) := rfl

/-- Product of two local activities, supported on the union in both field
families. -/
def mul [DecidableEq Site] [Mul α] (F G : LocalActivity Site Ψ Φ α) :
    LocalActivity Site Ψ Φ α where
  spectatorSupport := F.spectatorSupport ∪ G.spectatorSupport
  fluctuationSupport := F.fluctuationSupport ∪ G.fluctuationSupport
  eval ψ φ :=
    F.eval
      (restrictRestricted (by intro x hx; exact Finset.mem_union_left _ hx) ψ)
      (restrictRestricted (by intro x hx; exact Finset.mem_union_left _ hx) φ) *
    G.eval
      (restrictRestricted (by intro x hx; exact Finset.mem_union_right _ hx) ψ)
      (restrictRestricted (by intro x hx; exact Finset.mem_union_right _ hx) φ)

@[simp] theorem globalEval_mul [DecidableEq Site] [Mul α] (F G : LocalActivity Site Ψ Φ α)
    (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x) :
    (F.mul G).globalEval ψ φ = F.globalEval ψ φ * G.globalEval ψ φ := rfl

/-- Finite product of two-field local activities, supported on the union of
spectator supports and the union of fluctuation supports. -/
noncomputable def finsetProd [DecidableEq Site] [CommMonoid α] {ι : Type*}
    (I : Finset ι) (F : ι → LocalActivity Site Ψ Φ α) :
    LocalActivity Site Ψ Φ α where
  spectatorSupport := I.biUnion fun i => (F i).spectatorSupport
  fluctuationSupport := I.biUnion fun i => (F i).fluctuationSupport
  eval ψ φ :=
    ∏ i : {i // i ∈ I},
      (F i.1).eval
        (restrictRestricted
          (by
            intro x hx
            exact Finset.mem_biUnion.mpr ⟨i.1, i.2, hx⟩)
          ψ)
        (restrictRestricted
          (by
            intro x hx
            exact Finset.mem_biUnion.mpr ⟨i.1, i.2, hx⟩)
          φ)

@[simp] theorem globalEval_finsetProd [DecidableEq Site] [CommMonoid α]
    {ι : Type*} (I : Finset ι) (F : ι → LocalActivity Site Ψ Φ α)
    (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x) :
    (finsetProd I F).globalEval ψ φ =
      ∏ i : {i // i ∈ I}, (F i.1).globalEval ψ φ := rfl

/-- Finite sum of two-field local activities, supported on the union of the
spectator supports and the union of the fluctuation supports. -/
noncomputable def finsetSum [DecidableEq Site] [AddCommMonoid α] {ι : Type*}
    (I : Finset ι) (F : ι → LocalActivity Site Ψ Φ α) :
    LocalActivity Site Ψ Φ α where
  spectatorSupport := I.biUnion fun i => (F i).spectatorSupport
  fluctuationSupport := I.biUnion fun i => (F i).fluctuationSupport
  eval ψ φ :=
    ∑ i : {i // i ∈ I},
      (F i.1).eval
        (restrictRestricted
          (by
            intro x hx
            exact Finset.mem_biUnion.mpr ⟨i.1, i.2, hx⟩)
          ψ)
        (restrictRestricted
          (by
            intro x hx
            exact Finset.mem_biUnion.mpr ⟨i.1, i.2, hx⟩)
          φ)

@[simp] theorem globalEval_finsetSum [DecidableEq Site] [AddCommMonoid α]
    {ι : Type*} (I : Finset ι) (F : ι → LocalActivity Site Ψ Φ α)
    (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x) :
    (finsetSum I F).globalEval ψ φ =
      ∑ i ∈ I, (F i).globalEval ψ φ := by
  change (∑ i : {i // i ∈ I}, (F i.1).globalEval ψ φ) =
    ∑ i ∈ I, (F i).globalEval ψ φ
  simpa using
    (Finset.sum_attach I (fun i : ι => (F i).globalEval ψ φ))

/-- Integrate the fluctuation field of a two-field local activity against an
ultralocal product measure, leaving a spectator-field local functional. -/
noncomputable def integrateFluctuation
    {β : Type*} [Fintype Site] [MeasurableSpace β]
    (F : LocalActivity Site Ψ (fun _ => β) ℂ) (μ : Measure β) :
    LocalFunctional Site Ψ ℂ where
  support := F.spectatorSupport
  eval ψ :=
    ∫ φ : (∀ _ : Site, β),
      F.eval ψ (restrictGlobal F.fluctuationSupport φ)
      ∂(Measure.pi fun _ : Site => μ)

@[simp] theorem globalEval_integrateFluctuation
    {β : Type*} [Fintype Site] [MeasurableSpace β]
    (F : LocalActivity Site Ψ (fun _ => β) ℂ) (μ : Measure β)
    (ψ : ∀ x, Ψ x) :
    (F.integrateFluctuation μ).globalEval ψ =
      ∫ φ : (∀ _ : Site, β), F.globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ) := rfl

/-- A uniform pointwise bound on a local activity bounds its integrated
fluctuation functional.  The explicit `Integrable` hypothesis is carried in
the interface so later Appendix-F statements do not silently rely on Lean's
default value for non-integrable integrals. -/
theorem norm_globalEval_integrateFluctuation_le_of_norm_le
    {β : Type*} [Fintype Site] [MeasurableSpace β]
    (μ : Measure β) [IsProbabilityMeasure μ]
    (F : LocalActivity Site Ψ (fun _ => β) ℂ)
    (ψ : ∀ x, Ψ x) {B : ℝ}
    (_hint : Integrable (fun φ => F.globalEval ψ φ)
      (Measure.pi fun _ : Site => μ))
    (hB : ∀ φ, ‖F.globalEval ψ φ‖ ≤ B) :
    ‖(F.integrateFluctuation μ).globalEval ψ‖ ≤ B := by
  have hconst := norm_integral_le_of_norm_le_const
    (μ := Measure.pi fun _ : Site => μ)
    (Filter.Eventually.of_forall hB)
  simpa using hconst

end LocalActivity

end YangMills.RG
