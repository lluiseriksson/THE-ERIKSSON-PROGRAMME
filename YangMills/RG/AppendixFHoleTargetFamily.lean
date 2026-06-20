/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHoleTarget

/-!
# Appendix F: target families for Ω-active hole covers

This module completes the finite two-support target-family reindexing for the
source-facing with-holes carrier.

For `omegaHolePolymerSystem`, a connected raw cover uses
`skeleton HF X.val` for Ω-connectivity/admissibility, but its target label is
the full union `X.val`.  The target family is therefore hard-core only through
the active skeleton of the full target, not through full-target disjointness.

The main result is the exact finite identity

```
∏ i ∈ Λ, (1 + w i)
  =
∑ admissible full-target families Υ,
  ∏ Y ∈ Υ, K_w(Y),
```

where `K_w(Y)` sums all skeleton-connected raw covers whose full union is `Y`.
This is the source-shaped finite Mayer/Fubini part of Dimock Appendix F
(639)--(640).  It is still finite algebra only: no metric estimate, no
ultralocal integration, no second Ursell expansion, and no Yang-Mills
activity-decay theorem are proved here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open Finset
open scoped BigOperators

/-- The first connected Mayer activity for source-facing hole targets.  Covers
are connected through active skeletons; the target `Y` is the union of the full
hole-polymers. -/
noncomputable def appendixFHoleConnectedMayerActivity
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (w : OmegaPolymerType HF z → ℂ)
    (Y : Finset (Cube d L)) : ℂ :=
  appendixFConnectedMayerActivity
    (Finset.univ : Finset (Cube d L))
    (fun X : OmegaPolymerType HF z => skeleton HF X.val)
    (fun X : OmegaPolymerType HF z => X.val)
    Λ w Y

/-- Full-target families admitted by the source-facing Appendix-F hard-core
relation.  Targets are full hole-polymers, but incompatibility is disjointness
of their active skeletons. -/
noncomputable def appendixFHoleAdmissibleTargetFamilies
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z)) :
    Finset (Finset (Finset (Cube d L))) :=
  (appendixFTargetRegion
    (Finset.univ : Finset (Cube d L))
    (fun X : OmegaPolymerType HF z => skeleton HF X.val)
    (fun X : OmegaPolymerType HF z => X.val)
    Λ).powerset.filter fun targets =>
      ∀ Y ∈ targets, ∀ Z ∈ targets, Y ≠ Z →
        Disjoint (skeleton HF Y) (skeleton HF Z)

@[simp] theorem mem_appendixFHoleAdmissibleTargetFamilies_iff
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (targets : Finset (Finset (Cube d L))) :
    targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ ↔
      targets ⊆ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)
        (fun X : OmegaPolymerType HF z => X.val)
        Λ ∧
      ∀ Y ∈ targets, ∀ Z ∈ targets, Y ≠ Z →
        Disjoint (skeleton HF Y) (skeleton HF Z) := by
  classical
  simp [appendixFHoleAdmissibleTargetFamilies]

/-- The explicit finite choice domain: an admissible full-target family
together with one skeleton-connected raw cover in each full-target fiber. -/
noncomputable def appendixFHoleAdmissibleTargetChoices
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z)) :
    Finset (Σ targets : Finset (Finset (Cube d L)),
      ∀ Y, Y ∈ targets → Finset (OmegaPolymerType HF z)) :=
  (appendixFHoleAdmissibleTargetFamilies HF z Λ).sigma fun targets =>
    targets.pi fun Y =>
      appendixFTargetFiber
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)
        (fun X : OmegaPolymerType HF z => X.val)
        Λ Y

@[simp] theorem mem_appendixFHoleAdmissibleTargetChoices_iff
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (choice : Σ targets : Finset (Finset (Cube d L)),
      ∀ Y, Y ∈ targets → Finset (OmegaPolymerType HF z)) :
    choice ∈ appendixFHoleAdmissibleTargetChoices HF z Λ ↔
      choice.1 ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ ∧
      ∀ Y hY, choice.2 Y hY ∈ appendixFTargetFiber
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)
        (fun X : OmegaPolymerType HF z => X.val)
        Λ Y := by
  classical
  simp [appendixFHoleAdmissibleTargetChoices]

theorem appendixFHoleTargetChoiceCoverFamily_mem_admissible
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {choice : Σ targets : Finset (Finset (Cube d L)),
      ∀ Y, Y ∈ targets → Finset (OmegaPolymerType HF z)}
    (hchoice : choice ∈ appendixFHoleAdmissibleTargetChoices HF z Λ) :
    appendixFTargetChoiceCoverFamily choice ∈
      appendixFAdmissibleConnectedCoverFamilies
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)
        Λ := by
  classical
  rw [mem_appendixFAdmissibleConnectedCoverFamilies_iff]
  rw [mem_appendixFHoleAdmissibleTargetChoices_iff] at hchoice
  refine ⟨?_, ?_⟩
  · intro C hC
    rw [appendixFTargetChoiceCoverFamily] at hC
    rcases Finset.mem_image.mp hC with ⟨Y, _hY, rfl⟩
    exact ((mem_appendixFTargetFiber_iff
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y.1 (choice.2 Y.1 Y.2)).mp (hchoice.2 Y.1 Y.2)).1
  · intro C hC D hD hCD
    rw [appendixFTargetChoiceCoverFamily] at hC hD
    rcases Finset.mem_image.mp hC with ⟨Y, _hY, rfl⟩
    rcases Finset.mem_image.mp hD with ⟨Z, _hZ, rfl⟩
    have hYfiber := (mem_appendixFTargetFiber_iff
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y.1 (choice.2 Y.1 Y.2)).mp (hchoice.2 Y.1 Y.2)
    have hZfiber := (mem_appendixFTargetFiber_iff
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Z.1 (choice.2 Z.1 Z.2)).mp (hchoice.2 Z.1 Z.2)
    have hYZ : Y.1 ≠ Z.1 := by
      intro hval
      have hYZsub : Y = Z := Subtype.ext hval
      exact hCD (by subst Z; rfl)
    have htarget :=
      ((mem_appendixFHoleAdmissibleTargetFamilies_iff HF z Λ choice.1).mp
        hchoice.1).2 Y.1 Y.2 Z.1 Z.2 hYZ
    have hCskel :
        appendixFCoverUnion
          (fun X : OmegaPolymerType HF z => skeleton HF X.val)
          (choice.2 Y.1 Y.2) = skeleton HF Y.1 := by
      calc
        appendixFCoverUnion
            (fun X : OmegaPolymerType HF z => skeleton HF X.val)
            (choice.2 Y.1 Y.2)
            = skeleton HF
                (appendixFCoverUnion
                  (fun X : OmegaPolymerType HF z => X.val)
                  (choice.2 Y.1 Y.2)) := by
              exact (appendixFHoleCoverUnion_skeleton HF z
                (choice.2 Y.1 Y.2)).symm
        _ = skeleton HF Y.1 := by rw [hYfiber.2]
    have hDskel :
        appendixFCoverUnion
          (fun X : OmegaPolymerType HF z => skeleton HF X.val)
          (choice.2 Z.1 Z.2) = skeleton HF Z.1 := by
      calc
        appendixFCoverUnion
            (fun X : OmegaPolymerType HF z => skeleton HF X.val)
            (choice.2 Z.1 Z.2)
            = skeleton HF
                (appendixFCoverUnion
                  (fun X : OmegaPolymerType HF z => X.val)
                  (choice.2 Z.1 Z.2)) := by
              exact (appendixFHoleCoverUnion_skeleton HF z
                (choice.2 Z.1 Z.2)).symm
        _ = skeleton HF Z.1 := by rw [hZfiber.2]
    simpa [hCskel, hDskel] using htarget

theorem appendixFCoverFamilyWeight_holeTargetChoiceCoverFamily_eq
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (w : OmegaPolymerType HF z → ℂ)
    {choice : Σ targets : Finset (Finset (Cube d L)),
      ∀ Y, Y ∈ targets → Finset (OmegaPolymerType HF z)}
    (hchoice : choice ∈ appendixFHoleAdmissibleTargetChoices HF z Λ) :
    appendixFCoverFamilyWeight w (appendixFTargetChoiceCoverFamily choice) =
      ∏ Y ∈ choice.1.attach, ∏ i ∈ choice.2 Y.1 Y.2, w i := by
  classical
  rw [mem_appendixFHoleAdmissibleTargetChoices_iff] at hchoice
  unfold appendixFCoverFamilyWeight appendixFComponentWeight
    appendixFTargetChoiceCoverFamily
  rw [Finset.prod_image]
  intro Y _hY Z _hZ hYZ
  apply Subtype.ext
  have hYfiber := (mem_appendixFTargetFiber_iff
    (Finset.univ : Finset (Cube d L))
    (fun X : OmegaPolymerType HF z => skeleton HF X.val)
    (fun X : OmegaPolymerType HF z => X.val)
    Λ Y.1 (choice.2 Y.1 Y.2)).mp (hchoice.2 Y.1 Y.2)
  have hZfiber := (mem_appendixFTargetFiber_iff
    (Finset.univ : Finset (Cube d L))
    (fun X : OmegaPolymerType HF z => skeleton HF X.val)
    (fun X : OmegaPolymerType HF z => X.val)
    Λ Z.1 (choice.2 Z.1 Z.2)).mp (hchoice.2 Z.1 Z.2)
  have hcover :
      appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val)
          (choice.2 Y.1 Y.2) =
        appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val)
          (choice.2 Z.1 Z.2) := by
    exact congrArg
      (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val)) hYZ
  exact hYfiber.2.symm.trans (hcover.trans hZfiber.2)

theorem image_fullCoverUnion_mem_appendixFHoleAdmissibleTargetFamilies
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Γ : Finset (Finset (OmegaPolymerType HF z))}
    (hΓ : Γ ∈ appendixFAdmissibleConnectedCoverFamilies
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      Λ) :
    Γ.image (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val)) ∈
      appendixFHoleAdmissibleTargetFamilies HF z Λ := by
  classical
  rw [mem_appendixFHoleAdmissibleTargetFamilies_iff]
  rw [mem_appendixFAdmissibleConnectedCoverFamilies_iff] at hΓ
  refine ⟨?_, ?_⟩
  · intro Y hY
    rcases Finset.mem_image.mp hY with ⟨C, hC, rfl⟩
    exact Finset.mem_image.mpr ⟨C, hΓ.1 hC, rfl⟩
  · intro Y hY Z hZ hYZ
    rcases Finset.mem_image.mp hY with ⟨C, hC, rfl⟩
    rcases Finset.mem_image.mp hZ with ⟨D, hD, rfl⟩
    have hCD : C ≠ D := by
      intro hCD
      exact hYZ (by simp [hCD])
    have hdisj := hΓ.2 C hC D hD hCD
    have hCskel :
        skeleton HF
          (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C) =
        appendixFCoverUnion (fun X : OmegaPolymerType HF z => skeleton HF X.val) C :=
      appendixFHoleCoverUnion_skeleton HF z C
    have hDskel :
        skeleton HF
          (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) D) =
        appendixFCoverUnion (fun X : OmegaPolymerType HF z => skeleton HF X.val) D :=
      appendixFHoleCoverUnion_skeleton HF z D
    simpa [hCskel, hDskel] using hdisj

/-- The inverse finite Fubini datum for a source-facing admissible connected
cover family: full targets are the full cover unions, and each full target
chooses one connected cover from its fiber. -/
noncomputable def appendixFHoleConnectedCoverFamilyTargetChoiceSigma
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Γ : Finset (Finset (OmegaPolymerType HF z))) :
    Σ targets : Finset (Finset (Cube d L)),
      ∀ Y, Y ∈ targets → Finset (OmegaPolymerType HF z) :=
  appendixFConnectedCoverFamilyTargetChoiceSigma
    (fun X : OmegaPolymerType HF z => X.val) Γ

theorem appendixFHoleConnectedCoverFamilyTargetChoiceSigma_mem_choices
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Γ : Finset (Finset (OmegaPolymerType HF z))}
    (hΓ : Γ ∈ appendixFAdmissibleConnectedCoverFamilies
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      Λ) :
    appendixFHoleConnectedCoverFamilyTargetChoiceSigma HF z Γ ∈
      appendixFHoleAdmissibleTargetChoices HF z Λ := by
  classical
  rw [mem_appendixFHoleAdmissibleTargetChoices_iff]
  refine ⟨image_fullCoverUnion_mem_appendixFHoleAdmissibleTargetFamilies
    HF z Λ hΓ, ?_⟩
  intro Y hY
  change
    (appendixFConnectedCoverFamilyTargetChoiceSigma
      (fun X : OmegaPolymerType HF z => X.val) Γ).2 Y hY ∈
      appendixFTargetFiber
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)
        (fun X : OmegaPolymerType HF z => X.val)
        Λ Y
  rw [mem_appendixFTargetFiber_iff]
  have hspec :=
    appendixFConnectedCoverFamilyTargetChoice_spec
      (fun X : OmegaPolymerType HF z => X.val) Γ Y hY
  rw [mem_appendixFAdmissibleConnectedCoverFamilies_iff] at hΓ
  exact ⟨hΓ.1 hspec.1, hspec.2⟩

theorem appendixFHoleTargetChoiceCoverFamily_image_fullCoverUnion_eq
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {choice : Σ targets : Finset (Finset (Cube d L)),
      ∀ Y, Y ∈ targets → Finset (OmegaPolymerType HF z)}
    (hchoice : choice ∈ appendixFHoleAdmissibleTargetChoices HF z Λ) :
    (appendixFTargetChoiceCoverFamily choice).image
        (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val)) =
      choice.1 := by
  classical
  rw [mem_appendixFHoleAdmissibleTargetChoices_iff] at hchoice
  ext Y
  constructor
  · intro hY
    rcases Finset.mem_image.mp hY with ⟨C, hC, hCY⟩
    rw [appendixFTargetChoiceCoverFamily] at hC
    rcases Finset.mem_image.mp hC with ⟨Z, _hZ, hZC⟩
    have hZfiber := (mem_appendixFTargetFiber_iff
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Z.1 (choice.2 Z.1 Z.2)).mp (hchoice.2 Z.1 Z.2)
    have hYZ : Y = Z.1 := by
      exact hCY.symm.trans
        ((congrArg (appendixFCoverUnion
          (fun X : OmegaPolymerType HF z => X.val)) hZC.symm).trans
          hZfiber.2)
    rw [hYZ]
    exact Z.2
  · intro hY
    refine Finset.mem_image.mpr ⟨choice.2 Y hY, ?_, ?_⟩
    · rw [appendixFTargetChoiceCoverFamily]
      exact Finset.mem_image.mpr ⟨⟨Y, hY⟩, by simp, rfl⟩
    · exact ((mem_appendixFTargetFiber_iff
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)
        (fun X : OmegaPolymerType HF z => X.val)
        Λ Y (choice.2 Y hY)).mp (hchoice.2 Y hY)).2

theorem appendixFHoleTargetChoiceCoverFamily_connectedCoverFamilyTargetChoiceSigma_eq
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Γ : Finset (Finset (OmegaPolymerType HF z))}
    (hΓ : Γ ∈ appendixFAdmissibleConnectedCoverFamilies
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      Λ) :
    appendixFTargetChoiceCoverFamily
      (appendixFHoleConnectedCoverFamilyTargetChoiceSigma HF z Γ) = Γ := by
  classical
  ext C
  constructor
  · intro hC
    rw [appendixFTargetChoiceCoverFamily,
      appendixFHoleConnectedCoverFamilyTargetChoiceSigma,
      appendixFConnectedCoverFamilyTargetChoiceSigma] at hC
    rcases Finset.mem_image.mp hC with ⟨Y, _hY, hCY⟩
    rw [← hCY]
    exact (appendixFConnectedCoverFamilyTargetChoice_spec
      (fun X : OmegaPolymerType HF z => X.val) Γ Y.1 Y.2).1
  · intro hCΓ
    rw [appendixFTargetChoiceCoverFamily,
      appendixFHoleConnectedCoverFamilyTargetChoiceSigma,
      appendixFConnectedCoverFamilyTargetChoiceSigma]
    let Y : Finset (Cube d L) :=
      appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C
    have hY : Y ∈ Γ.image
        (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val)) :=
      Finset.mem_image.mpr ⟨C, hCΓ, rfl⟩
    refine Finset.mem_image.mpr ⟨⟨Y, hY⟩, by simp, ?_⟩
    have hspec :=
      appendixFConnectedCoverFamilyTargetChoice_spec
        (fun X : OmegaPolymerType HF z => X.val) Γ Y hY
    exact appendixFHoleCoverUnion_injective_on_admissibleConnectedCoverFamily
      HF z Λ hΓ hspec.1 hCΓ hspec.2

private theorem cast_forall_mem_finset_apply
    {α β : Type*} [DecidableEq α]
    {A B : Finset α} (h : A = B)
    (f : ∀ x : α, x ∈ A → β) (x : α) (hx : x ∈ B) :
    cast (congrArg (fun U : Finset α => ∀ x : α, x ∈ U → β) h) f x hx =
      f x (by rw [h]; exact hx) := by
  cases h
  rfl

theorem appendixFHoleConnectedCoverFamilyTargetChoiceSigma_targetChoiceCoverFamily_eq
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {choice : Σ targets : Finset (Finset (Cube d L)),
      ∀ Y, Y ∈ targets → Finset (OmegaPolymerType HF z)}
    (hchoice : choice ∈ appendixFHoleAdmissibleTargetChoices HF z Λ) :
    appendixFHoleConnectedCoverFamilyTargetChoiceSigma HF z
      (appendixFTargetChoiceCoverFamily choice) = choice := by
  classical
  cases choice with
  | mk targets rawChoice =>
    let Γ : Finset (Finset (OmegaPolymerType HF z)) :=
      appendixFTargetChoiceCoverFamily (Sigma.mk targets rawChoice)
    have hchoice' : Sigma.mk targets rawChoice ∈
        appendixFHoleAdmissibleTargetChoices HF z Λ := hchoice
    have hΓ : Γ ∈ appendixFAdmissibleConnectedCoverFamilies
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)
        Λ :=
      appendixFHoleTargetChoiceCoverFamily_mem_admissible HF z Λ hchoice'
    have hfirst :
        (appendixFHoleConnectedCoverFamilyTargetChoiceSigma HF z Γ).1 =
          targets := by
      simpa [Γ, appendixFHoleConnectedCoverFamilyTargetChoiceSigma,
        appendixFConnectedCoverFamilyTargetChoiceSigma]
        using appendixFHoleTargetChoiceCoverFamily_image_fullCoverUnion_eq
          HF z Λ hchoice'
    change appendixFHoleConnectedCoverFamilyTargetChoiceSigma HF z Γ =
      Sigma.mk targets rawChoice
    refine Sigma.ext hfirst ?_
    let left := (appendixFHoleConnectedCoverFamilyTargetChoiceSigma HF z Γ).2
    let hty := congrArg (fun U : Finset (Finset (Cube d L)) =>
      ((Y : Finset (Cube d L)) → Y ∈ U → Finset (OmegaPolymerType HF z))) hfirst
    have hcast : cast hty left = rawChoice := by
      funext Y hY
      let hYleft : Y ∈ (appendixFHoleConnectedCoverFamilyTargetChoiceSigma HF z Γ).1 := by
        rw [hfirst]
        exact hY
      have happly : cast hty left Y hY = left Y hYleft := by
        simpa [hty, hYleft] using
          cast_forall_mem_finset_apply
            (α := Finset (Cube d L))
            (β := Finset (OmegaPolymerType HF z))
            hfirst left Y hY
      rw [happly]
      have hspec :=
        appendixFConnectedCoverFamilyTargetChoice_spec
          (fun X : OmegaPolymerType HF z => X.val) Γ Y hYleft
      have hraw_mem : rawChoice Y hY ∈ Γ := by
        dsimp [Γ, appendixFTargetChoiceCoverFamily]
        exact Finset.mem_image.mpr ⟨⟨Y, hY⟩, by simp, rfl⟩
      have hchoice_data :=
        (mem_appendixFHoleAdmissibleTargetChoices_iff HF z Λ
          (Sigma.mk targets rawChoice :
            Sigma (fun targets : Finset (Finset (Cube d L)) =>
              ∀ Y, Y ∈ targets → Finset (OmegaPolymerType HF z)))).mp hchoice'
      have hraw_cover :
          appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val)
            (rawChoice Y hY) = Y :=
        ((mem_appendixFTargetFiber_iff
          (Finset.univ : Finset (Cube d L))
          (fun X : OmegaPolymerType HF z => skeleton HF X.val)
          (fun X : OmegaPolymerType HF z => X.val)
          Λ Y (rawChoice Y hY)).mp (hchoice_data.2 Y hY)).2
      exact appendixFHoleCoverUnion_injective_on_admissibleConnectedCoverFamily
        HF z Λ hΓ hspec.1 hraw_mem (hspec.2.trans hraw_cover.symm)
    exact HEq.trans (HEq.symm (cast_heq hty left)) (heq_of_eq hcast)

theorem sum_appendixFHoleAdmissibleTargetChoices_eq_sum_admissibleConnectedCoverFamilies
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (w : OmegaPolymerType HF z → ℂ) :
    (∑ choice ∈ appendixFHoleAdmissibleTargetChoices HF z Λ,
        ∏ Y ∈ choice.1.attach, ∏ i ∈ choice.2 Y.1 Y.2, w i) =
      ∑ Γ ∈ appendixFAdmissibleConnectedCoverFamilies
          (Finset.univ : Finset (Cube d L))
          (fun X : OmegaPolymerType HF z => skeleton HF X.val)
          Λ,
        appendixFCoverFamilyWeight w Γ := by
  classical
  refine Finset.sum_bij'
    (fun choice _hchoice => appendixFTargetChoiceCoverFamily choice)
    (fun Γ _hΓ => appendixFHoleConnectedCoverFamilyTargetChoiceSigma HF z Γ)
    ?_ ?_ ?_ ?_ ?_
  · intro choice hchoice
    exact appendixFHoleTargetChoiceCoverFamily_mem_admissible HF z Λ hchoice
  · intro Γ hΓ
    exact appendixFHoleConnectedCoverFamilyTargetChoiceSigma_mem_choices HF z Λ hΓ
  · intro choice hchoice
    exact appendixFHoleConnectedCoverFamilyTargetChoiceSigma_targetChoiceCoverFamily_eq
      HF z Λ hchoice
  · intro Γ hΓ
    exact appendixFHoleTargetChoiceCoverFamily_connectedCoverFamilyTargetChoiceSigma_eq
      HF z Λ hΓ
  · intro choice hchoice
    exact (appendixFCoverFamilyWeight_holeTargetChoiceCoverFamily_eq
      HF z Λ w hchoice).symm

theorem sum_appendixFHoleAdmissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_targetChoices
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (w : OmegaPolymerType HF z → ℂ) :
    (∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets, appendixFHoleConnectedMayerActivity HF z Λ w Y) =
      ∑ choice ∈ appendixFHoleAdmissibleTargetChoices HF z Λ,
        ∏ Y ∈ choice.1.attach, ∏ i ∈ choice.2 Y.1 Y.2, w i := by
  classical
  calc
    (∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets, appendixFHoleConnectedMayerActivity HF z Λ w Y)
        =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∑ p ∈ targets.pi (fun Y =>
            appendixFTargetFiber
              (Finset.univ : Finset (Cube d L))
              (fun X : OmegaPolymerType HF z => skeleton HF X.val)
              (fun X : OmegaPolymerType HF z => X.val)
              Λ Y),
          ∏ Y ∈ targets.attach, ∏ i ∈ p Y.1 Y.2, w i := by
        refine Finset.sum_congr rfl ?_
        intro targets _htargets
        exact Finset.prod_sum targets
          (fun Y =>
            appendixFTargetFiber
              (Finset.univ : Finset (Cube d L))
              (fun X : OmegaPolymerType HF z => skeleton HF X.val)
              (fun X : OmegaPolymerType HF z => X.val)
              Λ Y)
          (fun _Y C => ∏ i ∈ C, w i)
    _ =
      ∑ choice ∈ appendixFHoleAdmissibleTargetChoices HF z Λ,
        ∏ Y ∈ choice.1.attach, ∏ i ∈ choice.2 Y.1 Y.2, w i := by
        rw [Finset.sum_sigma']
        rfl

/-- The full two-support source-facing target-family sum equals the
single-support admissible connected-cover-family sum. -/
theorem sum_appendixFHoleAdmissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_admissibleConnectedCoverFamilies
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (w : OmegaPolymerType HF z → ℂ) :
    (∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets, appendixFHoleConnectedMayerActivity HF z Λ w Y) =
      ∑ Γ ∈ appendixFAdmissibleConnectedCoverFamilies
          (Finset.univ : Finset (Cube d L))
          (fun X : OmegaPolymerType HF z => skeleton HF X.val)
          Λ,
        appendixFCoverFamilyWeight w Γ := by
  rw [sum_appendixFHoleAdmissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_targetChoices]
  exact sum_appendixFHoleAdmissibleTargetChoices_eq_sum_admissibleConnectedCoverFamilies
    HF z Λ w

/-- Exact finite two-support Appendix-F target-family identity for the active
with-holes carrier.  Connectivity/admissibility use skeletons; target labels
are full hole-polymer unions. -/
theorem prod_one_add_eq_sum_appendixFHoleAdmissibleTargetFamilies
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (w : OmegaPolymerType HF z → ℂ) :
    (∏ i ∈ Λ, (1 + w i)) =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets, appendixFHoleConnectedMayerActivity HF z Λ w Y := by
  classical
  have hcovers :=
    prod_one_add_eq_sum_appendixFAdmissibleConnectedCoverFamilies
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      Λ w
  exact hcovers.trans
    (sum_appendixFHoleAdmissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_admissibleConnectedCoverFamilies
      HF z Λ w).symm

/-- Exponential specialization of the exact finite two-support target-family
identity. -/
theorem complex_exp_sum_eq_sum_appendixFHoleAdmissibleTargetFamilies
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (h : OmegaPolymerType HF z → ℂ) :
    Complex.exp (∑ i ∈ Λ, h i) =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets,
          appendixFHoleConnectedMayerActivity HF z Λ
            (fun i => Complex.exp (h i) - 1) Y := by
  classical
  rw [Complex.exp_sum]
  have hprod :
      (∏ i ∈ Λ, Complex.exp (h i)) =
        ∏ i ∈ Λ, (1 + (Complex.exp (h i) - 1)) := by
    refine Finset.prod_congr rfl ?_
    intro i _hi
    ring
  rw [hprod]
  exact prod_one_add_eq_sum_appendixFHoleAdmissibleTargetFamilies
    HF z Λ (fun i => Complex.exp (h i) - 1)

end YangMills.RG
