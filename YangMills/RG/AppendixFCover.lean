/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.OmegaConnectedCover
import YangMills.RG.LocalKP

/-!
# Appendix-F target covers

This file adds the finite, cover-facing carrier needed by the Dimock
Appendix-F route: an Ω-connected Mayer cover together with the concrete target
set swept out by its active pieces.

Honest scope: this is a combinatorial and type-local interface.  It does not
prove the Yang--Mills raw activity estimate, the fluctuation integral, the
renormalized effective activity bound, or any continuum/OS statement.  Its job
is to make the finite cover target explicit so later source-derived estimates
can feed the already verified Ω-polymer/KP consumers.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped BigOperators

/-- An Appendix-F target cover is an Ω-connected cover plus the finite target
set equal to the union of active supports in the cover.

The extra `target` field is deliberately redundant: it is the object later
quantitative estimates will measure, while `target_eq` keeps it tied to the
existing Ω-connected-cover algebra. -/
structure OmegaTargetCover (Site ι : Type*) [DecidableEq Site] where
  index : Finset ι
  omega : Finset Site
  activeSupport : ι → Finset Site
  connected : omegaConnectedIndex omega index activeSupport
  target : Finset Site
  nonempty : index.Nonempty
  target_eq : target = index.biUnion activeSupport

namespace OmegaTargetCover

variable {Site : Type*} [DecidableEq Site] {Ψ Φ : Site → Type*} {ι : Type*}

/-- Forget the explicit target and recover the existing Ω-connected cover. -/
def toConnectedCover (C : OmegaTargetCover Site ι) :
    OmegaConnectedCover Site ι where
  index := C.index
  omega := C.omega
  activeSupport := C.activeSupport
  connected := C.connected

@[simp] theorem toConnectedCover_index (C : OmegaTargetCover Site ι) :
    C.toConnectedCover.index = C.index :=
  rfl

@[simp] theorem toConnectedCover_omega (C : OmegaTargetCover Site ι) :
    C.toConnectedCover.omega = C.omega :=
  rfl

@[simp] theorem toConnectedCover_activeSupport (C : OmegaTargetCover Site ι) :
    C.toConnectedCover.activeSupport = C.activeSupport :=
  rfl

/-- Each active support of a member of the cover lies in the target union. -/
theorem activeSupport_subset_target (C : OmegaTargetCover Site ι)
    {i : ι} (hi : i ∈ C.index) :
    C.activeSupport i ⊆ C.target := by
  rw [C.target_eq]
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩

/-- If every active support is inside Ω, then the target itself is inside Ω. -/
theorem target_subset_omega_of_activeSupport_subset (C : OmegaTargetCover Site ι)
    (hsub : ∀ i, i ∈ C.index → C.activeSupport i ⊆ C.omega) :
    C.target ⊆ C.omega := by
  rw [C.target_eq]
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
  exact hsub i hi hxi

/-- A target cover has nonempty target as soon as at least one chosen active
support is nonempty.  The generic structure does not force this because some
source compilers may temporarily carry empty active pieces before pruning. -/
theorem target_nonempty_of_exists_activeSupport_nonempty
    (C : OmegaTargetCover Site ι)
    (h : ∃ i, i ∈ C.index ∧ (C.activeSupport i).Nonempty) :
    C.target.Nonempty := by
  rcases h with ⟨i, hi, x, hx⟩
  rw [C.target_eq]
  exact ⟨x, Finset.mem_biUnion.mpr ⟨i, hi, hx⟩⟩

/-- The Mayer activity attached to a target cover, inherited from the underlying
Ω-connected cover. -/
noncomputable def mayerActivity (C : OmegaTargetCover Site ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ) : LocalActivity Site Ψ Φ ℂ :=
  C.toConnectedCover.mayerActivity H

@[simp] theorem mayerActivity_spectatorSupport (C : OmegaTargetCover Site ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ) :
    (C.mayerActivity H).spectatorSupport =
      C.index.biUnion fun i => (H i).spectatorSupport :=
  rfl

@[simp] theorem mayerActivity_fluctuationSupport (C : OmegaTargetCover Site ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ) :
    (C.mayerActivity H).fluctuationSupport =
      C.index.biUnion fun i => (H i).fluctuationSupport :=
  rfl

/-- Target-cover support lifting: if each factor lives inside its declared
Ω-active support, the finite Mayer product lives inside `Ω ∩ target`. -/
theorem mayerActivity_fluctuationSupport_subset_omega_target
    (C : OmegaTargetCover Site ι) (H : ι → LocalActivity Site Ψ Φ ℂ)
    (hsub : ∀ i, i ∈ C.index →
      (H i).fluctuationSupport ⊆ C.omega ∩ C.activeSupport i) :
    (C.mayerActivity H).fluctuationSupport ⊆ C.omega ∩ C.target := by
  have h := C.toConnectedCover.mayerActivity_fluctuationSupport_subset_omega_biUnion_activeSupport
    H hsub
  simpa [mayerActivity, toConnectedCover, C.target_eq] using h

@[simp] theorem globalEval_mayerActivity (C : OmegaTargetCover Site ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ)
    (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x) :
    (C.mayerActivity H).globalEval ψ φ =
      ∏ i : {i // i ∈ C.index}, (Complex.exp ((H i.1).globalEval ψ φ) - 1) := by
  simp [mayerActivity, toConnectedCover]

/-- Pointwise norm bound inherited from the underlying Ω-connected cover. -/
theorem norm_globalEval_mayerActivity_le_prod_two_of_norm_le
    (C : OmegaTargetCover Site ι) (H : ι → LocalActivity Site Ψ Φ ℂ)
    (A : ι → ℝ) (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x)
    (hA : ∀ i, i ∈ C.index → ‖(H i).globalEval ψ φ‖ ≤ A i)
    (hsmall : ∀ i, i ∈ C.index → A i ≤ 1) :
    ‖(C.mayerActivity H).globalEval ψ φ‖ ≤
      ∏ i : {i // i ∈ C.index}, (2 * A i.1) := by
  exact C.toConnectedCover.norm_globalEval_mayerActivity_le_prod_two_of_norm_le
    H A ψ φ hA hsmall

/-- Uniform-amplitude target-cover form of the Mayer product norm bound. -/
theorem norm_globalEval_mayerActivity_le_two_mul_pow_card_of_norm_le
    (C : OmegaTargetCover Site ι) (H : ι → LocalActivity Site Ψ Φ ℂ)
    (A : ℝ) (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x)
    (hA : ∀ i, i ∈ C.index → ‖(H i).globalEval ψ φ‖ ≤ A)
    (hsmall : A ≤ 1) :
    ‖(C.mayerActivity H).globalEval ψ φ‖ ≤ (2 * A) ^ C.index.card := by
  exact C.toConnectedCover.norm_globalEval_mayerActivity_le_two_mul_pow_card_of_norm_le
    H A ψ φ hA hsmall

/-- Decay-form target-cover bound, with the same cardinality lower-bound
interface as `OmegaConnectedCover`. -/
theorem norm_globalEval_mayerActivity_le_two_mul_pow_of_le_card
    (C : OmegaTargetCover Site ι) (H : ι → LocalActivity Site Ψ Φ ℂ)
    (A : ℝ) (n : ℕ) (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x)
    (hA0 : 0 ≤ A)
    (hA : ∀ i, i ∈ C.index → ‖(H i).globalEval ψ φ‖ ≤ A)
    (hsmall : A ≤ 1) (hcost : 2 * A ≤ 1) (hn : n ≤ C.index.card) :
    ‖(C.mayerActivity H).globalEval ψ φ‖ ≤ (2 * A) ^ n := by
  exact C.toConnectedCover.norm_globalEval_mayerActivity_le_two_mul_pow_of_le_card
    H A n ψ φ hA0 hA hsmall hcost hn

/-- Off-support invariance through the target-cover Mayer product.  The field
support side is still the actual union of fluctuation supports; combine this
with `mayerActivity_fluctuationSupport_subset_omega_target` when an estimate is
phrased only on `Ω ∩ target`. -/
theorem mayerActivity_globalEval_eq_of_agreeOn (C : OmegaTargetCover Site ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ)
    {ψ₁ ψ₂ : ∀ x, Ψ x} {φ₁ φ₂ : ∀ x, Φ x}
    (hψ : AgreeOn (C.index.biUnion fun i => (H i).spectatorSupport) ψ₁ ψ₂)
    (hφ : AgreeOn (C.index.biUnion fun i => (H i).fluctuationSupport) φ₁ φ₂) :
    (C.mayerActivity H).globalEval ψ₁ φ₁ =
      (C.mayerActivity H).globalEval ψ₂ φ₂ := by
  exact C.toConnectedCover.mayerActivity_globalEval_eq_of_agreeOn H hψ hφ

end OmegaTargetCover

/-- Appendix-F target covers specialized to active with-holes polymers. -/
abbrev OmegaPolymerTargetCover {d L : ℕ} [NeZero L] (H : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ) :=
  OmegaTargetCover (Cube d L) (OmegaPolymerType H z)

/-- Build the concrete target cover from a finite Ω-connected family of active
hole-polymers.  Its target is exactly the union of active skeletons. -/
noncomputable def omegaPolymerTargetCover {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (I : Finset (OmegaPolymerType H z))
    (hconn : omegaConnectedIndex (Finset.univ : Finset (Cube d L)) I
      (fun X => skeleton H X.val))
    (hne : I.Nonempty) : OmegaPolymerTargetCover H z where
  index := I
  omega := Finset.univ
  activeSupport := fun X => skeleton H X.val
  connected := hconn
  target := I.biUnion fun X => skeleton H X.val
  nonempty := hne
  target_eq := rfl

@[simp] theorem omegaPolymerTargetCover_target {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (I : Finset (OmegaPolymerType H z))
    (hconn : omegaConnectedIndex (Finset.univ : Finset (Cube d L)) I
      (fun X => skeleton H X.val))
    (hne : I.Nonempty) :
    (omegaPolymerTargetCover H z I hconn hne).target =
      I.biUnion fun X => skeleton H X.val :=
  rfl

/-- Concrete Appendix-F active-polymer target covers have nonempty target:
the index set is nonempty, and each active polymer has nonempty skeleton by
definition of `OmegaPolymerType`. -/
theorem omegaPolymerTargetCover_target_nonempty {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (I : Finset (OmegaPolymerType H z))
    (hconn : omegaConnectedIndex (Finset.univ : Finset (Cube d L)) I
      (fun X => skeleton H X.val))
    (hne : I.Nonempty) :
    (omegaPolymerTargetCover H z I hconn hne).target.Nonempty := by
  rcases hne with ⟨X, hX⟩
  exact (omegaPolymerTargetCover H z I hconn ⟨X, hX⟩).target_nonempty_of_exists_activeSupport_nonempty
    ⟨X, hX, X.property.right.right.right⟩

end YangMills.RG
