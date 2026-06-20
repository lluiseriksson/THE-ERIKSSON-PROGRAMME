/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.RawMayerWithHoles
import YangMills.RG.ModifiedMetric

/-!
# Ω-connected Mayer covers

This file packages the next algebraic layer of a Dimock-F.1-style
with-holes compiler.

For an abstract finite family of local activities, it defines:

* the Ω-overlap graph on cover indices, where two pieces touch if their active
  supports overlap inside Ω;
* the predicate that the chosen index set is connected in that graph;
* the finite product of raw Mayer activities `∏ᵢ (exp Hᵢ - 1)` as a
  type-local `LocalActivity`, with support equal to the union of the supports
  of the factors.

Honest scope: Ω-connectedness is recorded as the source-shaped combinatorial
condition, but no quantitative Appendix-F loss, ultralocal integration,
renormalized effective activity, or Yang--Mills activity-decay theorem is
proved here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped BigOperators

/-- The index graph of an Ω-cover: two cover pieces are adjacent when their
declared active supports intersect inside Ω. -/
def omegaOverlapGraph {Site ι : Type*} [DecidableEq Site]
    (Ω : Finset Site) (activeSupport : ι → Finset Site) : SimpleGraph ι where
  Adj i j :=
    i ≠ j ∧ ¬ Disjoint (Ω ∩ activeSupport i) (Ω ∩ activeSupport j)
  symm := by
    intro i j h
    exact ⟨h.1.symm, by simpa [disjoint_comm] using h.2⟩
  loopless := ⟨fun i h => h.1 rfl⟩

@[simp] theorem omegaOverlapGraph_adj_iff {Site ι : Type*} [DecidableEq Site]
    (Ω : Finset Site) (activeSupport : ι → Finset Site) (i j : ι) :
    (omegaOverlapGraph Ω activeSupport).Adj i j ↔
      i ≠ j ∧ ¬ Disjoint (Ω ∩ activeSupport i) (Ω ∩ activeSupport j) :=
  Iff.rfl

/-- A finite index set is Ω-connected if it is walk-connected in the
Ω-overlap graph induced by the declared active supports. -/
def omegaConnectedIndex {Site ι : Type*} [DecidableEq Site]
    (Ω : Finset Site) (I : Finset ι) (activeSupport : ι → Finset Site) : Prop :=
  walkConnected (omegaOverlapGraph Ω activeSupport) I

/-- Source-shaped package for a finite Ω-connected cover.  The active support
need not coincide with the full field-dependency support of a `LocalActivity`;
in Appendix-F applications it is the part of a polymer visible inside Ω. -/
structure OmegaConnectedCover (Site ι : Type*) [DecidableEq Site] where
  index : Finset ι
  omega : Finset Site
  activeSupport : ι → Finset Site
  connected : omegaConnectedIndex omega index activeSupport

namespace LocalActivity

variable {Site : Type*} [DecidableEq Site] {Ψ Φ : Site → Type*} {ι : Type*}

/-- The finite product of raw Mayer activities over a cover index set. -/
noncomputable def mayerCoverActivity (I : Finset ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ) : LocalActivity Site Ψ Φ ℂ :=
  finsetProd I fun i => (H i).rawMayer

@[simp] theorem mayerCoverActivity_spectatorSupport (I : Finset ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ) :
    (mayerCoverActivity I H).spectatorSupport =
      I.biUnion fun i => (H i).spectatorSupport :=
  rfl

@[simp] theorem mayerCoverActivity_fluctuationSupport (I : Finset ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ) :
    (mayerCoverActivity I H).fluctuationSupport =
      I.biUnion fun i => (H i).fluctuationSupport :=
  rfl

/-- If each factor's fluctuation support is contained in its declared
`Ω`-active support, then the whole Mayer-cover product has fluctuation support
contained in the union of those declared active supports inside `Ω`.  This is
the finite support-lifting step a source compiler needs before applying the
Ω-component factorization layer. -/
theorem mayerCoverActivity_fluctuationSupport_subset_omega_biUnion_activeSupport
    (I : Finset ι) (H : ι → LocalActivity Site Ψ Φ ℂ)
    (Ω : Finset Site) (activeSupport : ι → Finset Site)
    (hsub : ∀ i, i ∈ I → (H i).fluctuationSupport ⊆ Ω ∩ activeSupport i) :
    (mayerCoverActivity I H).fluctuationSupport ⊆
      Ω ∩ I.biUnion activeSupport := by
  rw [mayerCoverActivity_fluctuationSupport]
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
  have hxsub := hsub i hi hxi
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxsub).1,
    Finset.mem_biUnion.mpr ⟨i, hi, (Finset.mem_inter.mp hxsub).2⟩⟩

@[simp] theorem globalEval_mayerCoverActivity (I : Finset ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ)
    (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x) :
    (mayerCoverActivity I H).globalEval ψ φ =
      ∏ i : {i // i ∈ I}, (Complex.exp ((H i.1).globalEval ψ φ) - 1) := by
  simp [mayerCoverActivity]

/-- The Mayer cover product remains insensitive to off-support changes in both
field families, with supports equal to the corresponding support unions. -/
theorem mayerCoverActivity_globalEval_eq_of_agreeOn (I : Finset ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ)
    {ψ₁ ψ₂ : ∀ x, Ψ x} {φ₁ φ₂ : ∀ x, Φ x}
    (hψ : AgreeOn (I.biUnion fun i => (H i).spectatorSupport) ψ₁ ψ₂)
    (hφ : AgreeOn (I.biUnion fun i => (H i).fluctuationSupport) φ₁ φ₂) :
    (mayerCoverActivity I H).globalEval ψ₁ φ₁ =
      (mayerCoverActivity I H).globalEval ψ₂ φ₂ := by
  exact (mayerCoverActivity I H).globalEval_eq_of_agreeOn hψ hφ

end LocalActivity

namespace OmegaConnectedCover

variable {Site : Type*} [DecidableEq Site] {Ψ Φ : Site → Type*} {ι : Type*}

/-- The local Mayer product associated to an Ω-connected cover.  The
connectedness certificate is carried by `C`; the support algebra itself is the
finite-product algebra of `LocalActivity`. -/
noncomputable def mayerActivity (C : OmegaConnectedCover Site ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ) : LocalActivity Site Ψ Φ ℂ :=
  LocalActivity.mayerCoverActivity C.index H

@[simp] theorem mayerActivity_spectatorSupport (C : OmegaConnectedCover Site ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ) :
    (C.mayerActivity H).spectatorSupport =
      C.index.biUnion fun i => (H i).spectatorSupport :=
  rfl

@[simp] theorem mayerActivity_fluctuationSupport (C : OmegaConnectedCover Site ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ) :
    (C.mayerActivity H).fluctuationSupport =
      C.index.biUnion fun i => (H i).fluctuationSupport :=
  rfl

/-- Cover-facing form of
`LocalActivity.mayerCoverActivity_fluctuationSupport_subset_omega_biUnion_activeSupport`. -/
theorem mayerActivity_fluctuationSupport_subset_omega_biUnion_activeSupport
    (C : OmegaConnectedCover Site ι) (H : ι → LocalActivity Site Ψ Φ ℂ)
    (hsub : ∀ i, i ∈ C.index →
      (H i).fluctuationSupport ⊆ C.omega ∩ C.activeSupport i) :
    (C.mayerActivity H).fluctuationSupport ⊆
      C.omega ∩ C.index.biUnion C.activeSupport := by
  exact LocalActivity.mayerCoverActivity_fluctuationSupport_subset_omega_biUnion_activeSupport
    C.index H C.omega C.activeSupport hsub

@[simp] theorem globalEval_mayerActivity (C : OmegaConnectedCover Site ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ)
    (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x) :
    (C.mayerActivity H).globalEval ψ φ =
      ∏ i : {i // i ∈ C.index}, (Complex.exp ((H i.1).globalEval ψ φ) - 1) := by
  simp [mayerActivity]

theorem mayerActivity_globalEval_eq_of_agreeOn (C : OmegaConnectedCover Site ι)
    (H : ι → LocalActivity Site Ψ Φ ℂ)
    {ψ₁ ψ₂ : ∀ x, Ψ x} {φ₁ φ₂ : ∀ x, Φ x}
    (hψ : AgreeOn (C.index.biUnion fun i => (H i).spectatorSupport) ψ₁ ψ₂)
    (hφ : AgreeOn (C.index.biUnion fun i => (H i).fluctuationSupport) φ₁ φ₂) :
    (C.mayerActivity H).globalEval ψ₁ φ₁ =
      (C.mayerActivity H).globalEval ψ₂ φ₂ := by
  exact LocalActivity.mayerCoverActivity_globalEval_eq_of_agreeOn C.index H hψ hφ

end OmegaConnectedCover

end YangMills.RG
