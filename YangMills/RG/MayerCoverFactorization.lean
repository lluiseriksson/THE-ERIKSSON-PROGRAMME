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
open SimpleGraph
open scoped BigOperators

/-- Reachability from `r` to `x` by a walk whose support stays inside the
finite index set `K`. -/
def confinedReachable {ι : Type*} (G : SimpleGraph ι) (K : Finset ι)
    (r x : ι) : Prop :=
  ∃ w : G.Walk r x, ∀ y, y ∈ w.support → y ∈ K

/-- The finite component of `r` inside `K`, using only walks whose supports
stay in `K`.  This is noncomputable only because reachability is a proposition
used as a `Finset.filter` predicate. -/
noncomputable def confinedComponent {ι : Type*} (G : SimpleGraph ι)
    (K : Finset ι) (r : ι) : Finset ι := by
  classical
  exact K.filter fun x => confinedReachable G K r x

@[simp]
theorem mem_confinedComponent_iff {ι : Type*} (G : SimpleGraph ι)
    (K : Finset ι) (r x : ι) :
    x ∈ confinedComponent G K r ↔ x ∈ K ∧ confinedReachable G K r x := by
  classical
  simp [confinedComponent]

theorem confinedComponent_subset {ι : Type*} (G : SimpleGraph ι)
    (K : Finset ι) (r : ι) :
    confinedComponent G K r ⊆ K := by
  intro x hx
  exact (mem_confinedComponent_iff G K r x).mp hx |>.1

theorem root_mem_confinedComponent {ι : Type*} (G : SimpleGraph ι)
    (K : Finset ι) {r : ι} (hr : r ∈ K) :
    r ∈ confinedComponent G K r := by
  classical
  rw [mem_confinedComponent_iff]
  refine ⟨hr, ?_⟩
  refine ⟨Walk.nil, ?_⟩
  intro y hy
  rw [Walk.support_nil, List.mem_singleton] at hy
  simpa [hy] using hr

/-- A confined component has no edge from a vertex in the component to a vertex
of `K` outside the component. -/
theorem no_adj_confinedComponent_compl {ι : Type*} (G : SimpleGraph ι)
    (K : Finset ι) {r x y : ι}
    (hx : x ∈ confinedComponent G K r) (hyK : y ∈ K)
    (hy : y ∉ confinedComponent G K r) :
    ¬ G.Adj x y := by
  classical
  intro hxy
  rw [mem_confinedComponent_iff] at hx hy
  rcases hx.2 with ⟨w, hwK⟩
  apply hy
  refine ⟨hyK, ?_⟩
  refine ⟨w.concat hxy, ?_⟩
  intro z hz
  rw [Walk.support_concat, List.concat_eq_append, List.mem_append,
    List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact hwK z hz
  · exact hyK

namespace LocalActivity

/-- Index graph whose edges record overlap of fluctuation supports for a
family of type-local activities.  This is the finite graph a disconnected-cover
compiler can use before handing cross-component disjointness to the
product-measure factorization theorem below. -/
def fluctuationOverlapGraph {Site ι : Type*} [DecidableEq Site]
    {Ψ Φ : Site → Type*} (H : ι → LocalActivity Site Ψ Φ ℂ) :
    SimpleGraph ι where
  Adj i j :=
    i ≠ j ∧ ¬ Disjoint (H i).fluctuationSupport (H j).fluctuationSupport
  symm := by
    intro i j h
    exact ⟨h.1.symm, by simpa [disjoint_comm] using h.2⟩
  loopless := ⟨fun i h => h.1 rfl⟩

@[simp]
theorem fluctuationOverlapGraph_adj_iff
    {Site ι : Type*} [DecidableEq Site]
    {Ψ Φ : Site → Type*} (H : ι → LocalActivity Site Ψ Φ ℂ)
    {i j : ι} :
    (fluctuationOverlapGraph H).Adj i j ↔
      i ≠ j ∧
        ¬ Disjoint (H i).fluctuationSupport (H j).fluctuationSupport :=
  Iff.rfl

/-- If two distinct indices are not adjacent in the fluctuation-overlap graph,
their fluctuation supports are disjoint. -/
theorem fluctuationSupport_disjoint_of_not_adj
    {Site ι : Type*} [DecidableEq Site]
    {Ψ Φ : Site → Type*} (H : ι → LocalActivity Site Ψ Φ ℂ)
    {i j : ι} (hij : i ≠ j)
    (hnadj : ¬ (fluctuationOverlapGraph H).Adj i j) :
    Disjoint (H i).fluctuationSupport (H j).fluctuationSupport := by
  by_contra hdisj
  exact hnadj ⟨hij, hdisj⟩

/-- No cross-edges in the fluctuation-overlap graph give the pairwise
cross-disjointness hypothesis consumed by Mayer-cover factorization. -/
theorem pairwise_disjoint_fluctuationSupport_of_no_cross_adj
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    {Ψ Φ : Site → Type*}
    (I J : Finset ι) (H : ι → LocalActivity Site Ψ Φ ℂ)
    (hIJ : Disjoint I J)
    (hno : ∀ i, i ∈ I → ∀ j, j ∈ J →
      ¬ (fluctuationOverlapGraph H).Adj i j) :
    ∀ i, i ∈ I → ∀ j, j ∈ J →
      Disjoint (H i).fluctuationSupport (H j).fluctuationSupport := by
  intro i hi j hj
  have hij : i ≠ j := by
    intro h
    exact (Finset.disjoint_left.mp hIJ hi) (by simpa [h] using hj)
  exact fluctuationSupport_disjoint_of_not_adj H hij (hno i hi j hj)

/-- Evaluation of a Mayer-cover product over a disjoint union of index sets
splits into the product of the two evaluations. -/
theorem globalEval_mayerCoverActivity_union
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    {Ψ Φ : Site → Type*}
    (I J : Finset ι) (H : ι → LocalActivity Site Ψ Φ ℂ)
    (hIJ : Disjoint I J)
    (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x) :
    (mayerCoverActivity (I ∪ J) H).globalEval ψ φ =
      (mayerCoverActivity I H).globalEval ψ φ *
        (mayerCoverActivity J H).globalEval ψ φ := by
  classical
  let f : ι → ℂ := fun i => Complex.exp ((H i).globalEval ψ φ) - 1
  have hprod : ∏ i ∈ I ∪ J, f i =
      (∏ i ∈ I, f i) * ∏ i ∈ J, f i := by
    exact Finset.prod_union hIJ
  rw [globalEval_mayerCoverActivity, globalEval_mayerCoverActivity,
    globalEval_mayerCoverActivity]
  change (∏ i : {i // i ∈ I ∪ J}, f i.1) =
    (∏ i : {i // i ∈ I}, f i.1) * ∏ i : {i // i ∈ J}, f i.1
  rw [Finset.prod_coe_sort, Finset.prod_coe_sort, Finset.prod_coe_sort]
  exact hprod

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

/-- If a finite Mayer cover splits into two disjoint index blocks whose
fluctuation supports are pairwise disjoint across the split, then the
integrated product over the union factorizes into the product of the two
integrated subproducts. -/
theorem mayerCoverActivity_union_integral_of_pairwise_disjoint_fluctuationSupport
    {Site β ι : Type*} [Fintype Site] [DecidableEq Site] [DecidableEq ι]
    [MeasurableSpace β] [Nonempty β]
    {Ψ : Site → Type*}
    (μ : Measure β) [IsProbabilityMeasure μ]
    (I J : Finset ι)
    (H : ι → LocalActivity Site Ψ (fun _ => β) ℂ)
    (ψ : ∀ x, Ψ x)
    (hIJ : Disjoint I J)
    (hpair : ∀ i, i ∈ I → ∀ j, j ∈ J →
      Disjoint (H i).fluctuationSupport (H j).fluctuationSupport) :
    ∫ φ, (mayerCoverActivity (I ∪ J) H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)
      =
      (∫ φ, (mayerCoverActivity I H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)) *
      ∫ φ, (mayerCoverActivity J H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ) := by
  simpa [globalEval_mayerCoverActivity_union I J H hIJ] using
    mayerCoverActivity_integral_mul_of_pairwise_disjoint_fluctuationSupport
      μ I J H H ψ hpair

/-- Graph-theoretic form of the finite disconnected-cover split: if two
disjoint index blocks have no cross-edge in the fluctuation-overlap graph, then
the integrated Mayer-cover product over their union factorizes. -/
theorem mayerCoverActivity_union_integral_of_no_cross_fluctuationAdj
    {Site β ι : Type*} [Fintype Site] [DecidableEq Site] [DecidableEq ι]
    [MeasurableSpace β] [Nonempty β]
    {Ψ : Site → Type*}
    (μ : Measure β) [IsProbabilityMeasure μ]
    (I J : Finset ι)
    (H : ι → LocalActivity Site Ψ (fun _ => β) ℂ)
    (ψ : ∀ x, Ψ x)
    (hIJ : Disjoint I J)
    (hno : ∀ i, i ∈ I → ∀ j, j ∈ J →
      ¬ (fluctuationOverlapGraph H).Adj i j) :
    ∫ φ, (mayerCoverActivity (I ∪ J) H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)
      =
      (∫ φ, (mayerCoverActivity I H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)) *
      ∫ φ, (mayerCoverActivity J H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ) := by
  exact mayerCoverActivity_union_integral_of_pairwise_disjoint_fluctuationSupport
    μ I J H ψ hIJ
    (pairwise_disjoint_fluctuationSupport_of_no_cross_adj I J H hIJ hno)

/-- Component-extraction form of the finite disconnected-cover split.  Splitting
a finite index set `K` into the confined component of `r` in the
fluctuation-overlap graph and its complement inside `K` gives the Mayer-cover
integral factorization. -/
theorem mayerCoverActivity_integral_split_confinedComponent
    {Site β ι : Type*} [Fintype Site] [DecidableEq Site] [DecidableEq ι]
    [MeasurableSpace β] [Nonempty β]
    {Ψ : Site → Type*}
    (μ : Measure β) [IsProbabilityMeasure μ]
    (K : Finset ι) (r : ι)
    (H : ι → LocalActivity Site Ψ (fun _ => β) ℂ)
    (ψ : ∀ x, Ψ x) :
    let I := confinedComponent (fluctuationOverlapGraph H) K r
    ∫ φ, (mayerCoverActivity K H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)
      =
      (∫ φ, (mayerCoverActivity I H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)) *
      ∫ φ, (mayerCoverActivity (K \ I) H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ) := by
  classical
  let G := fluctuationOverlapGraph H
  let I := confinedComponent G K r
  have hI_sub : I ⊆ K := confinedComponent_subset G K r
  have hIJ : Disjoint I (K \ I) := Finset.disjoint_sdiff
  have hno : ∀ i, i ∈ I → ∀ j, j ∈ K \ I → ¬ G.Adj i j := by
    intro i hi j hj
    exact no_adj_confinedComponent_compl G K hi
      (Finset.mem_sdiff.mp hj).1 (Finset.mem_sdiff.mp hj).2
  have hsplit :=
    mayerCoverActivity_union_integral_of_no_cross_fluctuationAdj
      μ I (K \ I) H ψ hIJ hno
  have hUnion : I ∪ (K \ I) = K := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxI | hxK
      · exact hI_sub hxI
      · exact (Finset.mem_sdiff.mp hxK).1
    · intro hxK
      by_cases hxI : x ∈ I
      · exact Finset.mem_union_left _ hxI
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxK, hxI⟩)
  simpa [I, G, hUnion] using hsplit

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
