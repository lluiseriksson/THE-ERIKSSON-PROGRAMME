/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.MayerCoverFactorization
import YangMills.RG.HolePolymerSystem

/-!
# Dimock Appendix F: exact finite-cover expansion

This file formalizes the finite combinatorial compiler underlying Dimock II,
Appendix F, equations (639)--(640).

For a finite family `Λ` of raw local activities it proves, exactly and without
convergence assumptions,

* the raw Mayer expansion
  `exp (∑ i ∈ Λ, h i) = ∑ I ⊆ Λ, ∏ i ∈ I, (exp (h i) - 1)`;
* the pointwise local-activity version regrouped by
  `confinedComponents (omegaOverlapGraph Ω activeSupport) I`;
* the canonical decomposition of every selected family `I` into the connected
  components of the literal `Ω`-overlap graph;
* the exact reindexing of the powerset sum by those canonical component
  families;
* nonemptiness, `Ω`-connectedness, and mutual `Ω`-disjointness of the canonical
  components;
* the first connected activity `K(Y)`, obtained by summing connected Mayer
  covers with declared raw-support union exactly `Y`;
* the exact fiberwise grouping of connected covers by their target union;
* local influence of `K(Y)`: changing a raw activity whose declared target
  support is not contained in `Y` cannot change `K(Y)`.
* the finite hard-core target system on representable unions, with
  incompatibility given by literal active `Ω`-intersection and activity
  `K(Y)`;
* the explicit finite Fubini domain of admissible target families equipped
  with one connected-cover choice in each target fiber, together with the
  forward map to admissible connected-cover families and the inverse
  choice datum that recovers any admissible connected-cover family under
  the active-nonempty hypothesis;
* the finite inverse from canonical components to admissible families of
  `Ω`-connected covers with pairwise `Ω`-disjoint declared-support unions
  for a single support map, plus the product identity `∏ᵢ (1 + wᵢ)` as a sum
  over those admissible families.

This is the finite algebraic part of Appendix F.  It does **not** prove the
modified-metric bound (642), ultralocal integration (643)--(644), the second
Ursell exponentiation (645)--(646), or the final loss
`κ - 3 * κ₀ - 3`.  Those remain separate analytic/quantitative steps.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open Finset
open scoped BigOperators

/-! ## Generic finite connected-component bookkeeping -/

/-- The union of the declared supports of the members of a finite cover. -/
noncomputable def appendixFCoverUnion {Site ι : Type*} [DecidableEq Site]
    (support : ι → Finset Site) (C : Finset ι) : Finset Site :=
  C.biUnion support

/-- The cardinality of a finite cover union is bounded by the sum of the
cardinalities of the declared supports.  This is the overlap-free upper
budget; it intentionally does not assume disjointness. -/
theorem appendixFCoverUnion_card_le_sum
    {Site ι : Type*} [DecidableEq Site]
    (support : ι → Finset Site) (C : Finset ι) :
    (appendixFCoverUnion support C).card ≤
      ∑ i ∈ C, (support i).card := by
  classical
  simpa [appendixFCoverUnion] using
    (Finset.card_biUnion_le (s := C) (t := support))

/-- Real-valued form of `appendixFCoverUnion_card_le_sum`. -/
theorem appendixFCoverUnion_card_real_le_sum
    {Site ι : Type*} [DecidableEq Site]
    (support : ι → Finset Site) (C : Finset ι) :
    ((appendixFCoverUnion support C).card : ℝ) ≤
      ∑ i ∈ C, ((support i).card : ℝ) := by
  exact_mod_cast appendixFCoverUnion_card_le_sum support C

/-- The finite component decomposition is injective: the original finite set is
recovered by taking the union of its confined components. -/
theorem confinedComponents_injective {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) : Function.Injective (confinedComponents G) := by
  intro A B hAB
  calc
    A = (confinedComponents G A).biUnion id :=
      (biUnion_confinedComponents_eq G A).symm
    _ = (confinedComponents G B).biUnion id := by rw [hAB]
    _ = B := biUnion_confinedComponents_eq G B

/-- Every member of the finite confined-component family is nonempty. -/
theorem nonempty_of_mem_confinedComponents {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (K C : Finset ι)
    (hC : C ∈ confinedComponents G K) : C.Nonempty := by
  rcases (mem_confinedComponents_iff G K C).mp hC with ⟨r, hr, rfl⟩
  exact ⟨r, root_mem_confinedComponent G K hr⟩

/-- Every member of the finite confined-component family is walk-connected. -/
theorem walkConnected_of_mem_confinedComponents {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (K C : Finset ι)
    (hC : C ∈ confinedComponents G K) : walkConnected G C := by
  rcases (mem_confinedComponents_iff G K C).mp hC with ⟨r, _hr, rfl⟩
  exact confinedComponent_walkConnected G K r

/-- A product over a finite set is exactly the iterated product over its
canonical graph components. -/
theorem prod_confinedComponents_eq_prod {ι M : Type*} [DecidableEq ι]
    [CommMonoid M] (G : SimpleGraph ι) (w : ι → M) (K : Finset ι) :
    (∏ C ∈ confinedComponents G K, ∏ i ∈ C, w i) = ∏ i ∈ K, w i := by
  classical
  have hpair : Set.PairwiseDisjoint
      (↑(confinedComponents G K) : Set (Finset ι))
      (id : Finset ι → Finset ι) :=
    fun C hC D hD hne =>
      disjoint_of_mem_confinedComponents_ne G K hC hD hne
  calc
    (∏ C ∈ confinedComponents G K, ∏ i ∈ C, w i)
        = ∏ i ∈ (confinedComponents G K).biUnion id, w i := by
          simpa using (Finset.prod_biUnion hpair).symm
    _ = ∏ i ∈ K, w i := by
          rw [biUnion_confinedComponents_eq G K]

theorem walk_support_subset_of_no_exit {ι : Type*} [DecidableEq ι]
    {G : SimpleGraph ι} {U C : Finset ι} {r s : ι}
    (w : G.Walk r s) (hrC : r ∈ C)
    (hwU : ∀ y, y ∈ w.support → y ∈ U)
    (hno : ∀ x, x ∈ C → ∀ y, y ∈ U → y ∉ C → ¬ G.Adj x y) :
    ∀ y, y ∈ w.support → y ∈ C := by
  induction w with
  | nil =>
      intro y hy
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
      simpa [hy] using hrC
  | @cons u v t hxy p ih =>
      have hvU : v ∈ U := hwU v (by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ p.start_mem_support)
      have hvC : v ∈ C := by
        by_contra hvnot
        exact (hno u hrC v hvU hvnot) hxy
      have hpU : ∀ y, y ∈ p.support → y ∈ U := by
        intro y hy
        exact hwU y (by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ hy)
      intro y hy
      rw [SimpleGraph.Walk.support_cons] at hy
      rcases List.mem_cons.mp hy with rfl | hyTail
      · exact hrC
      · exact ih hvC hpU y hyTail

theorem confinedComponent_eq_of_connected_no_exit {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (U C : Finset ι)
    (hCU : C ⊆ U) (hCnonempty : C.Nonempty)
    (hconn : walkConnected G C)
    (hno : ∀ x, x ∈ C → ∀ y, y ∈ U → y ∉ C → ¬ G.Adj x y) :
    ∃ r ∈ U, confinedComponent G U r = C := by
  classical
  rcases hCnonempty with ⟨r, hrC⟩
  refine ⟨r, hCU hrC, ?_⟩
  ext x
  constructor
  · intro hx
    rw [mem_confinedComponent_iff] at hx
    rcases hx.2 with ⟨w, hwU⟩
    exact walk_support_subset_of_no_exit w hrC hwU hno x w.end_mem_support
  · intro hxC
    rw [mem_confinedComponent_iff]
    rcases hconn r hrC x hxC with ⟨w, hwC⟩
    exact ⟨hCU hxC, ⟨w, fun y hy => hCU (hwC y hy)⟩⟩

/-! ## Canonical families of Ω-connected covers -/

/-- The finite set of canonical connected-cover families obtained from all
subfamilies of `Λ`.  Each member is the component family of one selected raw
subfamily. -/
noncomputable def appendixFCanonicalCoverFamilies {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (Λ : Finset ι) : Finset (Finset (Finset ι)) :=
  Λ.powerset.image (confinedComponents G)

@[simp] theorem mem_appendixFCanonicalCoverFamilies_iff
    {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (Λ : Finset ι)
    (Γ : Finset (Finset ι)) :
    Γ ∈ appendixFCanonicalCoverFamilies G Λ ↔
      ∃ I ∈ Λ.powerset, Γ = confinedComponents G I := by
  classical
  constructor
  · intro hΓ
    rw [appendixFCanonicalCoverFamilies, Finset.mem_image] at hΓ
    rcases hΓ with ⟨I, hI, hEq⟩
    exact ⟨I, hI, hEq.symm⟩
  · rintro ⟨I, hI, rfl⟩
    rw [appendixFCanonicalCoverFamilies, Finset.mem_image]
    exact ⟨I, hI, rfl⟩

/-- The members of a canonical cover family cover a subfamily of `Λ`. -/
theorem biUnion_subset_of_mem_appendixFCanonicalCoverFamilies
    {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (Λ : Finset ι)
    {Γ : Finset (Finset ι)}
    (hΓ : Γ ∈ appendixFCanonicalCoverFamilies G Λ) :
    Γ.biUnion id ⊆ Λ := by
  rcases (mem_appendixFCanonicalCoverFamilies_iff G Λ Γ).mp hΓ with
    ⟨I, hI, rfl⟩
  rw [biUnion_confinedComponents_eq G I]
  exact Finset.mem_powerset.mp hI

/-- Every member of a canonical cover family is nonempty. -/
theorem nonempty_of_mem_appendixFCanonicalCoverFamily
    {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (Λ : Finset ι)
    {Γ : Finset (Finset ι)}
    (hΓ : Γ ∈ appendixFCanonicalCoverFamilies G Λ)
    {C : Finset ι} (hC : C ∈ Γ) : C.Nonempty := by
  rcases (mem_appendixFCanonicalCoverFamilies_iff G Λ Γ).mp hΓ with
    ⟨I, _hI, rfl⟩
  exact nonempty_of_mem_confinedComponents G I C hC

/-- Every member of a canonical cover family is connected in the graph used to
form the components. -/
theorem walkConnected_of_mem_appendixFCanonicalCoverFamily
    {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (Λ : Finset ι)
    {Γ : Finset (Finset ι)}
    (hΓ : Γ ∈ appendixFCanonicalCoverFamilies G Λ)
    {C : Finset ι} (hC : C ∈ Γ) : walkConnected G C := by
  rcases (mem_appendixFCanonicalCoverFamilies_iff G Λ Γ).mp hΓ with
    ⟨I, _hI, rfl⟩
  exact walkConnected_of_mem_confinedComponents G I C hC

/-- Distinct members of a canonical cover family are disjoint as index sets. -/
theorem disjoint_of_mem_appendixFCanonicalCoverFamily_ne
    {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (Λ : Finset ι)
    {Γ : Finset (Finset ι)}
    (hΓ : Γ ∈ appendixFCanonicalCoverFamilies G Λ)
    {C D : Finset ι} (hC : C ∈ Γ) (hD : D ∈ Γ) (hCD : C ≠ D) :
    Disjoint C D := by
  rcases (mem_appendixFCanonicalCoverFamilies_iff G Λ Γ).mp hΓ with
    ⟨I, _hI, rfl⟩
  exact disjoint_of_mem_confinedComponents_ne G I hC hD hCD

/-- Distinct members of a canonical cover family have no graph edge between
any pair of their indices. -/
theorem no_adj_of_mem_appendixFCanonicalCoverFamily_ne
    {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (Λ : Finset ι)
    {Γ : Finset (Finset ι)}
    (hΓ : Γ ∈ appendixFCanonicalCoverFamilies G Λ)
    {C D : Finset ι} (hC : C ∈ Γ) (hD : D ∈ Γ) (hCD : C ≠ D)
    {i j : ι} (hi : i ∈ C) (hj : j ∈ D) : ¬ G.Adj i j := by
  rcases (mem_appendixFCanonicalCoverFamilies_iff G Λ Γ).mp hΓ with
    ⟨I, _hI, rfl⟩
  exact no_adj_of_mem_confinedComponents_ne G I hC hD hCD hi hj

/-- For the literal Appendix-F graph, distinct canonical components have
pairwise disjoint raw supports inside `Ω`. -/
theorem appendixFCanonicalComponents_omegaSupport_disjoint
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    {Γ : Finset (Finset ι)}
    (hΓ : Γ ∈ appendixFCanonicalCoverFamilies
      (omegaOverlapGraph Ω support) Λ)
    {C D : Finset ι} (hC : C ∈ Γ) (hD : D ∈ Γ) (hCD : C ≠ D) :
    Disjoint (Ω ∩ appendixFCoverUnion support C)
      (Ω ∩ appendixFCoverUnion support D) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxC hxD
  rcases Finset.mem_inter.mp hxC with ⟨hxΩ, hxCU⟩
  rcases Finset.mem_inter.mp hxD with ⟨_hxΩ', hxDU⟩
  rcases Finset.mem_biUnion.mp hxCU with ⟨i, hiC, hxi⟩
  rcases Finset.mem_biUnion.mp hxDU with ⟨j, hjD, hxj⟩
  have hno : ¬ (omegaOverlapGraph Ω support).Adj i j :=
    no_adj_of_mem_appendixFCanonicalCoverFamily_ne
      (omegaOverlapGraph Ω support) Λ hΓ hC hD hCD hiC hjD
  have hCDdisj : Disjoint C D :=
    disjoint_of_mem_appendixFCanonicalCoverFamily_ne
      (omegaOverlapGraph Ω support) Λ hΓ hC hD hCD
  have hij : i ≠ j := by
    intro hij
    subst j
    exact (Finset.disjoint_left.mp hCDdisj hiC) hjD
  exact hno ((omegaOverlapGraph_adj_iff Ω support i j).mpr
    ⟨hij, by
      intro hd
      exact (Finset.disjoint_left.mp hd (Finset.mem_inter.mpr ⟨hxΩ, hxi⟩))
        (Finset.mem_inter.mpr ⟨hxΩ, hxj⟩)⟩)

/-! ## Exact finite Mayer reindexing -/

/-- Product weight of one connected raw cover. -/
noncomputable def appendixFComponentWeight {ι M : Type*} [DecidableEq ι]
    [CommMonoid M] (w : ι → M) (C : Finset ι) : M :=
  ∏ i ∈ C, w i

/-- Product weight of a finite family of connected raw covers. -/
noncomputable def appendixFCoverFamilyWeight {ι M : Type*} [DecidableEq ι]
    [CommMonoid M] (w : ι → M) (Γ : Finset (Finset ι)) : M :=
  ∏ C ∈ Γ, appendixFComponentWeight w C

/-- Exact reindexing of a finite powerset sum by canonical connected-component
families.  This is the purely finite combinatorial content of Appendix F (639).
-/
theorem sum_powerset_eq_sum_appendixFCanonicalCoverFamilies
    {ι A : Type*} [DecidableEq ι] [AddCommMonoid A] [CommMonoid A]
    (G : SimpleGraph ι) (Λ : Finset ι) (w : ι → A) :
    (∑ I ∈ Λ.powerset, ∏ i ∈ I, w i) =
      ∑ Γ ∈ appendixFCanonicalCoverFamilies G Λ,
        appendixFCoverFamilyWeight w Γ := by
  classical
  unfold appendixFCoverFamilyWeight appendixFComponentWeight
  refine Finset.sum_nbij'
    (confinedComponents G)
    (fun Γ => Γ.biUnion id) ?_ ?_ ?_ ?_ ?_
  · intro I hI
    rw [appendixFCanonicalCoverFamilies, Finset.mem_image]
    exact ⟨I, hI, rfl⟩
  · intro Γ hΓ
    rcases (mem_appendixFCanonicalCoverFamilies_iff G Λ Γ).mp hΓ with
      ⟨I, hI, rfl⟩
    change (confinedComponents G I).biUnion id ∈ Λ.powerset
    rw [biUnion_confinedComponents_eq G I]
    exact hI
  · intro I _hI
    exact biUnion_confinedComponents_eq G I
  · intro Γ hΓ
    rcases (mem_appendixFCanonicalCoverFamilies_iff G Λ Γ).mp hΓ with
      ⟨I, _hI, rfl⟩
    change confinedComponents G ((confinedComponents G I).biUnion id) =
      confinedComponents G I
    rw [biUnion_confinedComponents_eq G I]
  · intro I _hI
    exact (prod_confinedComponents_eq_prod G w I).symm

/-- The elementary finite raw-Mayer identity. -/
theorem complex_exp_sum_eq_sum_powerset_rawMayer
    {ι : Type*} [DecidableEq ι] (Λ : Finset ι) (h : ι → ℂ) :
    Complex.exp (∑ i ∈ Λ, h i) =
      ∑ I ∈ Λ.powerset, ∏ i ∈ I, (Complex.exp (h i) - 1) := by
  classical
  rw [Complex.exp_sum]
  have hfac : ∀ i ∈ Λ,
      Complex.exp (h i) = (Complex.exp (h i) - 1) + 1 := by
    intro i _hi
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_add]
  exact Finset.sum_congr rfl fun I _hI => by
    rw [Finset.prod_const_one, mul_one]

/-- Finset-indexed form of the pointwise value of a Mayer-cover activity. -/
theorem globalEval_mayerCoverActivity_eq_finsetProd
    {Site : Type*} [DecidableEq Site] {Ψ Φ : Site → Type*} {ι : Type*}
    (I : Finset ι) (H : ι → LocalActivity Site Ψ Φ ℂ)
    (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x) :
    (LocalActivity.mayerCoverActivity I H).globalEval ψ φ =
      ∏ i ∈ I, (Complex.exp ((H i).globalEval ψ φ) - 1) := by
  classical
  rw [LocalActivity.globalEval_mayerCoverActivity]
  exact Finset.prod_coe_sort I
    (fun i => Complex.exp ((H i).globalEval ψ φ) - 1)

/-- Pointwise Appendix-F component expansion for local activities.  This is
the finite Mayer expansion regrouped by the canonical `Ω`-connected components
of each selected raw subfamily; it carries no measure or decay hypothesis. -/
theorem exp_finsetSum_eq_sum_powerset_prod_confinedOmegaComponents
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    {Ψ Φ : Site → Type*}
    (Ω : Finset Site) (activeSupport : ι → Finset Site)
    (K : Finset ι) (H : ι → LocalActivity Site Ψ Φ ℂ)
    (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x) :
    Complex.exp (∑ i ∈ K, (H i).globalEval ψ φ) =
      ∑ I ∈ K.powerset,
        ∏ C ∈ confinedComponents
            (omegaOverlapGraph Ω activeSupport) I,
          (LocalActivity.mayerCoverActivity C H).globalEval ψ φ := by
  classical
  rw [complex_exp_sum_eq_sum_powerset_rawMayer K
    (fun i => (H i).globalEval ψ φ)]
  refine Finset.sum_congr rfl ?_
  intro I _hI
  let G := omegaOverlapGraph Ω activeSupport
  let w : ι → ℂ := fun i => Complex.exp ((H i).globalEval ψ φ) - 1
  calc
    (∏ i ∈ I, (Complex.exp ((H i).globalEval ψ φ) - 1))
        = ∏ C ∈ confinedComponents G I, ∏ i ∈ C, w i := by
          simpa [G, w] using (prod_confinedComponents_eq_prod G w I).symm
    _ = ∏ C ∈ confinedComponents G I,
          (LocalActivity.mayerCoverActivity C H).globalEval ψ φ := by
          refine Finset.prod_congr rfl ?_
          intro C _hC
          rw [globalEval_mayerCoverActivity_eq_finsetProd]

/-- **Appendix-F finite-cover expansion.**  The exponential of the finite raw
activity sum is exactly the sum over canonical families of `Ω`-connected raw
Mayer covers.  No convergence or smallness hypothesis is used. -/
theorem appendixF_finite_cover_expansion
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site)
    (Λ : Finset ι) (h : ι → ℂ) :
    Complex.exp (∑ i ∈ Λ, h i) =
      ∑ Γ ∈ appendixFCanonicalCoverFamilies
          (omegaOverlapGraph Ω support) Λ,
        appendixFCoverFamilyWeight
          (fun i => Complex.exp (h i) - 1) Γ := by
  rw [complex_exp_sum_eq_sum_powerset_rawMayer Λ h]
  exact sum_powerset_eq_sum_appendixFCanonicalCoverFamilies
    (omegaOverlapGraph Ω support) Λ
    (fun i => Complex.exp (h i) - 1)

/-! ## The first connected activity K(Y), Appendix F (640) -/

/-- All nonempty `Ω`-connected raw covers selected from a finite raw family.
`overlapSupport` controls the `Ω`-overlap graph.  It is deliberately separate
from the support map used to form the target union `Y`: in the concrete
with-holes system, connectivity is through skeletons while `Y` is the union of
full hole-polymers. -/
noncomputable def appendixFConnectedCoverRegion
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (overlapSupport : ι → Finset Site) (Λ : Finset ι) :
    Finset (Finset ι) :=
  Λ.powerset.filter fun C =>
    C.Nonempty ∧ omegaConnectedIndex Ω C overlapSupport

@[simp] theorem mem_appendixFConnectedCoverRegion_iff
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (overlapSupport : ι → Finset Site)
    (Λ C : Finset ι) :
    C ∈ appendixFConnectedCoverRegion Ω overlapSupport Λ ↔
      C ⊆ Λ ∧ C.Nonempty ∧ omegaConnectedIndex Ω C overlapSupport := by
  classical
  simp [appendixFConnectedCoverRegion]

/-- The finite set of target full-support unions carried by connected covers. -/
noncomputable def appendixFTargetRegion
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) : Finset (Finset Site) :=
  (appendixFConnectedCoverRegion Ω overlapSupport Λ).image
    (appendixFCoverUnion targetSupport)

/-- The connected-cover fiber over one declared target union. -/
noncomputable def appendixFTargetFiber
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (Y : Finset Site) : Finset (Finset ι) :=
  (appendixFConnectedCoverRegion Ω overlapSupport Λ).filter
    (fun C => appendixFCoverUnion targetSupport C = Y)

@[simp] theorem mem_appendixFTargetFiber_iff
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (Y : Finset Site) (C : Finset ι) :
    C ∈ appendixFTargetFiber Ω overlapSupport targetSupport Λ Y ↔
      C ∈ appendixFConnectedCoverRegion Ω overlapSupport Λ ∧
        appendixFCoverUnion targetSupport C = Y := by
  classical
  simp [appendixFTargetFiber]

/-- The first connected activity for already-formed Mayer weights `w i`.
This is the algebraic core of `K(Y)` before specializing
`w i = exp (h i) - 1`. -/
noncomputable def appendixFConnectedMayerActivity
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (w : ι → ℂ) (Y : Finset Site) : ℂ :=
  ∑ C ∈ appendixFTargetFiber Ω overlapSupport targetSupport Λ Y,
    ∏ i ∈ C, w i

/-- Dimock's first connected activity `K(Y)`: sum all connected raw Mayer covers
whose declared full-support union is exactly `Y`. -/
noncomputable def appendixFConnectedActivity
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (h : ι → ℂ) (Y : Finset Site) : ℂ :=
  ∑ C ∈ (appendixFConnectedCoverRegion Ω overlapSupport Λ).filter
      (fun C => appendixFCoverUnion targetSupport C = Y),
    ∏ i ∈ C, (Complex.exp (h i) - 1)

/-- Exact fiberwise grouping of all connected raw covers by their target union.
This is the finite summation content of Appendix F (640). -/
theorem sum_connectedCovers_eq_sum_appendixFConnectedActivity
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (h : ι → ℂ) :
    (∑ C ∈ appendixFConnectedCoverRegion Ω overlapSupport Λ,
        ∏ i ∈ C, (Complex.exp (h i) - 1)) =
      ∑ Y ∈ appendixFTargetRegion Ω overlapSupport targetSupport Λ,
        appendixFConnectedActivity Ω overlapSupport targetSupport Λ h Y := by
  classical
  unfold appendixFTargetRegion appendixFConnectedActivity
  exact (Finset.sum_fiberwise_of_maps_to
    (fun C hC => Finset.mem_image.mpr ⟨C, hC, rfl⟩) _).symm

/-- Every raw index in a cover contributing to `K(Y)` has its declared full
support contained in `Y`. -/
theorem targetSupport_subset_of_mem_appendixFConnectedActivityFiber
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (Y : Finset Site) {C : Finset ι}
    (hC : C ∈ (appendixFConnectedCoverRegion Ω overlapSupport Λ).filter
      (fun C => appendixFCoverUnion targetSupport C = Y))
    {i : ι} (hi : i ∈ C) : targetSupport i ⊆ Y := by
  intro x hx
  have hxU : x ∈ appendixFCoverUnion targetSupport C :=
    Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
  have htarget := (Finset.mem_filter.mp hC).2
  rwa [htarget] at hxU

/-- **Local influence of the first connected activity.**  To determine `K(Y)`
it is enough to know raw activities whose indices belong to `Λ` and whose full
support is contained in `Y`. -/
theorem appendixFConnectedActivity_congr
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (h₁ h₂ : ι → ℂ) (Y : Finset Site)
    (heq : ∀ i, i ∈ Λ → targetSupport i ⊆ Y → h₁ i = h₂ i) :
    appendixFConnectedActivity Ω overlapSupport targetSupport Λ h₁ Y =
      appendixFConnectedActivity Ω overlapSupport targetSupport Λ h₂ Y := by
  classical
  unfold appendixFConnectedActivity
  refine Finset.sum_congr rfl ?_
  intro C hC
  refine Finset.prod_congr rfl ?_
  intro i hi
  have hCregion : C ∈ appendixFConnectedCoverRegion Ω overlapSupport Λ :=
    (Finset.mem_filter.mp hC).1
  have hCsubset : C ⊆ Λ :=
    ((mem_appendixFConnectedCoverRegion_iff Ω overlapSupport Λ C).mp hCregion).1
  have hiΛ : i ∈ Λ := hCsubset hi
  have hisub : targetSupport i ⊆ Y :=
    targetSupport_subset_of_mem_appendixFConnectedActivityFiber
      Ω overlapSupport targetSupport Λ Y hC hi
  rw [heq i hiΛ hisub]

/-! ## The finite hard-core target system -/

/-- A connected cover whose raw active supports are all nonempty inside `Ω`
has a nonempty active target union.  This is the finite self-incompatibility
input needed by the target hard-core gas. -/
theorem omega_inter_coverUnion_nonempty_of_mem_appendixFConnectedCoverRegion
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty)
    {C : Finset ι}
    (hC : C ∈ appendixFConnectedCoverRegion Ω support Λ) :
    (Ω ∩ appendixFCoverUnion support C).Nonempty := by
  classical
  have hCdata := (mem_appendixFConnectedCoverRegion_iff Ω support Λ C).mp hC
  rcases hCdata.2.1 with ⟨i, hiC⟩
  rcases hactive i (hCdata.1 hiC) with ⟨x, hx⟩
  rw [Finset.mem_inter] at hx
  refine ⟨x, Finset.mem_inter.mpr ⟨hx.1, ?_⟩⟩
  exact Finset.mem_biUnion.mpr ⟨i, hiC, hx.2⟩

/-- Every representable target union has nonempty active part when every raw
support selected from `Λ` does. -/
theorem omega_inter_target_nonempty_of_mem_appendixFTargetRegion
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty)
    {Y : Finset Site}
    (hY : Y ∈ appendixFTargetRegion Ω support support Λ) :
    (Ω ∩ Y).Nonempty := by
  classical
  unfold appendixFTargetRegion at hY
  rcases Finset.mem_image.mp hY with ⟨C, hC, rfl⟩
  exact omega_inter_coverUnion_nonempty_of_mem_appendixFConnectedCoverRegion
    Ω support Λ hactive hC

/-- The exact finite Appendix-F hard-core gas on representable target unions.
Its incompatibility is literal `Ω`-active intersection of targets, and its
activity is the connected-cover fiber sum `K(Y)`. -/
noncomputable def appendixFTargetPolymerSystem
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (w : ι → ℂ)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty) :
    KP.PolymerSystem where
  Polymer := {Y : Finset Site // Y ∈ appendixFTargetRegion Ω support support Λ}
  incomp Y Z := ¬ Disjoint (Ω ∩ Y.val) (Ω ∩ Z.val)
  incomp_symm := by
    intro Y Z hYZ hZY
    exact hYZ (by rwa [disjoint_comm])
  incomp_self := by
    intro Y hdisj
    rcases omega_inter_target_nonempty_of_mem_appendixFTargetRegion
        Ω support Λ hactive Y.property with ⟨x, hx⟩
    exact (Finset.disjoint_left.mp hdisj hx) hx
  activity Y :=
    appendixFConnectedMayerActivity Ω support support Λ w Y.val

/-- The target polymer type is finite because it is the subtype cut out by the
finite representable-target set. -/
noncomputable instance appendixFTargetPolymerSystem_fintype
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (w : ι → ℂ)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty) :
    Fintype (appendixFTargetPolymerSystem Ω support Λ w hactive).Polymer := by
  dsimp [appendixFTargetPolymerSystem]
  exact Fintype.ofFinset (appendixFTargetRegion Ω support support Λ) (by
    intro Y
    rfl)

/-- A finite target family is admissible for `appendixFTargetPolymerSystem`
exactly when its distinct active target unions are pairwise `Ω`-disjoint. -/
theorem appendixFTargetPolymerSystem_admissible_iff
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (w : ι → ℂ)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty)
    (S : Finset (appendixFTargetPolymerSystem Ω support Λ w hactive).Polymer) :
    KP.Admissible (appendixFTargetPolymerSystem Ω support Λ w hactive) S ↔
      ∀ Y ∈ S, ∀ Z ∈ S, Y ≠ Z →
        Disjoint (Ω ∩ Y.val) (Ω ∩ Z.val) := by
  classical
  constructor
  · intro h Y hY Z hZ hYZ
    by_contra hdisj
    exact h Y hY Z hZ hYZ hdisj
  · intro h Y hY Z hZ hYZ hincomp
    exact hincomp (h Y hY Z hZ hYZ)

/-- Finite target families admitted by the Appendix-F target hard-core gas,
written without the subtype wrapper used by `KP.partition`. -/
noncomputable def appendixFAdmissibleTargetFamilies
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι) :
    Finset (Finset (Finset Site)) :=
  (appendixFTargetRegion Ω support support Λ).powerset.filter fun Υ =>
    ∀ Y ∈ Υ, ∀ Z ∈ Υ, Y ≠ Z →
      Disjoint (Ω ∩ Y) (Ω ∩ Z)

@[simp] theorem mem_appendixFAdmissibleTargetFamilies_iff
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (Υ : Finset (Finset Site)) :
    Υ ∈ appendixFAdmissibleTargetFamilies Ω support Λ ↔
      Υ ⊆ appendixFTargetRegion Ω support support Λ ∧
        ∀ Y ∈ Υ, ∀ Z ∈ Υ, Y ≠ Z →
          Disjoint (Ω ∩ Y) (Ω ∩ Z) := by
  classical
  simp [appendixFAdmissibleTargetFamilies]

theorem appendixFTargetPolymerSystem_partition_eq_sum_admissibleTargetFamilies
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (w : ι → ℂ)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty) :
    KP.partition (appendixFTargetPolymerSystem Ω support Λ w hactive) Finset.univ =
      ∑ Υ ∈ appendixFAdmissibleTargetFamilies Ω support Λ,
        ∏ Y ∈ Υ, appendixFConnectedMayerActivity Ω support support Λ w Y := by
  classical
  let P := appendixFTargetPolymerSystem Ω support Λ w hactive
  let T := appendixFTargetRegion Ω support support Λ
  rw [KP.partition]
  refine Finset.sum_bij'
    (fun S _ => S.image (fun Y : P.Polymer => Y.val))
    (fun Υ hΥ =>
      let hΥdata := (mem_appendixFAdmissibleTargetFamilies_iff Ω support Λ Υ).mp hΥ
      Υ.attach.image (fun Y : {Y // Y ∈ Υ} =>
        (⟨Y.val, hΥdata.1 Y.property⟩ : P.Polymer))) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_appendixFAdmissibleTargetFamilies_iff]
    rw [Finset.mem_filter] at hS
    have hAdm := hS.2
    have hpair :=
      (appendixFTargetPolymerSystem_admissible_iff Ω support Λ w hactive S).mp hAdm
    refine ⟨?_, ?_⟩
    · intro Y hY
      rcases Finset.mem_image.mp hY with ⟨Yp, _hYp, rfl⟩
      exact Yp.property
    · intro Y hY Z hZ hYZ
      rcases Finset.mem_image.mp hY with ⟨Yp, hYp, rfl⟩
      rcases Finset.mem_image.mp hZ with ⟨Zp, hZp, rfl⟩
      exact hpair Yp hYp Zp hZp (by
        intro hYZp
        exact hYZ (by simp [hYZp]))
  · intro Υ hΥ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr (by intro Y _hY; simp), ?_⟩
    rw [appendixFTargetPolymerSystem_admissible_iff]
    intro Y hY Z hZ hYZ
    rw [mem_appendixFAdmissibleTargetFamilies_iff] at hΥ
    rcases Finset.mem_image.mp hY with ⟨Yraw, hYraw, rfl⟩
    rcases Finset.mem_image.mp hZ with ⟨Zraw, hZraw, rfl⟩
    exact hΥ.2 Yraw.val Yraw.property Zraw.val Zraw.property (by
      intro hval
      exact hYZ (Subtype.ext hval))
  · intro S hS
    ext Y
    constructor
    · intro hY
      rcases Finset.mem_image.mp hY with ⟨Yraw, hYraw, hYeq⟩
      rcases Finset.mem_image.mp Yraw.property with ⟨Z, hZ, hZeq⟩
      have hYZ : Y = Z := by
        apply Subtype.ext
        have hYval : Yraw.val = Y.val := congrArg Subtype.val hYeq
        exact hYval.symm.trans hZeq.symm
      rw [hYZ]
      exact hZ
    · intro hY
      rw [Finset.mem_image]
      refine ⟨⟨Y.val, ?_⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨Y, hY, rfl⟩
      · simp
      · exact Subtype.ext rfl
  · intro Υ hΥ
    ext Y
    constructor
    · intro hY
      rcases Finset.mem_image.mp hY with ⟨Yp, hYp, rfl⟩
      rcases Finset.mem_image.mp hYp with ⟨Yraw, hYraw, hYeq⟩
      have hval : Yraw.val = Yp.val := congrArg Subtype.val hYeq
      rw [← hval]
      exact Yraw.property
    · intro hY
      rw [Finset.mem_image]
      rw [mem_appendixFAdmissibleTargetFamilies_iff] at hΥ
      refine ⟨⟨Y, hΥ.1 hY⟩, ?_, rfl⟩
      rw [Finset.mem_image]
      exact ⟨⟨Y, hY⟩, by simp, rfl⟩
  · intro S hS
    dsimp [P, appendixFTargetPolymerSystem]
    rw [Finset.prod_image]
    intro Y hY Z hZ hYZ
    exact Subtype.ext hYZ

/-- The finite domain obtained by choosing, for each admissible target `Y` in
an admissible target family, one connected raw cover in the fiber over `Y`.
This is the explicit finite Fubini domain for the target-lumping theorem. -/
noncomputable def appendixFAdmissibleTargetChoices
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι) :
    Finset (Σ Υ : Finset (Finset Site),
      ∀ Y, Y ∈ Υ → Finset ι) :=
  (appendixFAdmissibleTargetFamilies Ω support Λ).sigma fun Υ =>
    Υ.pi fun Y => appendixFTargetFiber Ω support support Λ Y

@[simp] theorem mem_appendixFAdmissibleTargetChoices_iff
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (Ξ : Σ Υ : Finset (Finset Site), ∀ Y, Y ∈ Υ → Finset ι) :
    Ξ ∈ appendixFAdmissibleTargetChoices Ω support Λ ↔
      Ξ.1 ∈ appendixFAdmissibleTargetFamilies Ω support Λ ∧
        ∀ Y hY, Ξ.2 Y hY ∈ appendixFTargetFiber Ω support support Λ Y := by
  classical
  simp [appendixFAdmissibleTargetChoices]

theorem sum_admissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_targetChoices
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (w : ι → ℂ) :
    (∑ Υ ∈ appendixFAdmissibleTargetFamilies Ω support Λ,
        ∏ Y ∈ Υ, appendixFConnectedMayerActivity Ω support support Λ w Y) =
      ∑ Ξ ∈ appendixFAdmissibleTargetChoices Ω support Λ,
        ∏ Y ∈ Ξ.1.attach, ∏ i ∈ Ξ.2 Y.1 Y.2, w i := by
  classical
  calc
    (∑ Υ ∈ appendixFAdmissibleTargetFamilies Ω support Λ,
        ∏ Y ∈ Υ, appendixFConnectedMayerActivity Ω support support Λ w Y)
        =
          ∑ Υ ∈ appendixFAdmissibleTargetFamilies Ω support Λ,
            ∑ p ∈ Υ.pi (fun Y => appendixFTargetFiber Ω support support Λ Y),
              ∏ Y ∈ Υ.attach, ∏ i ∈ p Y.1 Y.2, w i := by
            refine Finset.sum_congr rfl ?_
            intro Υ _hΥ
            exact Finset.prod_sum Υ
              (fun Y => appendixFTargetFiber Ω support support Λ Y)
              (fun _Y C => ∏ i ∈ C, w i)
    _ =
      ∑ Ξ ∈ appendixFAdmissibleTargetChoices Ω support Λ,
        ∏ Y ∈ Ξ.1.attach, ∏ i ∈ Ξ.2 Y.1 Y.2, w i := by
          rw [Finset.sum_sigma']
          rfl

private theorem cast_forall_mem_finset_apply
    {α β : Type*} [DecidableEq α]
    {A B : Finset α} (h : A = B)
    (f : ∀ x : α, x ∈ A → β) (x : α) (hx : x ∈ B) :
    cast (congrArg (fun U : Finset α => ∀ x : α, x ∈ U → β) h) f x hx =
      f x (by rw [h]; exact hx) := by
  cases h
  rfl

/-- A finite family of connected raw covers is Appendix-F admissible when
distinct connected covers have disjoint declared-support union inside `Ω`.

This is intentionally the single-support variant.  The separate `K(Y)` layer
above allows a different `targetSupport`; no theorem here asserts full-target
disjointness for the with-holes adapter where connectivity uses skeletons. -/
noncomputable def appendixFAdmissibleConnectedCoverFamilies
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι) :
    Finset (Finset (Finset ι)) :=
  (appendixFConnectedCoverRegion Ω support Λ).powerset.filter fun Γ =>
    ∀ C ∈ Γ, ∀ D ∈ Γ, C ≠ D →
      Disjoint (Ω ∩ appendixFCoverUnion support C)
        (Ω ∩ appendixFCoverUnion support D)

@[simp] theorem mem_appendixFAdmissibleConnectedCoverFamilies_iff
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (Γ : Finset (Finset ι)) :
    Γ ∈ appendixFAdmissibleConnectedCoverFamilies Ω support Λ ↔
      Γ ⊆ appendixFConnectedCoverRegion Ω support Λ ∧
        ∀ C ∈ Γ, ∀ D ∈ Γ, C ≠ D →
          Disjoint (Ω ∩ appendixFCoverUnion support C)
            (Ω ∩ appendixFCoverUnion support D) := by
  classical
  simp [appendixFAdmissibleConnectedCoverFamilies]

/-- A target choice family, with the target labels erased, is the finite family
of connected raw covers selected in each target fiber. -/
noncomputable def appendixFTargetChoiceCoverFamily
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ξ : Σ Υ : Finset (Finset Site), ∀ Y, Y ∈ Υ → Finset ι) :
    Finset (Finset ι) :=
  Ξ.1.attach.image fun Y => Ξ.2 Y.1 Y.2

theorem appendixFTargetChoiceCoverFamily_mem_admissible
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    {Ξ : Σ Υ : Finset (Finset Site), ∀ Y, Y ∈ Υ → Finset ι}
    (hΞ : Ξ ∈ appendixFAdmissibleTargetChoices Ω support Λ) :
    appendixFTargetChoiceCoverFamily Ξ ∈
      appendixFAdmissibleConnectedCoverFamilies Ω support Λ := by
  classical
  rw [mem_appendixFAdmissibleConnectedCoverFamilies_iff]
  rw [mem_appendixFAdmissibleTargetChoices_iff] at hΞ
  refine ⟨?_, ?_⟩
  · intro C hC
    rw [appendixFTargetChoiceCoverFamily] at hC
    rcases Finset.mem_image.mp hC with ⟨Y, _hY, rfl⟩
    exact ((mem_appendixFTargetFiber_iff Ω support support Λ
      Y.1 (Ξ.2 Y.1 Y.2)).mp (hΞ.2 Y.1 Y.2)).1
  · intro C hC D hD hCD
    rw [appendixFTargetChoiceCoverFamily] at hC hD
    rcases Finset.mem_image.mp hC with ⟨Y, _hY, rfl⟩
    rcases Finset.mem_image.mp hD with ⟨Z, _hZ, rfl⟩
    have hYfiber := (mem_appendixFTargetFiber_iff Ω support support Λ
      Y.1 (Ξ.2 Y.1 Y.2)).mp (hΞ.2 Y.1 Y.2)
    have hZfiber := (mem_appendixFTargetFiber_iff Ω support support Λ
      Z.1 (Ξ.2 Z.1 Z.2)).mp (hΞ.2 Z.1 Z.2)
    have hYZ : Y.1 ≠ Z.1 := by
      intro hval
      have hYZsub : Y = Z := Subtype.ext hval
      exact hCD (by subst Z; rfl)
    have htarget :=
      ((mem_appendixFAdmissibleTargetFamilies_iff Ω support Λ Ξ.1).mp hΞ.1).2
        Y.1 Y.2 Z.1 Z.2 hYZ
    simpa [hYfiber.2, hZfiber.2] using htarget

theorem appendixFCoverFamilyWeight_targetChoiceCoverFamily_eq
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (w : ι → ℂ)
    {Ξ : Σ Υ : Finset (Finset Site), ∀ Y, Y ∈ Υ → Finset ι}
    (hΞ : Ξ ∈ appendixFAdmissibleTargetChoices Ω support Λ) :
    appendixFCoverFamilyWeight w (appendixFTargetChoiceCoverFamily Ξ) =
      ∏ Y ∈ Ξ.1.attach, ∏ i ∈ Ξ.2 Y.1 Y.2, w i := by
  classical
  rw [mem_appendixFAdmissibleTargetChoices_iff] at hΞ
  unfold appendixFCoverFamilyWeight appendixFComponentWeight
    appendixFTargetChoiceCoverFamily
  rw [Finset.prod_image]
  intro Y _hY Z _hZ hYZ
  apply Subtype.ext
  have hYfiber := (mem_appendixFTargetFiber_iff Ω support support Λ
    Y.1 (Ξ.2 Y.1 Y.2)).mp (hΞ.2 Y.1 Y.2)
  have hZfiber := (mem_appendixFTargetFiber_iff Ω support support Λ
    Z.1 (Ξ.2 Z.1 Z.2)).mp (hΞ.2 Z.1 Z.2)
  have hcover :
      appendixFCoverUnion support (Ξ.2 Y.1 Y.2) =
        appendixFCoverUnion support (Ξ.2 Z.1 Z.2) := by
    exact congrArg (appendixFCoverUnion support) hYZ
  exact hYfiber.2.symm.trans (hcover.trans hZfiber.2)

/-- Mapping an admissible connected-cover family to its target unions gives an
admissible target family.  This is the forward half of the finite
Appendix-F target-lumping map. -/
theorem image_coverUnion_mem_appendixFAdmissibleTargetFamilies
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    {Γ : Finset (Finset ι)}
    (hΓ : Γ ∈ appendixFAdmissibleConnectedCoverFamilies Ω support Λ) :
    Γ.image (appendixFCoverUnion support) ∈
      appendixFAdmissibleTargetFamilies Ω support Λ := by
  classical
  rw [mem_appendixFAdmissibleTargetFamilies_iff]
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
    exact hΓ.2 C hC D hD hCD

/-- Under nonempty active raw supports, an admissible connected-cover family
cannot contain two distinct connected covers with the same target union. -/
theorem appendixFCoverUnion_injective_on_admissibleConnectedCoverFamily
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty)
    {Γ : Finset (Finset ι)}
    (hΓ : Γ ∈ appendixFAdmissibleConnectedCoverFamilies Ω support Λ)
    {C D : Finset ι} (hC : C ∈ Γ) (hD : D ∈ Γ)
    (hCD : appendixFCoverUnion support C = appendixFCoverUnion support D) :
    C = D := by
  classical
  by_contra hne
  rw [mem_appendixFAdmissibleConnectedCoverFamilies_iff] at hΓ
  have hdisj := hΓ.2 C hC D hD hne
  rw [← hCD] at hdisj
  have hnonempty :
      (Ω ∩ appendixFCoverUnion support C).Nonempty :=
    omega_inter_coverUnion_nonempty_of_mem_appendixFConnectedCoverRegion
      Ω support Λ hactive (hΓ.1 hC)
  rcases hnonempty with ⟨x, hx⟩
  exact (Finset.disjoint_left.mp hdisj hx) hx

/-- Choose one connected cover from an admissible cover family over a target
union in its image.  This is intentionally noncomputable and local to the
finite Fubini/lumping construction. -/
noncomputable def appendixFConnectedCoverFamilyTargetChoice
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (support : ι → Finset Site) (Γ : Finset (Finset ι))
    (Y : Finset Site) (hY : Y ∈ Γ.image (appendixFCoverUnion support)) :
    Finset ι :=
  Classical.choose (Finset.mem_image.mp hY)

theorem appendixFConnectedCoverFamilyTargetChoice_spec
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (support : ι → Finset Site) (Γ : Finset (Finset ι))
    (Y : Finset Site) (hY : Y ∈ Γ.image (appendixFCoverUnion support)) :
    appendixFConnectedCoverFamilyTargetChoice support Γ Y hY ∈ Γ ∧
      appendixFCoverUnion support
        (appendixFConnectedCoverFamilyTargetChoice support Γ Y hY) = Y := by
  classical
  exact Classical.choose_spec (Finset.mem_image.mp hY)

/-- The inverse finite Fubini datum attached to an admissible connected-cover
family: targets are the cover unions, and each target carries a chosen cover
from its fiber. -/
noncomputable def appendixFConnectedCoverFamilyTargetChoiceSigma
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (support : ι → Finset Site) (Γ : Finset (Finset ι)) :
    Σ Υ : Finset (Finset Site), ∀ Y, Y ∈ Υ → Finset ι :=
  ⟨Γ.image (appendixFCoverUnion support),
    appendixFConnectedCoverFamilyTargetChoice support Γ⟩

theorem appendixFConnectedCoverFamilyTargetChoiceSigma_mem_choices
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    {Γ : Finset (Finset ι)}
    (hΓ : Γ ∈ appendixFAdmissibleConnectedCoverFamilies Ω support Λ) :
    appendixFConnectedCoverFamilyTargetChoiceSigma support Γ ∈
      appendixFAdmissibleTargetChoices Ω support Λ := by
  classical
  rw [mem_appendixFAdmissibleTargetChoices_iff]
  refine ⟨image_coverUnion_mem_appendixFAdmissibleTargetFamilies
    Ω support Λ hΓ, ?_⟩
  intro Y hY
  rw [mem_appendixFTargetFiber_iff]
  have hspec :=
    appendixFConnectedCoverFamilyTargetChoice_spec support Γ Y hY
  rw [mem_appendixFAdmissibleConnectedCoverFamilies_iff] at hΓ
  exact ⟨hΓ.1 hspec.1, hspec.2⟩

theorem appendixFTargetChoiceCoverFamily_connectedCoverFamilyTargetChoiceSigma_eq
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty)
    {Γ : Finset (Finset ι)}
    (hΓ : Γ ∈ appendixFAdmissibleConnectedCoverFamilies Ω support Λ) :
    appendixFTargetChoiceCoverFamily
      (appendixFConnectedCoverFamilyTargetChoiceSigma support Γ) = Γ := by
  classical
  ext C
  constructor
  · intro hC
    rw [appendixFTargetChoiceCoverFamily,
      appendixFConnectedCoverFamilyTargetChoiceSigma] at hC
    rcases Finset.mem_image.mp hC with ⟨Y, _hY, hCY⟩
    rw [← hCY]
    exact (appendixFConnectedCoverFamilyTargetChoice_spec
      support Γ Y.1 Y.2).1
  · intro hCΓ
    rw [appendixFTargetChoiceCoverFamily,
      appendixFConnectedCoverFamilyTargetChoiceSigma]
    let Y : Finset Site := appendixFCoverUnion support C
    have hY : Y ∈ Γ.image (appendixFCoverUnion support) :=
      Finset.mem_image.mpr ⟨C, hCΓ, rfl⟩
    refine Finset.mem_image.mpr ⟨⟨Y, hY⟩, by simp, ?_⟩
    have hspec :=
      appendixFConnectedCoverFamilyTargetChoice_spec support Γ Y hY
    exact appendixFCoverUnion_injective_on_admissibleConnectedCoverFamily
      Ω support Λ hactive hΓ hspec.1 hCΓ hspec.2

/-- The target labels carried by a target-choice family are exactly the target
unions of its selected connected covers. -/
theorem appendixFTargetChoiceCoverFamily_image_coverUnion_eq
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    {Ξ : Σ Υ : Finset (Finset Site), ∀ Y, Y ∈ Υ → Finset ι}
    (hΞ : Ξ ∈ appendixFAdmissibleTargetChoices Ω support Λ) :
    (appendixFTargetChoiceCoverFamily Ξ).image (appendixFCoverUnion support) = Ξ.1 := by
  classical
  rw [mem_appendixFAdmissibleTargetChoices_iff] at hΞ
  ext Y
  constructor
  · intro hY
    rcases Finset.mem_image.mp hY with ⟨C, hC, hCY⟩
    rw [appendixFTargetChoiceCoverFamily] at hC
    rcases Finset.mem_image.mp hC with ⟨Z, _hZ, hZC⟩
    have hZfiber := (mem_appendixFTargetFiber_iff Ω support support Λ
      Z.1 (Ξ.2 Z.1 Z.2)).mp (hΞ.2 Z.1 Z.2)
    have hYZ : Y = Z.1 := by
      exact hCY.symm.trans
        ((congrArg (appendixFCoverUnion support) hZC.symm).trans hZfiber.2)
    rw [hYZ]
    exact Z.2
  · intro hY
    refine Finset.mem_image.mpr ⟨Ξ.2 Y hY, ?_, ?_⟩
    · rw [appendixFTargetChoiceCoverFamily]
      exact Finset.mem_image.mpr ⟨⟨Y, hY⟩, by simp, rfl⟩
    · exact ((mem_appendixFTargetFiber_iff Ω support support Λ
        Y (Ξ.2 Y hY)).mp (hΞ.2 Y hY)).2

/-- Reconstructing the inverse target-choice datum from the erased connected
cover family recovers the original target choice.  This is the dependent
left-inverse needed for the finite Fubini/lumping reindexing. -/
theorem appendixFConnectedCoverFamilyTargetChoiceSigma_targetChoiceCoverFamily_eq
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty)
    {Ξ : Σ Υ : Finset (Finset Site), ∀ Y, Y ∈ Υ → Finset ι}
    (hΞ : Ξ ∈ appendixFAdmissibleTargetChoices Ω support Λ) :
    appendixFConnectedCoverFamilyTargetChoiceSigma support
      (appendixFTargetChoiceCoverFamily Ξ) = Ξ := by
  classical
  cases Ξ with
  | mk Υ choice =>
    let Γ : Finset (Finset ι) := appendixFTargetChoiceCoverFamily (Sigma.mk Υ choice)
    have hΞ' : Sigma.mk Υ choice ∈
        appendixFAdmissibleTargetChoices Ω support Λ := hΞ
    have hΓ : Γ ∈ appendixFAdmissibleConnectedCoverFamilies Ω support Λ :=
      appendixFTargetChoiceCoverFamily_mem_admissible Ω support Λ hΞ'
    have hfirst :
        (appendixFConnectedCoverFamilyTargetChoiceSigma support Γ).1 = Υ := by
      simpa [Γ, appendixFConnectedCoverFamilyTargetChoiceSigma]
        using appendixFTargetChoiceCoverFamily_image_coverUnion_eq Ω support Λ hΞ'
    change appendixFConnectedCoverFamilyTargetChoiceSigma support Γ =
      Sigma.mk Υ choice
    refine Sigma.ext hfirst ?_
    let left := (appendixFConnectedCoverFamilyTargetChoiceSigma support Γ).2
    let hty := congrArg (fun U : Finset (Finset Site) =>
      ((Y : Finset Site) → Y ∈ U → Finset ι)) hfirst
    have hcast : cast hty left = choice := by
      funext Y hY
      let hYleft : Y ∈ (appendixFConnectedCoverFamilyTargetChoiceSigma support Γ).1 := by
        rw [hfirst]
        exact hY
      have happly : cast hty left Y hY = left Y hYleft := by
        simpa [hty, hYleft] using
          cast_forall_mem_finset_apply (α := Finset Site) (β := Finset ι)
            hfirst left Y hY
      rw [happly]
      have hspec :=
        appendixFConnectedCoverFamilyTargetChoice_spec support Γ Y hYleft
      have hchoice_mem : choice Y hY ∈ Γ := by
        dsimp [Γ, appendixFTargetChoiceCoverFamily]
        exact Finset.mem_image.mpr ⟨⟨Y, hY⟩, by simp, rfl⟩
      have hchoice_data :=
        (mem_appendixFAdmissibleTargetChoices_iff Ω support Λ
          (Sigma.mk Υ choice :
            Sigma (fun Υ : Finset (Finset Site) =>
              ∀ Y, Y ∈ Υ → Finset ι))).mp hΞ'
      have hchoice_cover : appendixFCoverUnion support (choice Y hY) = Y :=
        ((mem_appendixFTargetFiber_iff Ω support support Λ Y
          (choice Y hY)).mp (hchoice_data.2 Y hY)).2
      exact appendixFCoverUnion_injective_on_admissibleConnectedCoverFamily
        Ω support Λ hactive hΓ hspec.1 hchoice_mem
        (hspec.2.trans hchoice_cover.symm)
    exact HEq.trans (HEq.symm (cast_heq hty left)) (heq_of_eq hcast)

/-- The explicit finite Fubini target-choice sum is exactly the connected-cover
family sum.  This is the last single-support finite lumping step before the
target hard-core partition can be identified with the raw Mayer product. -/
theorem sum_appendixFAdmissibleTargetChoices_eq_sum_admissibleConnectedCoverFamilies
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (w : ι → ℂ)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty) :
    (∑ Ξ ∈ appendixFAdmissibleTargetChoices Ω support Λ,
        ∏ Y ∈ Ξ.1.attach, ∏ i ∈ Ξ.2 Y.1 Y.2, w i) =
      ∑ Γ ∈ appendixFAdmissibleConnectedCoverFamilies Ω support Λ,
        appendixFCoverFamilyWeight w Γ := by
  classical
  refine Finset.sum_bij'
    (fun Ξ _hΞ => appendixFTargetChoiceCoverFamily Ξ)
    (fun Γ _hΓ => appendixFConnectedCoverFamilyTargetChoiceSigma support Γ)
    ?_ ?_ ?_ ?_ ?_
  · intro Ξ hΞ
    exact appendixFTargetChoiceCoverFamily_mem_admissible Ω support Λ hΞ
  · intro Γ hΓ
    exact appendixFConnectedCoverFamilyTargetChoiceSigma_mem_choices
      Ω support Λ hΓ
  · intro Ξ hΞ
    exact appendixFConnectedCoverFamilyTargetChoiceSigma_targetChoiceCoverFamily_eq
      Ω support Λ hactive hΞ
  · intro Γ hΓ
    exact appendixFTargetChoiceCoverFamily_connectedCoverFamilyTargetChoiceSigma_eq
      Ω support Λ hactive hΓ
  · intro Ξ hΞ
    exact (appendixFCoverFamilyWeight_targetChoiceCoverFamily_eq
      Ω support Λ w hΞ).symm

/-- Combining product expansion over target fibers with the finite Fubini
reindexing gives the single-support target-family form of the Appendix-F
connected-cover identity. -/
theorem sum_admissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_admissibleConnectedCoverFamilies
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (w : ι → ℂ)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty) :
    (∑ Υ ∈ appendixFAdmissibleTargetFamilies Ω support Λ,
        ∏ Y ∈ Υ, appendixFConnectedMayerActivity Ω support support Λ w Y) =
      ∑ Γ ∈ appendixFAdmissibleConnectedCoverFamilies Ω support Λ,
        appendixFCoverFamilyWeight w Γ := by
  rw [sum_admissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_targetChoices]
  exact sum_appendixFAdmissibleTargetChoices_eq_sum_admissibleConnectedCoverFamilies
    Ω support Λ w hactive

theorem no_adj_of_omegaCoverUnion_disjoint
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site)
    {C D : Finset ι}
    (hdisj : Disjoint (Ω ∩ appendixFCoverUnion support C)
      (Ω ∩ appendixFCoverUnion support D))
    {i j : ι} (hi : i ∈ C) (hj : j ∈ D) :
    ¬ (omegaOverlapGraph Ω support).Adj i j := by
  classical
  rw [omegaOverlapGraph_adj_iff]
  intro hadj
  apply hadj.2
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rcases Finset.mem_inter.mp hxi with ⟨hxΩ, hxis⟩
  rcases Finset.mem_inter.mp hxj with ⟨_hxΩ', hxjs⟩
  exact (Finset.disjoint_left.mp hdisj
    (Finset.mem_inter.mpr
      ⟨hxΩ, Finset.mem_biUnion.mpr ⟨i, hi, hxis⟩⟩))
    (Finset.mem_inter.mpr
      ⟨hxΩ, Finset.mem_biUnion.mpr ⟨j, hj, hxjs⟩⟩)

/-- The canonical component families are exactly the finite families of
nonempty `Ω`-connected covers whose declared-support unions are pairwise
`Ω`-disjoint for the same support map that defines the overlap graph.  This is
the finite inverse needed before any later target-activity Fubini step; using a
different full `targetSupport` remains an additional statement, not this one. -/
theorem appendixFCanonicalCoverFamilies_eq_admissibleConnectedCoverFamilies
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι) :
    appendixFCanonicalCoverFamilies (omegaOverlapGraph Ω support) Λ =
      appendixFAdmissibleConnectedCoverFamilies Ω support Λ := by
  classical
  ext Γ
  constructor
  · intro hΓ
    rw [mem_appendixFAdmissibleConnectedCoverFamilies_iff]
    refine ⟨?_, ?_⟩
    · intro C hC
      rw [mem_appendixFConnectedCoverRegion_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        exact (biUnion_subset_of_mem_appendixFCanonicalCoverFamilies
          (omegaOverlapGraph Ω support) Λ hΓ)
          (Finset.mem_biUnion.mpr ⟨C, hC, hi⟩)
      · exact nonempty_of_mem_appendixFCanonicalCoverFamily
          (omegaOverlapGraph Ω support) Λ hΓ hC
      · exact walkConnected_of_mem_appendixFCanonicalCoverFamily
          (omegaOverlapGraph Ω support) Λ hΓ hC
    · intro C hC D hD hCD
      exact appendixFCanonicalComponents_omegaSupport_disjoint
        Ω support Λ hΓ hC hD hCD
  · intro hΓ
    rw [mem_appendixFAdmissibleConnectedCoverFamilies_iff] at hΓ
    let G := omegaOverlapGraph Ω support
    let U : Finset ι := Γ.biUnion id
    have hUΛ : U ∈ Λ.powerset := by
      rw [Finset.mem_powerset]
      intro i hiU
      rcases Finset.mem_biUnion.mp hiU with ⟨C, hCΓ, hiC⟩
      have hCreg := hΓ.1 hCΓ
      exact ((mem_appendixFConnectedCoverRegion_iff Ω support Λ C).mp hCreg).1 hiC
    have hmemConf : ∀ C ∈ Γ, C ∈ confinedComponents G U := by
      intro C hCΓ
      have hCreg := hΓ.1 hCΓ
      have hCdata :=
        (mem_appendixFConnectedCoverRegion_iff Ω support Λ C).mp hCreg
      have hCU : C ⊆ U := by
        intro i hiC
        exact Finset.mem_biUnion.mpr ⟨C, hCΓ, hiC⟩
      have hno : ∀ x, x ∈ C → ∀ y, y ∈ U → y ∉ C → ¬ G.Adj x y := by
        intro x hxC y hyU hyC
        rcases Finset.mem_biUnion.mp hyU with ⟨D, hDΓ, hyD⟩
        have hDC : D ≠ C := by
          intro hDC
          subst D
          exact hyC hyD
        have hCD : C ≠ D := hDC ∘ Eq.symm
        have hdisj := hΓ.2 C hCΓ D hDΓ hCD
        simpa [G] using
          no_adj_of_omegaCoverUnion_disjoint Ω support hdisj hxC hyD
      rcases confinedComponent_eq_of_connected_no_exit G U C hCU hCdata.2.1
          hCdata.2.2 hno with ⟨r, hrU, hrCeq⟩
      rw [mem_confinedComponents_iff]
      exact ⟨r, hrU, hrCeq.symm⟩
    rw [mem_appendixFCanonicalCoverFamilies_iff]
    refine ⟨U, hUΛ, ?_⟩
    ext C
    constructor
    · intro hCΓ
      exact hmemConf C hCΓ
    · intro hCconf
      have hCnonempty := nonempty_of_mem_confinedComponents G U C hCconf
      rcases hCnonempty with ⟨r, hrC⟩
      have hrU : r ∈ U := subset_of_mem_confinedComponents G U hCconf hrC
      rcases Finset.mem_biUnion.mp hrU with ⟨D, hDΓ, hrD⟩
      have hDconf := hmemConf D hDΓ
      have hCD : C = D :=
        confinedComponents_eq_of_nonempty_inter G U hCconf hDconf
          ⟨r, hrC, hrD⟩
      rw [hCD]
      exact hDΓ

/-- Product-form finite Appendix-F identity after closing the component-family
inverse: the raw finite gas is the sum over admissible connected-cover
families. -/
theorem prod_one_add_eq_sum_appendixFAdmissibleConnectedCoverFamilies
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site)
    (Λ : Finset ι) (w : ι → ℂ) :
    (∏ i ∈ Λ, (1 + w i)) =
      ∑ Γ ∈ appendixFAdmissibleConnectedCoverFamilies Ω support Λ,
        appendixFCoverFamilyWeight w Γ := by
  classical
  have hfac : ∀ i ∈ Λ, (1 + w i : ℂ) = w i + 1 := by
    intro i _hi
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_add]
  calc
    (∑ x ∈ Λ.powerset, (∏ i ∈ x, w i) * ∏ i ∈ Λ \ x, (1 : ℂ))
        = ∑ x ∈ Λ.powerset, ∏ i ∈ x, w i := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [Finset.prod_const_one, mul_one]
    _ = ∑ Γ ∈ appendixFCanonicalCoverFamilies
          (omegaOverlapGraph Ω support) Λ,
        appendixFCoverFamilyWeight w Γ :=
          sum_powerset_eq_sum_appendixFCanonicalCoverFamilies
            (omegaOverlapGraph Ω support) Λ w
    _ = ∑ Γ ∈ appendixFAdmissibleConnectedCoverFamilies Ω support Λ,
        appendixFCoverFamilyWeight w Γ := by
          rw [appendixFCanonicalCoverFamilies_eq_admissibleConnectedCoverFamilies
            Ω support Λ]

/-- The single-support finite Appendix-F target gas has the same partition
function as the raw finite Mayer product.  This closes the finite
target-family Fubini/lumping identity for the case where the same support map
controls connectivity and target unions. -/
theorem prod_one_add_eq_appendixFTargetPolymerSystem_partition
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site)
    (Λ : Finset ι) (w : ι → ℂ)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty) :
    (∏ i ∈ Λ, (1 + w i)) =
      KP.partition (appendixFTargetPolymerSystem Ω support Λ w hactive) Finset.univ := by
  classical
  have hprod :=
    prod_one_add_eq_sum_appendixFAdmissibleConnectedCoverFamilies
      Ω support Λ w
  have hpart :
      KP.partition (appendixFTargetPolymerSystem Ω support Λ w hactive) Finset.univ =
        ∑ Γ ∈ appendixFAdmissibleConnectedCoverFamilies Ω support Λ,
          appendixFCoverFamilyWeight w Γ := by
    calc
      KP.partition (appendixFTargetPolymerSystem Ω support Λ w hactive) Finset.univ
          =
        ∑ Υ ∈ appendixFAdmissibleTargetFamilies Ω support Λ,
          ∏ Y ∈ Υ, appendixFConnectedMayerActivity Ω support support Λ w Y :=
            appendixFTargetPolymerSystem_partition_eq_sum_admissibleTargetFamilies
              Ω support Λ w hactive
      _ =
        ∑ Γ ∈ appendixFAdmissibleConnectedCoverFamilies Ω support Λ,
          appendixFCoverFamilyWeight w Γ :=
            sum_admissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_admissibleConnectedCoverFamilies
              Ω support Λ w hactive
  exact hprod.trans hpart.symm

/-- Exponential specialization of the finite target-gas identity.  This is
still only the exact finite first Mayer/Appendix-F target identity, not the
metric bound, integration step, second Ursell expansion, or Yang-Mills
activity producer. -/
theorem complex_exp_sum_eq_appendixFTargetPolymerSystem_partition
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (support : ι → Finset Site) (Λ : Finset ι)
    (h : ι → ℂ)
    (hactive : ∀ i, i ∈ Λ → (Ω ∩ support i).Nonempty) :
    Complex.exp (∑ i ∈ Λ, h i) =
      KP.partition
        (appendixFTargetPolymerSystem Ω support Λ
          (fun i => Complex.exp (h i) - 1) hactive)
        Finset.univ := by
  classical
  rw [Complex.exp_sum]
  have hprod :
      (∏ i ∈ Λ, Complex.exp (h i)) =
        ∏ i ∈ Λ, (1 + (Complex.exp (h i) - 1)) := by
    refine Finset.prod_congr rfl ?_
    intro i _hi
    ring
  rw [hprod]
  exact prod_one_add_eq_appendixFTargetPolymerSystem_partition
    Ω support Λ (fun i => Complex.exp (h i) - 1) hactive

/-- Every component appearing in a canonical Appendix-F family is one of the
connected covers admitted by `appendixFConnectedCoverRegion`. -/
theorem mem_appendixFConnectedCoverRegion_of_mem_canonicalComponent
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site) (overlapSupport : ι → Finset Site) (Λ : Finset ι)
    {Γ : Finset (Finset ι)}
    (hΓ : Γ ∈ appendixFCanonicalCoverFamilies
      (omegaOverlapGraph Ω overlapSupport) Λ)
    {C : Finset ι} (hC : C ∈ Γ) :
    C ∈ appendixFConnectedCoverRegion Ω overlapSupport Λ := by
  rw [mem_appendixFConnectedCoverRegion_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact (biUnion_subset_of_mem_appendixFCanonicalCoverFamilies
      (omegaOverlapGraph Ω overlapSupport) Λ hΓ)
      (Finset.mem_biUnion.mpr ⟨C, hC, hi⟩)
  · exact nonempty_of_mem_appendixFCanonicalCoverFamily
      (omegaOverlapGraph Ω overlapSupport) Λ hΓ hC
  · exact walkConnected_of_mem_appendixFCanonicalCoverFamily
      (omegaOverlapGraph Ω overlapSupport) Λ hΓ hC

/-! ## Concrete adapter to the existing with-holes carrier -/

/-- In the concrete `omegaHolePolymerSystem`, using the skeleton as overlap
support and `univ` as the explicit active region reproduces its literal
incompatibility relation (apart from the graph's required inequality of
indices). -/
@[simp] theorem omegaOverlapGraph_univ_skeleton_adj_iff
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (X Y : (omegaHolePolymerSystem HF z).Polymer) :
    (omegaOverlapGraph (Finset.univ : Finset (Cube d L))
      (fun P : (omegaHolePolymerSystem HF z).Polymer => skeleton HF P.val)).Adj X Y
      ↔ X ≠ Y ∧ (omegaHolePolymerSystem HF z).incomp X Y := by
  rw [omegaOverlapGraph_adj_iff, omegaHolePolymerSystem_incomp_iff]
  simp

/-- The first Appendix-F connected activity on the repository's concrete
with-holes polymer carrier.  Connectivity is through active skeletons, while
the target `Y` is the union of the full polymers, exactly as in (639)--(640). -/
noncomputable def appendixFHoleConnectedActivity
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (omegaHolePolymerSystem HF z).Polymer)
    (h : (omegaHolePolymerSystem HF z).Polymer → ℂ)
    (Y : Finset (Cube d L)) : ℂ :=
  appendixFConnectedActivity
    (Finset.univ : Finset (Cube d L))
    (fun P : (omegaHolePolymerSystem HF z).Polymer => skeleton HF P.val)
    (fun P : (omegaHolePolymerSystem HF z).Polymer => P.val)
    Λ h Y

/-- Concrete local influence for the with-holes first connected activity. -/
theorem appendixFHoleConnectedActivity_congr
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (omegaHolePolymerSystem HF z).Polymer)
    (h₁ h₂ : (omegaHolePolymerSystem HF z).Polymer → ℂ)
    (Y : Finset (Cube d L))
    (heq : ∀ X, X ∈ Λ → X.val ⊆ Y → h₁ X = h₂ X) :
    appendixFHoleConnectedActivity HF z Λ h₁ Y =
      appendixFHoleConnectedActivity HF z Λ h₂ Y := by
  exact appendixFConnectedActivity_congr
    (Finset.univ : Finset (Cube d L))
    (fun P : (omegaHolePolymerSystem HF z).Polymer => skeleton HF P.val)
    (fun P : (omegaHolePolymerSystem HF z).Polymer => P.val)
    Λ h₁ h₂ Y heq

end YangMills.RG
