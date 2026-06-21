/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.KP.RootedChildCount
import YangMills.KP.PinnedWalk
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Rooted leaf summation profiles

This module isolates the finite combinatorics behind the degree-sensitive
Appendix-F leaf summation.  The key bookkeeping object is a parent map on the
`n` nonroot labels.  Grouping such maps by their child-count profile leaves a
single `n!` cost per profile; stars-and-bars gives at most `4^n` profiles.

No analytic KP estimate, source theorem, or Yang-Mills claim is introduced.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open SimpleGraph
open scoped BigOperators

variable {n : ℕ}

/-- Fibers of an abstract parent map on the `n` nonroot labels. -/
noncomputable def parentMapFiber
    (p : Fin n → Fin (n + 1)) (v : Fin (n + 1)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => p i = v)

/-- Child-count profile of an abstract parent map on the `n` nonroot labels. -/
noncomputable def parentMapChildCount
    (p : Fin n → Fin (n + 1)) (v : Fin (n + 1)) : ℕ :=
  (parentMapFiber p v).card

@[simp] theorem mem_parentMapFiber
    (p : Fin n → Fin (n + 1)) (v : Fin (n + 1)) (i : Fin n) :
    i ∈ parentMapFiber p v ↔ p i = v := by
  classical
  simp [parentMapFiber]

/-- The fibers of a parent map partition the nonroot labels. -/
theorem sum_parentMapChildCount_eq (p : Fin n → Fin (n + 1)) :
    (∑ v : Fin (n + 1), parentMapChildCount p v) = n := by
  classical
  have hmaps :
      Set.MapsTo p (↑(Finset.univ : Finset (Fin n)))
        (↑(Finset.univ : Finset (Fin (n + 1)))) := by
    intro i _hi
    exact Finset.mem_univ _
  have hfiber := Finset.card_eq_sum_card_fiberwise hmaps
  simpa [parentMapChildCount, parentMapFiber, Finset.card_univ,
    Fintype.card_fin] using hfiber.symm

/-- Disjoint fiber-family data with a prescribed profile. -/
def IsParentFiberFamily
    (m : Fin (n + 1) → ℕ) (ρ : Fin (n + 1) → Finset (Fin n)) : Prop :=
  (∀ u v : Fin (n + 1), u ≠ v → Disjoint (ρ u) (ρ v)) ∧
    (Finset.univ : Finset (Fin (n + 1))).biUnion ρ =
      (Finset.univ : Finset (Fin n)) ∧
    ∀ v : Fin (n + 1), (ρ v).card = m v

/-- The increasing enumeration of a parent-fiber block. -/
def IsParentFiberFamily.fiberEmb
    {m : Fin (n + 1) → ℕ} {ρ : Fin (n + 1) → Finset (Fin n)}
    (hρ : IsParentFiberFamily m ρ) (v : Fin (n + 1)) :
    Fin (m v) ↪o Fin n :=
  Finset.orderEmbOfFin (ρ v) (hρ.2.2 v)

lemma IsParentFiberFamily.fiberEmb_mem
    {m : Fin (n + 1) → ℕ} {ρ : Fin (n + 1) → Finset (Fin n)}
    (hρ : IsParentFiberFamily m ρ) (v : Fin (n + 1)) (j : Fin (m v)) :
    hρ.fiberEmb v j ∈ ρ v :=
  Finset.orderEmbOfFin_mem _ _ _

/-- List each fiber in increasing order, twisted by a local permutation. -/
def IsParentFiberFamily.placeFun
    {m : Fin (n + 1) → ℕ} {ρ : Fin (n + 1) → Finset (Fin n)}
    (hρ : IsParentFiberFamily m ρ)
    (π : ∀ v : Fin (n + 1), Equiv.Perm (Fin (m v))) :
    (Σ v : Fin (n + 1), Fin (m v)) → Fin n :=
  fun x => hρ.fiberEmb x.1 ((π x.1) x.2)

lemma IsParentFiberFamily.placeFun_mem
    {m : Fin (n + 1) → ℕ} {ρ : Fin (n + 1) → Finset (Fin n)}
    (hρ : IsParentFiberFamily m ρ)
    (π : ∀ v : Fin (n + 1), Equiv.Perm (Fin (m v)))
    (x : Σ v : Fin (n + 1), Fin (m v)) :
    hρ.placeFun π x ∈ ρ x.1 :=
  hρ.fiberEmb_mem x.1 ((π x.1) x.2)

lemma IsParentFiberFamily.placeFun_injective
    {m : Fin (n + 1) → ℕ} {ρ : Fin (n + 1) → Finset (Fin n)}
    (hρ : IsParentFiberFamily m ρ)
    (π : ∀ v : Fin (n + 1), Equiv.Perm (Fin (m v))) :
    Function.Injective (hρ.placeFun π) := by
  rintro ⟨u, i⟩ ⟨v, j⟩ h
  by_cases huv : u = v
  · subst v
    have hij : (π u) i = (π u) j :=
      (hρ.fiberEmb u).injective h
    have hij' : i = j := (π u).injective hij
    subst j
    rfl
  · have hu : hρ.placeFun π ⟨u, i⟩ ∈ ρ u :=
      hρ.placeFun_mem π ⟨u, i⟩
    have hv : hρ.placeFun π ⟨v, j⟩ ∈ ρ v :=
      hρ.placeFun_mem π ⟨v, j⟩
    rw [h] at hu
    exact False.elim ((Finset.disjoint_left.mp (hρ.1 u v huv)) hu hv)

open Classical in
/-- Fixed-profile parent-fiber families cost at most one global permutation
factor.  This is the no-root analogue of the block-counting lemma used in the
sharp shell recursion. -/
theorem card_parentFiberFamily_mul_prod_factorial_le
    (m : Fin (n + 1) → ℕ) (hsum : ∑ v : Fin (n + 1), m v = n) :
    (((Finset.univ : Finset (Fin (n + 1) → Finset (Fin n))).filter
      (fun ρ => IsParentFiberFamily m ρ)).card *
        ∏ v : Fin (n + 1), (m v).factorial)
      ≤ n.factorial := by
  classical
  have hcardSig : Fintype.card (Σ v : Fin (n + 1), Fin (m v)) = n := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact hsum
  have e₀ : (Σ v : Fin (n + 1), Fin (m v)) ≃ Fin n :=
    Fintype.equivOfCardEq (by rw [hcardSig, Fintype.card_fin])
  set enc :
      (Fin (n + 1) → Finset (Fin n)) ×
          (∀ v : Fin (n + 1), Equiv.Perm (Fin (m v)))
        → ((Σ v : Fin (n + 1), Fin (m v)) ≃ Fin n) :=
    fun ρπ => if h : IsParentFiberFamily m ρπ.1
      then Equiv.ofBijective (h.placeFun ρπ.2)
        ((Fintype.bijective_iff_injective_and_card _).mpr
          ⟨h.placeFun_injective ρπ.2,
            by rw [hcardSig, Fintype.card_fin]⟩)
      else e₀ with henc
  have hblock : ∀ (ρ : Fin (n + 1) → Finset (Fin n))
      (h : IsParentFiberFamily m ρ)
      (π : ∀ v : Fin (n + 1), Equiv.Perm (Fin (m v)))
      (v : Fin (n + 1)),
      ρ v = Finset.univ.image
        (fun j : Fin (m v) => h.placeFun π ⟨v, j⟩) := by
    intro ρ h π v
    have hinj : Function.Injective
        (fun j : Fin (m v) => h.placeFun π ⟨v, j⟩) := by
      intro j₁ j₂ hj
      have h2 := h.placeFun_injective π hj
      exact eq_of_heq (Sigma.mk.inj_iff.mp h2).2
    have hsub : Finset.univ.image
        (fun j : Fin (m v) => h.placeFun π ⟨v, j⟩) ⊆ ρ v := by
      intro x hx
      obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
      exact h.placeFun_mem π ⟨v, j⟩
    have hcard : (ρ v).card ≤
        (Finset.univ.image
          (fun j : Fin (m v) => h.placeFun π ⟨v, j⟩)).card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
        Fintype.card_fin, h.2.2 v]
    exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
  have hinjOn : ∀ pq₁ ∈ ((Finset.univ :
      Finset (Fin (n + 1) → Finset (Fin n))).filter
        (fun ρ => IsParentFiberFamily m ρ)) ×ˢ
      (Finset.univ :
        Finset (∀ v : Fin (n + 1), Equiv.Perm (Fin (m v)))),
      ∀ pq₂ ∈ ((Finset.univ :
        Finset (Fin (n + 1) → Finset (Fin n))).filter
          (fun ρ => IsParentFiberFamily m ρ)) ×ˢ
        (Finset.univ :
          Finset (∀ v : Fin (n + 1), Equiv.Perm (Fin (m v)))),
      enc pq₁ = enc pq₂ → pq₁ = pq₂ := by
    intro pq₁ h₁ pq₂ h₂ heq
    obtain ⟨ρ₁, π₁⟩ := pq₁
    obtain ⟨ρ₂, π₂⟩ := pq₂
    rw [Finset.mem_product, Finset.mem_filter] at h₁ h₂
    have hf₁ : IsParentFiberFamily m ρ₁ := h₁.1.2
    have hf₂ : IsParentFiberFamily m ρ₂ := h₂.1.2
    rw [henc] at heq
    simp only [dif_pos hf₁, dif_pos hf₂] at heq
    have happ : ∀ x, hf₁.placeFun π₁ x = hf₂.placeFun π₂ x := by
      intro x
      exact DFunLike.congr_fun heq x
    have hρ : ρ₁ = ρ₂ := by
      funext v
      rw [hblock ρ₁ hf₁ π₁ v, hblock ρ₂ hf₂ π₂ v]
      exact Finset.image_congr (fun j _ => happ ⟨v, j⟩)
    subst hρ
    have hπ : π₁ = π₂ := by
      funext v
      refine Equiv.ext fun j => ?_
      have hs := happ ⟨v, j⟩
      exact (hf₁.fiberEmb v).injective hs
    rw [hπ]
  calc
    (((Finset.univ : Finset (Fin (n + 1) → Finset (Fin n))).filter
        (fun ρ => IsParentFiberFamily m ρ)).card *
          ∏ v : Fin (n + 1), (m v).factorial)
        =
        (((Finset.univ : Finset (Fin (n + 1) → Finset (Fin n))).filter
          (fun ρ => IsParentFiberFamily m ρ)) ×ˢ
          (Finset.univ :
            Finset (∀ v : Fin (n + 1), Equiv.Perm (Fin (m v))))).card := by
          rw [Finset.card_product, Finset.card_univ]
          congr 1
          rw [Fintype.card_pi]
          exact (Finset.prod_congr rfl fun v _ => by
            rw [Fintype.card_perm, Fintype.card_fin]).symm
    _ ≤ (Finset.univ :
          Finset ((Σ v : Fin (n + 1), Fin (m v)) ≃ Fin n)).card :=
        Finset.card_le_card_of_injOn enc (fun _ _ => Finset.mem_univ _)
          (fun a ha b hb h => hinjOn a (Finset.mem_coe.mp ha) b
            (Finset.mem_coe.mp hb) h)
    _ = n.factorial := by
        rw [Finset.card_univ, Fintype.card_equiv e₀, hcardSig]

/-- Fibers of a parent map form a fiber family with the map's own profile. -/
theorem isParentFiberFamily_parentMap
    (p : Fin n → Fin (n + 1)) :
    IsParentFiberFamily (parentMapChildCount p) (fun v => parentMapFiber p v) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    rw [Finset.disjoint_left]
    intro i hiu hiv
    exact huv ((mem_parentMapFiber p u i).mp hiu |>.symm.trans
      ((mem_parentMapFiber p v i).mp hiv))
  · ext i
    constructor
    · intro _hi
      exact Finset.mem_univ i
    · intro _hi
      rw [Finset.mem_biUnion]
      exact ⟨p i, Finset.mem_univ _, (mem_parentMapFiber p (p i) i).mpr rfl⟩
  · intro v
    rfl

/-- For a fixed profile, parent maps priced by their child-factorials cost at
most one global permutation factor. -/
theorem parentMap_profile_sum_factorial_le
    (m : Fin (n + 1) → ℕ) (hm : ∑ v : Fin (n + 1), m v = n) :
    (∑ p ∈ (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
        (fun p => parentMapChildCount p = m),
      ∏ v : Fin (n + 1), (parentMapChildCount p v).factorial)
      ≤ n.factorial := by
  classical
  set Fams : Finset (Fin (n + 1) → Finset (Fin n)) :=
    (Finset.univ : Finset (Fin (n + 1) → Finset (Fin n))).filter
      (fun ρ => IsParentFiberFamily m ρ) with hFams
  set Maps : Finset (Fin n → Fin (n + 1)) :=
    (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
      (fun p => parentMapChildCount p = m) with hMaps
  have hconst : ∀ p ∈ Maps,
      (∏ v : Fin (n + 1), (parentMapChildCount p v).factorial) =
        ∏ v : Fin (n + 1), (m v).factorial := by
    intro p hp
    rw [hMaps, Finset.mem_filter] at hp
    rw [hp.2]
  have hsum :
      (∑ p ∈ Maps,
        ∏ v : Fin (n + 1), (parentMapChildCount p v).factorial)
      = Maps.card * ∏ v : Fin (n + 1), (m v).factorial := by
    rw [Finset.sum_const_nat]
    intro p hp
    exact hconst p hp
  have hmap : Set.MapsTo (fun p : Fin n → Fin (n + 1) =>
        fun v => parentMapFiber p v) ↑Maps ↑Fams := by
    intro p hp
    refine Finset.mem_coe.mpr ?_
    rw [hFams, Finset.mem_filter]
    have hpFin : p ∈ Maps := Finset.mem_coe.mp hp
    rw [hMaps, Finset.mem_filter] at hpFin
    exact ⟨Finset.mem_univ _, by
      simpa [hpFin.2] using isParentFiberFamily_parentMap p⟩
  have hinj : Set.InjOn (fun p : Fin n → Fin (n + 1) =>
        fun v => parentMapFiber p v) ↑Maps := by
    intro p hp q hq heq
    funext i
    have hi : i ∈ parentMapFiber p (p i) := by
      rw [mem_parentMapFiber]
    have hmem : i ∈ parentMapFiber q (p i) := by
      simpa [congrFun heq (p i)] using hi
    exact ((mem_parentMapFiber q (p i) i).mp hmem).symm
  have hcard : Maps.card ≤ Fams.card :=
    Finset.card_le_card_of_injOn (fun p : Fin n → Fin (n + 1) =>
      fun v => parentMapFiber p v) hmap hinj
  calc
    (∑ p ∈ Maps,
      ∏ v : Fin (n + 1), (parentMapChildCount p v).factorial)
        = Maps.card * ∏ v : Fin (n + 1), (m v).factorial := hsum
    _ ≤ Fams.card * ∏ v : Fin (n + 1), (m v).factorial := by
        exact Nat.mul_le_mul_right _ hcard
    _ ≤ n.factorial := by
        rw [hFams]
        exact card_parentFiberFamily_mul_prod_factorial_le m hm

/-- The set of parent-map profiles has at most `4^n` elements. -/
theorem parentMapProfileCount_le_four_pow (n : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) n).card
      ≤ 4 ^ n := by
  classical
  have hmap := Finset.map_sym_eq_piAntidiag
    (s := (Finset.univ : Finset (Fin (n + 1)))) n
  have hcard :
      (Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) n).card =
        Fintype.card (Sym (Fin (n + 1)) n) := by
    rw [← hmap, Finset.card_map, Finset.sym_univ, Finset.card_univ]
  rw [hcard, Sym.card_sym_eq_choose]
  have hsimp :
      ((Fintype.card (Fin (n + 1)) + n - 1).choose n) =
        (2 * n).choose n := by
    simp [Nat.add_comm, two_mul]
  rw [hsimp]
  calc
    (2 * n).choose n ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow (2 * n) n
    _ = 4 ^ n := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, pow_mul]

/-- Aggregate child-factorial cost over all abstract parent maps. -/
theorem sum_parentMapChildCount_factorialProduct_le_factorial_mul_four_pow
    (n : ℕ) :
    (∑ p : Fin n → Fin (n + 1),
      ∏ v : Fin (n + 1), (parentMapChildCount p v).factorial)
      ≤ n.factorial * 4 ^ n := by
  classical
  let profile : (Fin n → Fin (n + 1)) → (Fin (n + 1) → ℕ) :=
    fun p => parentMapChildCount p
  have hmaps :
      Set.MapsTo profile
        (↑(Finset.univ : Finset (Fin n → Fin (n + 1))))
        (↑(Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) n)) := by
    intro p _hp
    exact Finset.mem_coe.mpr <| by
      rw [Finset.mem_piAntidiag]
      exact ⟨sum_parentMapChildCount_eq p, by
        intro v _hv
        exact Finset.mem_univ v⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun p => ∏ v : Fin (n + 1), (parentMapChildCount p v).factorial)
  calc
    (∑ p : Fin n → Fin (n + 1),
      ∏ v : Fin (n + 1), (parentMapChildCount p v).factorial)
        =
      (∑ m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) n,
        ∑ p ∈ (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
          (fun p => profile p = m),
          ∏ v : Fin (n + 1), (parentMapChildCount p v).factorial) := by
          simpa using hfiber.symm
    _ ≤ ∑ _m ∈ Finset.piAntidiag
            (Finset.univ : Finset (Fin (n + 1))) n, n.factorial := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [Finset.mem_piAntidiag] at hm
          exact parentMap_profile_sum_factorial_le m hm.1
    _ = (Finset.piAntidiag
          (Finset.univ : Finset (Fin (n + 1))) n).card * n.factorial := by
          rw [Finset.sum_const_nat]
          intro _m _hm
          rfl
    _ ≤ (4 ^ n) * n.factorial := by
          exact Nat.mul_le_mul_right _ (parentMapProfileCount_le_four_pow n)
    _ = n.factorial * 4 ^ n := by
          rw [Nat.mul_comm]

/-- The BFS parent of the root is the root itself. -/
lemma rootedLeaf_bfsParent_zero
    (E : Finset (Sym2 (Fin (n + 1)))) :
    bfsParent E 0 = 0 := by
  unfold bfsParent
  rw [dif_neg]
  rintro ⟨u, hu⟩
  rw [mem_bfsParentSet] at hu
  have hlev := hu.2
  rw [bfsLevel_zero_eq] at hlev
  omega

/-- The concrete rooted child counts of a tree are the fiber counts of the
nonroot parent map `i ↦ bfsParent T i.succ`. -/
theorem rootedChildCount_eq_parentMapChildCount_succ
    (T : Finset (Sym2 (Fin (n + 1)))) (v : Fin (n + 1)) :
    rootedChildCount T v =
      parentMapChildCount (fun i : Fin n => bfsParent T i.succ) v := by
  classical
  unfold rootedChildCount parentMapChildCount
  refine Finset.card_bij
    (fun w hw => w.pred (rootedChild_ne_zero (T := T) (v := v) hw))
    ?_ ?_ ?_
  · intro w hw
    rw [mem_parentMapFiber]
    have hparent := rootedChild_parent_eq (T := T) (v := v) hw
    simpa [Fin.succ_pred] using hparent
  · intro w₁ hw₁ w₂ hw₂ heq
    have hsucc := congrArg Fin.succ heq
    simpa [Fin.succ_pred] using hsucc
  · intro i hi
    rw [mem_parentMapFiber] at hi
    have hw : i.succ ∈ rootedChildren T v := by
      rw [mem_rootedChildren]
      exact ⟨Fin.succ_ne_zero i, hi⟩
    refine ⟨i.succ, hw, ?_⟩
    simp

/-- Aggregate rooted child-factorial cost over all complete-graph spanning
trees.  The proof injects each tree into its nonroot BFS parent map and then
uses the parent-profile summation bound. -/
theorem sum_rootedChildCount_factorialProduct_le_factorial_mul_four_pow
    (n : ℕ) :
    (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
      ∏ v : Fin (n + 1), (rootedChildCount T v).factorial)
      ≤ n.factorial * 4 ^ n := by
  classical
  let treeParent :
      Finset (Sym2 (Fin (n + 1))) → Fin n → Fin (n + 1) :=
    fun T i => bfsParent T i.succ
  let F : (Fin n → Fin (n + 1)) → ℕ :=
    fun p => ∏ v : Fin (n + 1), (parentMapChildCount p v).factorial
  have hweight : ∀ T : Finset (Sym2 (Fin (n + 1))),
      (∏ v : Fin (n + 1), (rootedChildCount T v).factorial) =
        F (treeParent T) := by
    intro T
    dsimp [F, treeParent]
    exact Finset.prod_congr rfl fun v _ =>
      congrArg Nat.factorial
        (rootedChildCount_eq_parentMapChildCount_succ T v)
  have hinj : Set.InjOn treeParent
      ↑(spanningTrees (⊤ : SimpleGraph (Fin (n + 1)))) := by
    intro T₁ h₁ T₂ h₂ heq
    have hfull : bfsParent T₁ = bfsParent T₂ := by
      funext v
      by_cases hv : v = 0
      · rw [hv, rootedLeaf_bfsParent_zero T₁,
          rootedLeaf_bfsParent_zero T₂]
      · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hv
        exact congrFun heq i
    have e₁ : penroseTree T₁ = T₁ := penroseTree_of_spanningTree h₁
    have e₂ : penroseTree T₂ = T₂ := penroseTree_of_spanningTree h₂
    rw [← e₁, ← e₂]
    unfold penroseTree
    rw [hfull]
  calc
    (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
      ∏ v : Fin (n + 1), (rootedChildCount T v).factorial)
        = ∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
            F (treeParent T) := by
          exact Finset.sum_congr rfl fun T _ => hweight T
    _ = ∑ p ∈ (spanningTrees (⊤ : SimpleGraph (Fin (n + 1)))).image treeParent,
            F p := by
          exact (Finset.sum_image hinj).symm
    _ ≤ ∑ p : Fin n → Fin (n + 1), F p := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by intro p hp; exact Finset.mem_univ p)
            (fun p _hp _hnot => Nat.zero_le (F p))
    _ ≤ n.factorial * 4 ^ n :=
          sum_parentMapChildCount_factorialProduct_le_factorial_mul_four_pow n

/-- Real normalized form of the aggregate rooted child-factorial tree bound.
This is the form consumed by the second-Ursell `(n+1)!` normalization. -/
theorem rootedChildCount_factorialTreeSum_normalized_le_four_pow
    (n : ℕ) :
    ((n : ℝ) + 1) *
        (((n + 1).factorial : ℝ))⁻¹ *
        (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
          ∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ))
      ≤ (4 : ℝ) ^ n := by
  classical
  have hnat :=
    sum_rootedChildCount_factorialProduct_le_factorial_mul_four_pow n
  have hreal :
      (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
        ∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ))
        ≤ ((n.factorial * 4 ^ n : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hleft :
      0 ≤ ((n : ℝ) + 1) * (((n + 1).factorial : ℝ))⁻¹ := by
    positivity
  calc
    ((n : ℝ) + 1) *
        (((n + 1).factorial : ℝ))⁻¹ *
        (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
          ∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ))
        ≤ ((n : ℝ) + 1) *
            (((n + 1).factorial : ℝ))⁻¹ *
            ((n.factorial * 4 ^ n : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_left hreal hleft
    _ = (4 : ℝ) ^ n := by
          rw [Nat.cast_mul, Nat.cast_pow, Nat.factorial_succ]
          push_cast
          field_simp [show ((n : ℝ) + 1) ≠ 0 by positivity,
            show ((n.factorial : ℝ)) ≠ 0 by positivity]

end YangMills.KP
