/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

/-
# Rooted child-factorial Catalan bridge

This module proves the upstream bridge for the rigidity route, against the real
`YangMills.KP` definitions `spanningTrees`, `bfsParent`, `rootedChildren`, and
`rootedChildCount`.

The main result is the natural-number identity

`sum_prod_rootedChildCount_factorial_eq :
  (sum T in spanningTrees top, prod v, (rootedChildCount T v)!) =
    n! * catalan n`.

The proof builds a bijection between complete-graph spanning trees equipped
with ordered rooted-child fibers and the rooted labeled plane trees counted by
`LabeledPlaneTreeCatalan.lean`.

Expected oracle for the printed bridge theorems:
`[propext, Classical.choice, Quot.sound]`.
-/
import YangMills.KP.RootedChildCount
import YangMills.KP.LabeledPlaneTreeCatalan

open Nat Finset SimpleGraph RootedTreeCatalan LTree

namespace YangMills.KP

variable {n : ℕ}

/-! ### Niveles BFS de los hijos -/

/-- Un hijo BFS vive exactamente un nivel más abajo que su padre. -/
theorem bfsLevel_of_mem_rootedChildren
    {T : Finset (Sym2 (Fin (n + 1)))}
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    {v w : Fin (n + 1)} (hw : w ∈ rootedChildren T v) :
    bfsLevel T w = bfsLevel T v + 1 := by
  have h := (bfsParent_spec hconn (rootedChild_ne_zero hw)).2
  rw [rootedChild_parent_eq hw] at h
  omega

/-- En un grafo conexo sobre `n + 1` vértices, los niveles BFS no superan
`n`. -/
theorem bfsLevel_le_of_connected
    {T : Finset (Sym2 (Fin (n + 1)))}
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    (v : Fin (n + 1)) : bfsLevel T v ≤ n := by
  obtain ⟨w⟩ := hconn.preconnected 0 v
  have h1 : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).dist 0 v
      ≤ w.bypass.length := SimpleGraph.dist_le _
  have h2 := (SimpleGraph.Walk.bypass_isPath w).length_lt
  rw [Fintype.card_fin] at h2
  simp only [bfsLevel]
  omega

/-! ### Recuperación del árbol desde sus aristas-a-padre -/

/-- Un árbol generador tiene exactamente `n` aristas. -/
theorem card_of_mem_spanningTrees
    {T : Finset (Sym2 (Fin (n + 1)))}
    (hT : T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1)))) :
    T.card = n := by
  classical
  have htree := isTree_of_mem_spanningTrees _ hT
  have hset : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).edgeSet
      = (↑T : Set (Sym2 (Fin (n + 1)))) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff, Finset.mem_coe]
    refine ⟨fun h => h.1, fun he => ⟨he, ?_⟩⟩
    have h2 := spanningTrees_subset _ hT he
    rw [SimpleGraph.mem_edgeFinset] at h2
    exact SimpleGraph.not_isDiag_of_mem_edgeSet _ h2
  have hcard := (SimpleGraph.isTree_iff_connected_and_card.mp htree).2
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  omega

/-- **Recuperación**: un árbol generador es exactamente su conjunto de
aristas-a-padre BFS.  Ésta es la mitad "el árbol se recupera del árbol plano"
de la inyectividad del puente. -/
theorem penroseTree_eq_of_mem_spanningTrees
    {T : Finset (Sym2 (Fin (n + 1)))}
    (hT : T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1)))) :
    penroseTree T = T := by
  have hconn := (isTree_of_mem_spanningTrees _ hT).isConnected
  refine Finset.eq_of_subset_of_card_le (penroseTree_subset hconn) ?_
  rw [card_of_mem_spanningTrees hT, penroseTree_card hconn]

/-! ### Órdenes de hijos como listados sin repetición -/

/-- Los listados sin repetición de un `Finset`: imagen inyectiva de las
equivalencias `Fin s.card ≃ s`. -/
noncomputable def fiberListings {α : Type*} [DecidableEq α] (s : Finset α) :
    Finset (List α) :=
  (Finset.univ : Finset (Fin s.card ≃ {x // x ∈ s})).map
    ⟨fun e => List.ofFn (fun i => (e i).val), by
      intro e₁ e₂ h
      have h2 := List.ofFn_inj.mp h
      exact Equiv.ext fun i => Subtype.val_injective (congrFun h2 i)⟩

theorem card_fiberListings {α : Type*} [DecidableEq α] (s : Finset α) :
    (fiberListings s).card = s.card ! := by
  rw [fiberListings, Finset.card_map, Finset.card_univ,
    Fintype.card_equiv s.equivFin.symm, Fintype.card_fin]

/-- Caracterización semántica: son exactamente las listas sin repetición que
enumeran `s`. -/
theorem mem_fiberListings {α : Type*} [DecidableEq α] {s : Finset α}
    {l : List α} :
    l ∈ fiberListings s ↔ l.Nodup ∧ l.toFinset = s := by
  simp only [fiberListings, Finset.mem_map, Function.Embedding.coeFn_mk,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [List.nodup_ofFn]
      exact fun i j hij => e.injective (Subtype.val_injective hij)
    · ext x
      simp only [List.mem_toFinset, List.mem_ofFn', Set.mem_range]
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).property
      · intro hx
        exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  · rintro ⟨hnd, htf⟩
    have hlen : l.length = s.card := by
      rw [← htf, List.toFinset_card_of_nodup hnd]
    have hmem : ∀ i : Fin l.length, l.get i ∈ s := fun i => by
      rw [← htf]
      exact List.mem_toFinset.mpr (l.get_mem i)
    have hinj : Function.Injective
        (fun i : Fin l.length => (⟨l.get i, hmem i⟩ : {x // x ∈ s})) := by
      intro i j hij
      exact List.nodup_iff_injective_get.mp hnd (congrArg Subtype.val hij)
    have hbij := (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, by rw [Fintype.card_fin, Fintype.card_coe, hlen]⟩
    refine ⟨(finCongr hlen.symm).trans (Equiv.ofBijective _ hbij), ?_⟩
    have hfun : (fun i : Fin s.card =>
        (((finCongr hlen.symm).trans (Equiv.ofBijective _ hbij)) i).val)
        = fun i => l.get (Fin.cast hlen.symm i) := rfl
    rw [hfun, ofFn_cast_eq hlen.symm l.get, List.ofFn_get]

/-- Elecciones de orden de hijos para todas las fibras, como listas. -/
noncomputable def childListings (T : Finset (Sym2 (Fin (n + 1)))) :
    Finset (∀ _ : Fin (n + 1), List (Fin (n + 1))) :=
  Fintype.piFinset (fun v => fiberListings (rootedChildren T v))

theorem mem_childListings {T : Finset (Sym2 (Fin (n + 1)))}
    {L : ∀ _ : Fin (n + 1), List (Fin (n + 1))} :
    L ∈ childListings T ↔
      ∀ v, (L v).Nodup ∧ (L v).toFinset = rootedChildren T v := by
  simp only [childListings, Fintype.mem_piFinset, mem_fiberListings]

/-- El número de elecciones de orden es el producto de factoriales de los
conteos de hijos — el mismo peso que cuenta el repo. -/
theorem card_childListings (T : Finset (Sym2 (Fin (n + 1)))) :
    (childListings T).card = ∏ v, (rootedChildCount T v)! := by
  rw [childListings, Fintype.card_piFinset]
  exact Finset.prod_congr rfl fun v _ => card_fiberListings _

/-- **La suma de pesos factoriales es un cardinal**: el del Finset de pares
(árbol generador, listados de hijos).  Con esto, cerrar la identidad se reduce
a una biyección Finset-Finset con `labeledTreesOn n`. -/
theorem sum_prod_factorial_eq_card_sigma_childListings (n : ℕ) :
    (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
        ∏ v, (rootedChildCount T v)!)
      = ((spanningTrees (⊤ : SimpleGraph (Fin (n + 1)))).sigma
          (fun T => childListings T)).card := by
  rw [Finset.card_sigma]
  exact Finset.sum_congr rfl fun T _ => (card_childListings T).symm

/-! ### La definición clave: el árbol plano etiquetado de un árbol ordenado -/

/-- **El árbol plano etiquetado inducido**: el nodo `v` tiene por hijos los
subárboles de sus hijos BFS, en el orden dado por el listado `L v`.  Recursión
bien fundada: los hijos viven un nivel BFS más abajo, y los niveles están
acotados por `n`. -/
noncomputable def orderedBFSTree (T : Finset (Sym2 (Fin (n + 1))))
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    (L : ∀ _ : Fin (n + 1), List (Fin (n + 1)))
    (hL : ∀ v, (L v).toFinset = rootedChildren T v)
    (v : Fin (n + 1)) : LTree (Fin (n + 1)) :=
  LTree.node v (((L v).attach).map (fun w =>
    orderedBFSTree T hconn L hL w.val))
termination_by n + 1 - bfsLevel T v
decreasing_by
  have hw : w.val ∈ rootedChildren T v := by
    rw [← hL v]
    exact List.mem_toFinset.mpr w.property
  have h1 := bfsLevel_of_mem_rootedChildren hconn hw
  have h2 := bfsLevel_le_of_connected hconn v
  omega

@[simp] theorem rootLabel_orderedBFSTree
    (T : Finset (Sym2 (Fin (n + 1))))
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    (L : ∀ _ : Fin (n + 1), List (Fin (n + 1)))
    (hL : ∀ v, (L v).toFinset = rootedChildren T v)
    (v : Fin (n + 1)) :
    (orderedBFSTree T hconn L hL v).rootLabel = v := by
  rw [orderedBFSTree]
  rfl

/-! ### La cadena de padres y la caracterización de las etiquetas -/

theorem labelsForest_eq_flatten {α : Type*} (us : List (LTree α)) :
    labelsForest us = (us.map labels).flatten := by
  induction us with
  | nil => simp
  | cons u us ih => simp [ih]

/-- Iteración del padre BFS. -/
noncomputable def parIter (T : Finset (Sym2 (Fin (n + 1)))) (k : ℕ)
    (w : Fin (n + 1)) : Fin (n + 1) :=
  (bfsParent T)^[k] w

@[simp] theorem parIter_zero (T : Finset (Sym2 (Fin (n + 1))))
    (w : Fin (n + 1)) : parIter T 0 w = w := rfl

theorem parIter_succ (T : Finset (Sym2 (Fin (n + 1)))) (k : ℕ)
    (w : Fin (n + 1)) :
    parIter T (k + 1) w = bfsParent T (parIter T k w) :=
  Function.iterate_succ_apply' _ _ _

/-- Con conectividad, el nivel BFS se anula exactamente en la raíz. -/
theorem bfsLevel_eq_zero_iff {T : Finset (Sym2 (Fin (n + 1)))}
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    {x : Fin (n + 1)} : bfsLevel T x = 0 ↔ x = 0 := by
  constructor
  · intro h
    simp only [bfsLevel] at h
    rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h with h1 | h2
    · exact h1.symm
    · exact absurd (hconn.preconnected 0 x) h2
  · rintro rfl
    exact bfsLevel_zero_eq T

/-- El nivel desciende de uno en uno a lo largo de la cadena de padres. -/
theorem bfsLevel_parIter {T : Finset (Sym2 (Fin (n + 1)))}
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    (w : Fin (n + 1)) :
    ∀ k, k ≤ bfsLevel T w → bfsLevel T (parIter T k w) = bfsLevel T w - k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have hx0 : parIter T k w ≠ 0 := by
      intro h0
      rw [h0, bfsLevel_zero_eq] at h1
      omega
    have hspec := (bfsParent_spec hconn hx0).2
    rw [parIter_succ]
    omega

/-- La cadena de padres alcanza la raíz en `bfsLevel` pasos. -/
theorem parIter_bfsLevel_eq_zero {T : Finset (Sym2 (Fin (n + 1)))}
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    (w : Fin (n + 1)) : parIter T (bfsLevel T w) w = 0 := by
  have h := bfsLevel_parIter hconn w (bfsLevel T w) le_rfl
  exact (bfsLevel_eq_zero_iff hconn).mp (by omega)

/-- **Caracterización de las etiquetas**: `w` aparece en el subárbol plano de
`v` exactamente cuando la cadena de padres de `w` pasa por `v` con el desfase
de niveles correcto. -/
theorem mem_labels_orderedBFSTree
    (T : Finset (Sym2 (Fin (n + 1))))
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    (L : ∀ _ : Fin (n + 1), List (Fin (n + 1)))
    (hL : ∀ v, (L v).toFinset = rootedChildren T v)
    (v w : Fin (n + 1)) :
    w ∈ (orderedBFSTree T hconn L hL v).labels ↔
      ∃ k, parIter T k w = v ∧ bfsLevel T w = bfsLevel T v + k := by
  rw [orderedBFSTree, labels_node, List.mem_cons, labelsForest_eq_flatten]
  constructor
  · rintro (rfl | hmem)
    · exact ⟨0, rfl, by omega⟩
    · rw [List.mem_flatten] at hmem
      obtain ⟨l, hl, hwl⟩ := hmem
      rw [List.mem_map] at hl
      obtain ⟨u, hu, rfl⟩ := hl
      rw [List.mem_map] at hu
      obtain ⟨c, hc, rfl⟩ := hu
      have hcf : c.val ∈ rootedChildren T v := by
        rw [← hL v]
        exact List.mem_toFinset.mpr c.property
      obtain ⟨k, hk1, hk2⟩ :=
        (mem_labels_orderedBFSTree T hconn L hL c.val w).mp hwl
      refine ⟨k + 1, ?_, ?_⟩
      · rw [parIter_succ, hk1]
        exact rootedChild_parent_eq hcf
      · have hlev := bfsLevel_of_mem_rootedChildren hconn hcf
        omega
  · rintro ⟨k, hk1, hk2⟩
    cases k with
    | zero =>
      left
      simpa using hk1
    | succ k =>
      right
      have hlevc : bfsLevel T (parIter T k w) = bfsLevel T v + 1 := by
        have := bfsLevel_parIter hconn w k (by omega)
        omega
      have hc0 : parIter T k w ≠ 0 := by
        intro h0
        rw [h0, bfsLevel_zero_eq] at hlevc
        omega
      have hpar : bfsParent T (parIter T k w) = v := by
        rw [← parIter_succ]
        exact hk1
      have hcf : parIter T k w ∈ rootedChildren T v :=
        (mem_rootedChildren T v _).mpr ⟨hc0, hpar⟩
      have hcl : parIter T k w ∈ L v := by
        rw [← List.mem_toFinset, hL v]
        exact hcf
      have hw : w ∈ (orderedBFSTree T hconn L hL (parIter T k w)).labels :=
        (mem_labels_orderedBFSTree T hconn L hL (parIter T k w) w).mpr
          ⟨k, rfl, by omega⟩
      rw [List.mem_flatten]
      refine ⟨(orderedBFSTree T hconn L hL (parIter T k w)).labels, ?_, hw⟩
      rw [List.mem_map]
      refine ⟨orderedBFSTree T hconn L hL (parIter T k w), ?_, rfl⟩
      rw [List.mem_map]
      exact ⟨⟨parIter T k w, hcl⟩, List.mem_attach _ _, rfl⟩
termination_by n + 1 - bfsLevel T v
decreasing_by
  all_goals
    have h1 := bfsLevel_of_mem_rootedChildren hconn hcf
    have h2 := bfsLevel_le_of_connected hconn v
    omega

/-- Toda etiqueta aparece en el árbol enraizado en `0`. -/
theorem mem_labels_orderedBFSTree_root
    (T : Finset (Sym2 (Fin (n + 1))))
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    (L : ∀ _ : Fin (n + 1), List (Fin (n + 1)))
    (hL : ∀ v, (L v).toFinset = rootedChildren T v)
    (w : Fin (n + 1)) :
    w ∈ (orderedBFSTree T hconn L hL 0).labels := by
  rw [mem_labels_orderedBFSTree]
  exact ⟨bfsLevel T w, parIter_bfsLevel_eq_zero hconn w, by
    rw [bfsLevel_zero_eq]; omega⟩

/-- Las etiquetas del árbol plano inducido no se repiten (para listados sin
repetición): subárboles de hijos distintos son disjuntos, porque la cadena de
padres identifica al hijo por el desfase de niveles. -/
theorem nodup_labels_orderedBFSTree
    (T : Finset (Sym2 (Fin (n + 1))))
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    (L : ∀ _ : Fin (n + 1), List (Fin (n + 1)))
    (hL : ∀ v, (L v).toFinset = rootedChildren T v)
    (hLnd : ∀ v, (L v).Nodup)
    (v : Fin (n + 1)) :
    (orderedBFSTree T hconn L hL v).labels.Nodup := by
  rw [orderedBFSTree, labels_node, labelsForest_eq_flatten, List.nodup_cons,
    List.nodup_flatten]
  refine ⟨?_, ?_, ?_⟩
  · intro hv
    rw [List.mem_flatten] at hv
    obtain ⟨l, hl, hvl⟩ := hv
    rw [List.mem_map] at hl
    obtain ⟨u, hu, rfl⟩ := hl
    rw [List.mem_map] at hu
    obtain ⟨c, hc, rfl⟩ := hu
    have hcf : c.val ∈ rootedChildren T v := by
      rw [← hL v]
      exact List.mem_toFinset.mpr c.property
    obtain ⟨k, -, hk2⟩ :=
      (mem_labels_orderedBFSTree T hconn L hL c.val v).mp hvl
    have hlev := bfsLevel_of_mem_rootedChildren hconn hcf
    omega
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨u, hu, rfl⟩ := hl
    rw [List.mem_map] at hu
    obtain ⟨c, hc, rfl⟩ := hu
    have hcf : c.val ∈ rootedChildren T v := by
      rw [← hL v]
      exact List.mem_toFinset.mpr c.property
    exact nodup_labels_orderedBFSTree T hconn L hL hLnd c.val
  · rw [List.pairwise_map, List.pairwise_map]
    refine List.Pairwise.imp ?_ (List.nodup_attach.mpr (hLnd v))
    intro a b hab
    have hcfa : a.val ∈ rootedChildren T v := by
      rw [← hL v]
      exact List.mem_toFinset.mpr a.property
    have hcfb : b.val ∈ rootedChildren T v := by
      rw [← hL v]
      exact List.mem_toFinset.mpr b.property
    intro x hxa hxb
    obtain ⟨k₁, hk₁, hl₁⟩ :=
      (mem_labels_orderedBFSTree T hconn L hL a.val x).mp hxa
    obtain ⟨k₂, hk₂, hl₂⟩ :=
      (mem_labels_orderedBFSTree T hconn L hL b.val x).mp hxb
    have ha := bfsLevel_of_mem_rootedChildren hconn hcfa
    have hb := bfsLevel_of_mem_rootedChildren hconn hcfb
    have hk : k₁ = k₂ := by omega
    have hval : a.val = b.val := by
      rw [← hk₁, ← hk₂, hk]
    exact hab (Subtype.ext hval)
termination_by n + 1 - bfsLevel T v
decreasing_by
  all_goals
    have h1 := bfsLevel_of_mem_rootedChildren hconn hcf
    have h2 := bfsLevel_le_of_connected hconn v
    omega

/-- **Piedra (D) de (b2)**: el árbol plano etiquetado inducido por un árbol
generador con listados de hijos pertenece a `labeledTreesOn n`. -/
theorem orderedBFSTree_mem_labeledTreesOn
    (T : Finset (Sym2 (Fin (n + 1))))
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    (L : ∀ _ : Fin (n + 1), List (Fin (n + 1)))
    (hL : ∀ v, (L v).toFinset = rootedChildren T v)
    (hLnd : ∀ v, (L v).Nodup) :
    orderedBFSTree T hconn L hL 0 ∈ labeledTreesOn n := by
  rw [mem_labeledTreesOn]
  refine ⟨?_, rootLabel_orderedBFSTree T hconn L hL 0⟩
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact nodup_labels_orderedBFSTree T hconn L hL hLnd 0
  · exact List.nodup_finRange _
  · ext x
    simp only [List.mem_toFinset]
    constructor
    · intro _
      exact List.mem_finRange x
    · intro _
      exact mem_labels_orderedBFSTree_root T hconn L hL x

/-! ### Piedra (E): inyectividad — extracción de los datos desde el árbol -/

section ChildrenOf

variable {α : Type*} [DecidableEq α]

mutual
  /-- Los rótulos de los hijos del (primer) nodo etiquetado `v`. -/
  def childrenOf : LTree α → α → List α
    | LTree.node a cs, v =>
      if a = v then cs.map rootLabel else childrenOfForest cs v
  /-- Búsqueda de `childrenOf` en un bosque: primer subárbol que contiene
  la etiqueta. -/
  def childrenOfForest : List (LTree α) → α → List α
    | [], _ => []
    | u :: us, v =>
      if v ∈ labels u then childrenOf u v else childrenOfForest us v
end

@[simp] theorem childrenOf_node (a : α) (cs : List (LTree α)) (v : α) :
    childrenOf (LTree.node a cs) v =
      if a = v then cs.map rootLabel else childrenOfForest cs v := by
  simp [childrenOf]

@[simp] theorem childrenOfForest_nil (v : α) :
    childrenOfForest ([] : List (LTree α)) v = [] := by
  simp [childrenOfForest]

@[simp] theorem childrenOfForest_cons (u : LTree α) (us : List (LTree α))
    (v : α) :
    childrenOfForest (u :: us) v =
      if v ∈ labels u then childrenOf u v else childrenOfForest us v := by
  simp [childrenOfForest]

/-- En un bosque de etiquetas disjuntas, la búsqueda encuentra el subárbol
que contiene `v`. -/
theorem childrenOfForest_eq_of_mem {us : List (LTree α)} {u : LTree α}
    {v : α} (hu : u ∈ us) (hv : v ∈ labels u)
    (hdisj : us.Pairwise (fun a b => (labels a).Disjoint (labels b))) :
    childrenOfForest us v = childrenOf u v := by
  induction us with
  | nil => cases hu
  | cons w ws ih =>
    rcases List.mem_cons.mp hu with rfl | hu'
    · rw [childrenOfForest_cons, if_pos hv]
    · have hvw : v ∉ labels w := fun hvw =>
        (List.pairwise_cons.mp hdisj).1 u hu' hvw hv
      rw [childrenOfForest_cons, if_neg hvw]
      exact ih hu' hdisj.of_cons

end ChildrenOf

/-- Los subárboles de hijos distintos tienen etiquetas disjuntas. -/
theorem pairwise_disjoint_labels_orderedBFSTree
    (T : Finset (Sym2 (Fin (n + 1))))
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    (L : ∀ _ : Fin (n + 1), List (Fin (n + 1)))
    (hL : ∀ v, (L v).toFinset = rootedChildren T v)
    (hLnd : ∀ v, (L v).Nodup) (v : Fin (n + 1)) :
    (((L v).attach).map (fun c => orderedBFSTree T hconn L hL c.val)).Pairwise
      (fun a b => (labels a).Disjoint (labels b)) := by
  rw [List.pairwise_map]
  refine List.Pairwise.imp ?_ (List.nodup_attach.mpr (hLnd v))
  intro a b hab
  have hcfa : a.val ∈ rootedChildren T v := by
    rw [← hL v]
    exact List.mem_toFinset.mpr a.property
  have hcfb : b.val ∈ rootedChildren T v := by
    rw [← hL v]
    exact List.mem_toFinset.mpr b.property
  intro x hxa hxb
  obtain ⟨k₁, hk₁, hl₁⟩ :=
    (mem_labels_orderedBFSTree T hconn L hL a.val x).mp hxa
  obtain ⟨k₂, hk₂, hl₂⟩ :=
    (mem_labels_orderedBFSTree T hconn L hL b.val x).mp hxb
  have ha := bfsLevel_of_mem_rootedChildren hconn hcfa
  have hb := bfsLevel_of_mem_rootedChildren hconn hcfb
  have hk : k₁ = k₂ := by omega
  exact hab (Subtype.ext (by rw [← hk₁, ← hk₂, hk]))

/-- **Extracción**: los listados se recuperan del árbol plano leyendo los
hijos del nodo etiquetado `v`. -/
theorem childrenOf_orderedBFSTree
    (T : Finset (Sym2 (Fin (n + 1))))
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    (L : ∀ _ : Fin (n + 1), List (Fin (n + 1)))
    (hL : ∀ v, (L v).toFinset = rootedChildren T v)
    (hLnd : ∀ v, (L v).Nodup)
    (v₀ v : Fin (n + 1))
    (hv : v ∈ (orderedBFSTree T hconn L hL v₀).labels) :
    childrenOf (orderedBFSTree T hconn L hL v₀) v = L v := by
  rw [orderedBFSTree] at hv ⊢
  rw [childrenOf_node]
  by_cases h0 : v₀ = v
  · subst h0
    rw [if_pos rfl, List.map_map]
    have hcomp : (rootLabel ∘ fun w : {x // x ∈ L v₀} =>
        orderedBFSTree T hconn L hL w.val) = Subtype.val := by
      funext c
      exact rootLabel_orderedBFSTree T hconn L hL c.val
    rw [hcomp, List.attach_map_subtype_val]
  · rw [if_neg h0]
    rw [labels_node, List.mem_cons, labelsForest_eq_flatten] at hv
    rcases hv with rfl | hv
    · exact absurd rfl h0
    rw [List.mem_flatten] at hv
    obtain ⟨l, hl, hvl⟩ := hv
    rw [List.mem_map] at hl
    obtain ⟨u, hu, rfl⟩ := hl
    rw [List.mem_map] at hu
    obtain ⟨c, hc, rfl⟩ := hu
    have hcf : c.val ∈ rootedChildren T v₀ := by
      rw [← hL v₀]
      exact List.mem_toFinset.mpr c.property
    have hmem : orderedBFSTree T hconn L hL c.val ∈
        (L v₀).attach.map (fun w => orderedBFSTree T hconn L hL w.val) := by
      rw [List.mem_map]
      exact ⟨c, hc, rfl⟩
    have heq := childrenOfForest_eq_of_mem hmem hvl
      (pairwise_disjoint_labels_orderedBFSTree T hconn L hL hLnd v₀)
    rw [heq]
    exact childrenOf_orderedBFSTree T hconn L hL hLnd c.val v hvl
termination_by n + 1 - bfsLevel T v₀
decreasing_by
  all_goals
    have h1 := bfsLevel_of_mem_rootedChildren hconn hcf
    have h2 := bfsLevel_le_of_connected hconn v₀
    omega

/-- Con los listados en mano, el padre BFS queda determinado. -/
theorem bfsParent_eq_of_mem_listing
    {T : Finset (Sym2 (Fin (n + 1)))}
    {L : ∀ _ : Fin (n + 1), List (Fin (n + 1))}
    (hL : ∀ v, (L v).toFinset = rootedChildren T v)
    {v w : Fin (n + 1)} (hw : w ∈ L v) : bfsParent T w = v :=
  rootedChild_parent_eq ((hL v) ▸ List.mem_toFinset.mpr hw)

/-- Los listados determinan el árbol: dos árboles generadores con los mismos
listados coinciden (vía la recuperación `penroseTree T = T`). -/
theorem spanningTree_eq_of_listings_eq
    {T₁ T₂ : Finset (Sym2 (Fin (n + 1)))}
    (hT₁ : T₁ ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))))
    (hT₂ : T₂ ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))))
    {L : ∀ _ : Fin (n + 1), List (Fin (n + 1))}
    (hL₁ : ∀ v, (L v).toFinset = rootedChildren T₁ v)
    (hL₂ : ∀ v, (L v).toFinset = rootedChildren T₂ v) :
    T₁ = T₂ := by
  have hpar : ∀ w : Fin (n + 1), w ≠ 0 →
      bfsParent T₁ w = bfsParent T₂ w := by
    intro w hw
    have h1 : w ∈ L (bfsParent T₁ w) := by
      rw [← List.mem_toFinset, hL₁]
      exact mem_rootedChildren_parent T₁ hw
    exact (bfsParent_eq_of_mem_listing hL₂ h1).symm
  rw [← penroseTree_eq_of_mem_spanningTrees hT₁,
    ← penroseTree_eq_of_mem_spanningTrees hT₂]
  unfold penroseTree
  apply Finset.image_congr
  intro v hv
  rw [Finset.mem_coe, Finset.mem_filter] at hv
  show s(bfsParent T₁ v, v) = s(bfsParent T₂ v, v)
  rw [hpar v hv.2]

/-- **Piedra (E) de (b2): inyectividad.**  El par (árbol generador, listados
de hijos) queda determinado por el árbol plano etiquetado inducido. -/
theorem orderedBFSTree_injective
    {T₁ T₂ : Finset (Sym2 (Fin (n + 1)))}
    (hT₁ : T₁ ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))))
    (hT₂ : T₂ ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))))
    (hconn₁ : (fromEdgeSet (↑T₁ : Set (Sym2 (Fin (n + 1))))).Connected)
    (hconn₂ : (fromEdgeSet (↑T₂ : Set (Sym2 (Fin (n + 1))))).Connected)
    {L₁ L₂ : ∀ _ : Fin (n + 1), List (Fin (n + 1))}
    (hL₁ : ∀ v, (L₁ v).toFinset = rootedChildren T₁ v)
    (hL₂ : ∀ v, (L₂ v).toFinset = rootedChildren T₂ v)
    (hLnd₁ : ∀ v, (L₁ v).Nodup) (hLnd₂ : ∀ v, (L₂ v).Nodup)
    (heq : orderedBFSTree T₁ hconn₁ L₁ hL₁ 0
      = orderedBFSTree T₂ hconn₂ L₂ hL₂ 0) :
    T₁ = T₂ ∧ L₁ = L₂ := by
  have hLeq : L₁ = L₂ := by
    funext v
    have h1 := childrenOf_orderedBFSTree T₁ hconn₁ L₁ hL₁ hLnd₁ 0 v
      (mem_labels_orderedBFSTree_root T₁ hconn₁ L₁ hL₁ v)
    have h2 := childrenOf_orderedBFSTree T₂ hconn₂ L₂ hL₂ hLnd₂ 0 v
      (mem_labels_orderedBFSTree_root T₂ hconn₂ L₂ hL₂ v)
    rw [← h1, ← h2, heq]
  refine ⟨?_, hLeq⟩
  exact spanningTree_eq_of_listings_eq hT₁ hT₂ hL₁ (by rw [hLeq]; exact hL₂)

/-! ### Piedra (F-i): reconstrucción — `orderedBFSTree` reconstruye el árbol -/

/-- **Reconstrucción**: si los listados coinciden con `childrenOf u` sobre las
etiquetas de `u` (sin repetición), entonces `orderedBFSTree` enraizado en la
raíz de `u` devuelve exactamente `u`.  Es el corazón de la sobreyectividad. -/
theorem orderedBFSTree_eq_of_agree
    (T : Finset (Sym2 (Fin (n + 1))))
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).Connected)
    (L : ∀ _ : Fin (n + 1), List (Fin (n + 1)))
    (hL : ∀ v, (L v).toFinset = rootedChildren T v)
    (u : LTree (Fin (n + 1)))
    (hnd : u.labels.Nodup)
    (hagree : ∀ x ∈ u.labels, L x = childrenOf u x) :
    orderedBFSTree T hconn L hL u.rootLabel = u := by
  match u, hnd, hagree with
  | LTree.node v cs, hnd, hagree =>
    rw [show (LTree.node v cs).rootLabel = v from rfl, orderedBFSTree]
    rw [labels_node, List.nodup_cons, labelsForest_eq_flatten,
      List.nodup_flatten] at hnd
    have hLv : L v = cs.map rootLabel := by
      rw [hagree v (by rw [labels_node]; exact List.mem_cons_self ..),
        childrenOf_node, if_pos rfl]
    congr 1
    rw [hLv, List.attach_map_val, List.map_map]
    have hdisj : cs.Pairwise (fun a b => (labels a).Disjoint (labels b)) :=
      List.pairwise_map.mp hnd.2.2
    have hstep : ∀ c ∈ cs,
        (orderedBFSTree T hconn L hL ∘ rootLabel) c = id c := by
      intro c hc
      have hndc : c.labels.Nodup :=
        hnd.2.1 (labels c) (List.mem_map_of_mem hc)
      have hagreec : ∀ x ∈ c.labels, L x = childrenOf c x := by
        intro x hx
        have hxu : x ∈ (LTree.node v cs).labels := by
          rw [labels_node, labelsForest_eq_flatten]
          exact List.mem_cons_of_mem _ (List.mem_flatten.mpr
            ⟨labels c, List.mem_map_of_mem hc, hx⟩)
        have hxv : ¬ v = x := by
          rintro rfl
          exact hnd.1 (List.mem_flatten.mpr
            ⟨labels c, List.mem_map_of_mem hc, hx⟩)
        rw [hagree x hxu, childrenOf_node, if_neg hxv,
          childrenOfForest_eq_of_mem hc hx hdisj]
      show orderedBFSTree T hconn L hL c.rootLabel = c
      exact orderedBFSTree_eq_of_agree T hconn L hL c hndc hagreec
    rw [List.map_congr_left hstep, List.map_id]
termination_by sizeOf u
decreasing_by
  have h := List.sizeOf_lt_of_mem hc
  simp only [LTree.node.sizeOf_spec]
  omega

/-! ### Piedra (F-ii): el kit estructural de `childrenOf` -/

section ChildrenOfKit

variable {α : Type*} [DecidableEq α]

theorem rootLabel_mem_labels (u : LTree α) : u.rootLabel ∈ u.labels := by
  match u with
  | LTree.node a cs =>
    rw [show (LTree.node a cs).rootLabel = a from rfl, labels_node]
    exact List.mem_cons_self ..

/-- Extracción del bosque: la búsqueda encuentra algún subárbol. -/
theorem exists_of_mem_childrenOfForest {us : List (LTree α)} {v w : α}
    (hw : w ∈ childrenOfForest us v) : ∃ c ∈ us, w ∈ childrenOf c v := by
  induction us with
  | nil => simp at hw
  | cons u us ih =>
    rw [childrenOfForest_cons] at hw
    by_cases hm : v ∈ labels u
    · rw [if_pos hm] at hw
      exact ⟨u, List.mem_cons_self .., hw⟩
    · rw [if_neg hm] at hw
      obtain ⟨c, hc, hwc⟩ := ih hw
      exact ⟨c, List.mem_cons_of_mem _ hc, hwc⟩

/-- Si ningún subárbol contiene `v`, la búsqueda devuelve `[]`. -/
theorem childrenOfForest_eq_nil {us : List (LTree α)} {v : α}
    (h : ∀ c ∈ us, v ∉ labels c) : childrenOfForest us v = [] := by
  induction us with
  | nil => simp
  | cons u us ih =>
    rw [childrenOfForest_cons, if_neg (h u (List.mem_cons_self ..))]
    exact ih fun c hc => h c (List.mem_cons_of_mem _ hc)

/-- **(K1)** Los hijos y su padre son etiquetas del árbol. -/
theorem mem_labels_of_mem_childrenOf {u : LTree α} {v w : α}
    (hw : w ∈ childrenOf u v) : w ∈ u.labels ∧ v ∈ u.labels := by
  match u with
  | LTree.node a cs =>
    rw [childrenOf_node] at hw
    rw [labels_node, labelsForest_eq_flatten]
    by_cases h : a = v
    · rw [if_pos h] at hw
      rw [List.mem_map] at hw
      obtain ⟨c, hc, rfl⟩ := hw
      refine ⟨List.mem_cons_of_mem _ (List.mem_flatten.mpr
        ⟨labels c, List.mem_map_of_mem hc, rootLabel_mem_labels c⟩), ?_⟩
      rw [← h]
      exact List.mem_cons_self ..
    · rw [if_neg h] at hw
      obtain ⟨c, hc, hwc⟩ := exists_of_mem_childrenOfForest hw
      obtain ⟨h1, h2⟩ := mem_labels_of_mem_childrenOf hwc
      refine ⟨?_, ?_⟩
      · exact List.mem_cons_of_mem _ (List.mem_flatten.mpr
          ⟨labels c, List.mem_map_of_mem hc, h1⟩)
      · exact List.mem_cons_of_mem _ (List.mem_flatten.mpr
          ⟨labels c, List.mem_map_of_mem hc, h2⟩)
termination_by sizeOf u
decreasing_by
  have := List.sizeOf_lt_of_mem hc
  simp only [LTree.node.sizeOf_spec]
  omega

/-- **(K2)** La raíz nunca es hija (con etiquetas sin repetición). -/
theorem rootLabel_not_mem_childrenOf {u : LTree α} (hnd : u.labels.Nodup)
    {v : α} : u.rootLabel ∉ childrenOf u v := by
  match u with
  | LTree.node a cs =>
    rw [show (LTree.node a cs).rootLabel = a from rfl]
    rw [labels_node, List.nodup_cons, labelsForest_eq_flatten] at hnd
    intro hw
    rw [childrenOf_node] at hw
    by_cases h : a = v
    · rw [if_pos h, List.mem_map] at hw
      obtain ⟨c, hc, hroot⟩ := hw
      exact hnd.1 (List.mem_flatten.mpr ⟨labels c, List.mem_map_of_mem hc,
        hroot ▸ rootLabel_mem_labels c⟩)
    · rw [if_neg h] at hw
      obtain ⟨c, hc, hwc⟩ := exists_of_mem_childrenOfForest hw
      exact hnd.1 (List.mem_flatten.mpr ⟨labels c, List.mem_map_of_mem hc,
        (mem_labels_of_mem_childrenOf hwc).1⟩)

/-- **(K-desc)** `childrenOf` desciende a subárboles: sobre las etiquetas de un
hijo, coincide con el `childrenOf` del hijo. -/
theorem childrenOf_eq_of_mem_labels {a : α} {cs : List (LTree α)}
    (hnd : (LTree.node a cs).labels.Nodup) {c : LTree α} (hc : c ∈ cs)
    {x : α} (hx : x ∈ labels c) :
    childrenOf (LTree.node a cs) x = childrenOf c x := by
  rw [labels_node, List.nodup_cons, labelsForest_eq_flatten,
    List.nodup_flatten] at hnd
  have hax : ¬ a = x := by
    rintro rfl
    exact hnd.1 (List.mem_flatten.mpr ⟨labels c, List.mem_map_of_mem hc, hx⟩)
  rw [childrenOf_node, if_neg hax,
    childrenOfForest_eq_of_mem hc hx (List.pairwise_map.mp hnd.2.2)]

/-- Miembros distintos de un bosque de etiquetas disjuntas por pares tienen
etiquetas disjuntas. -/
theorem disjoint_labels_of_ne_of_pairwise {cs : List (LTree α)}
    (hdisj : cs.Pairwise (fun a b => (labels a).Disjoint (labels b)))
    {c c' : LTree α} (hc : c ∈ cs) (hc' : c' ∈ cs) (hne : c ≠ c') :
    (labels c).Disjoint (labels c') := by
  induction cs with
  | nil => cases hc
  | cons d ds ih =>
    rw [List.pairwise_cons] at hdisj
    rcases List.mem_cons.mp hc with rfl | hc2
    · rcases List.mem_cons.mp hc' with rfl | hc2'
      · exact absurd rfl hne
      · exact hdisj.1 c' hc2'
    · rcases List.mem_cons.mp hc' with rfl | hc2'
      · exact fun x hx1 hx2 => hdisj.1 c hc2 hx2 hx1
      · exact ih hdisj.2 hc2 hc2'

/-- **(K4)** El padre estructural es único. -/
theorem childrenOf_parent_unique {u : LTree α} (hnd : u.labels.Nodup)
    {v₁ v₂ w : α} (h₁ : w ∈ childrenOf u v₁) (h₂ : w ∈ childrenOf u v₂) :
    v₁ = v₂ := by
  match u with
  | LTree.node a cs =>
    rw [labels_node, List.nodup_cons, labelsForest_eq_flatten,
      List.nodup_flatten] at hnd
    have hdisj := List.pairwise_map.mp hnd.2.2
    by_cases ha₁ : a = v₁
    · by_cases ha₂ : a = v₂
      · rw [← ha₁, ← ha₂]
      · exfalso
        rw [childrenOf_node, if_pos ha₁, List.mem_map] at h₁
        obtain ⟨c, hc, hroot⟩ := h₁
        rw [childrenOf_node, if_neg ha₂] at h₂
        obtain ⟨c', hc', hwc'⟩ := exists_of_mem_childrenOfForest h₂
        have hw1 : w ∈ labels c := hroot ▸ rootLabel_mem_labels c
        have hw2 : w ∈ labels c' := (mem_labels_of_mem_childrenOf hwc').1
        have hcc : c = c' := by
          by_contra hne
          exact disjoint_labels_of_ne_of_pairwise hdisj hc hc' hne hw1 hw2
        subst hcc
        exact rootLabel_not_mem_childrenOf
          (hnd.2.1 (labels c) (List.mem_map_of_mem hc)) (hroot.symm ▸ hwc')
    · by_cases ha₂ : a = v₂
      · exfalso
        rw [childrenOf_node, if_pos ha₂, List.mem_map] at h₂
        obtain ⟨c, hc, hroot⟩ := h₂
        rw [childrenOf_node, if_neg ha₁] at h₁
        obtain ⟨c', hc', hwc'⟩ := exists_of_mem_childrenOfForest h₁
        have hw1 : w ∈ labels c := hroot ▸ rootLabel_mem_labels c
        have hw2 : w ∈ labels c' := (mem_labels_of_mem_childrenOf hwc').1
        have hcc : c = c' := by
          by_contra hne
          exact disjoint_labels_of_ne_of_pairwise hdisj hc hc' hne hw1 hw2
        subst hcc
        exact rootLabel_not_mem_childrenOf
          (hnd.2.1 (labels c) (List.mem_map_of_mem hc)) (hroot.symm ▸ hwc')
      · rw [childrenOf_node, if_neg ha₁] at h₁
        rw [childrenOf_node, if_neg ha₂] at h₂
        obtain ⟨c₁, hc₁, hwc₁⟩ := exists_of_mem_childrenOfForest h₁
        obtain ⟨c₂, hc₂, hwc₂⟩ := exists_of_mem_childrenOfForest h₂
        have hw1 : w ∈ labels c₁ := (mem_labels_of_mem_childrenOf hwc₁).1
        have hw2 : w ∈ labels c₂ := (mem_labels_of_mem_childrenOf hwc₂).1
        have hcc : c₁ = c₂ := by
          by_contra hne
          exact disjoint_labels_of_ne_of_pairwise hdisj hc₁ hc₂ hne hw1 hw2
        subst hcc
        exact childrenOf_parent_unique
          (hnd.2.1 (labels c₁) (List.mem_map_of_mem hc₁)) hwc₁ hwc₂
termination_by sizeOf u
decreasing_by
  have := List.sizeOf_lt_of_mem hc₁
  simp only [LTree.node.sizeOf_spec]
  omega

/-- **(K-antisim)** La relación padre-hijo estructural es antisimétrica. -/
theorem not_mem_childrenOf_of_mem_childrenOf {u : LTree α}
    (hnd : u.labels.Nodup) {v w : α} (hw : w ∈ childrenOf u v) :
    v ∉ childrenOf u w := by
  match u with
  | LTree.node a cs =>
    intro hv
    rw [labels_node, List.nodup_cons, labelsForest_eq_flatten,
      List.nodup_flatten] at hnd
    have hdisj := List.pairwise_map.mp hnd.2.2
    by_cases hav : a = v
    · rw [childrenOf_node, if_pos hav, List.mem_map] at hw
      obtain ⟨c, hc, hroot⟩ := hw
      have haw : ¬ a = w := by
        rintro rfl
        exact hnd.1 (List.mem_flatten.mpr ⟨labels c, List.mem_map_of_mem hc,
          hroot ▸ rootLabel_mem_labels c⟩)
      rw [childrenOf_node, if_neg haw] at hv
      obtain ⟨c', hc', hvc'⟩ := exists_of_mem_childrenOfForest hv
      have hvl : v ∈ labels c' := (mem_labels_of_mem_childrenOf hvc').1
      exact hnd.1 (List.mem_flatten.mpr ⟨labels c', List.mem_map_of_mem hc',
        hav.symm ▸ hvl⟩)
    · rw [childrenOf_node, if_neg hav] at hw
      obtain ⟨c, hc, hwc⟩ := exists_of_mem_childrenOfForest hw
      obtain ⟨hwl, hvl⟩ := mem_labels_of_mem_childrenOf hwc
      have haw : ¬ a = w := by
        rintro rfl
        exact hnd.1 (List.mem_flatten.mpr ⟨labels c, List.mem_map_of_mem hc,
          hwl⟩)
      rw [childrenOf_node, if_neg haw] at hv
      obtain ⟨c', hc', hvc'⟩ := exists_of_mem_childrenOfForest hv
      have hvl' : v ∈ labels c' := (mem_labels_of_mem_childrenOf hvc').1
      have hcc : c = c' := by
        by_contra hne
        exact disjoint_labels_of_ne_of_pairwise hdisj hc hc' hne hvl hvl'
      subst hcc
      exact not_mem_childrenOf_of_mem_childrenOf
        (hnd.2.1 (labels c) (List.mem_map_of_mem hc)) hwc hvc'
termination_by sizeOf u
decreasing_by
  have := List.sizeOf_lt_of_mem hc
  simp only [LTree.node.sizeOf_spec]
  omega

/-- **(K3)** Toda etiqueta no-raíz tiene padre estructural. -/
theorem exists_parent_of_mem_labels {u : LTree α} (hnd : u.labels.Nodup)
    {w : α} (hw : w ∈ u.labels) (hroot : w ≠ u.rootLabel) :
    ∃ v, w ∈ childrenOf u v := by
  match u with
  | LTree.node a cs =>
    rw [show (LTree.node a cs).rootLabel = a from rfl] at hroot
    rw [labels_node, List.mem_cons, labelsForest_eq_flatten] at hw
    rcases hw with rfl | hw
    · exact absurd rfl hroot
    rw [List.mem_flatten] at hw
    obtain ⟨l, hl, hwl⟩ := hw
    rw [List.mem_map] at hl
    obtain ⟨c, hc, rfl⟩ := hl
    by_cases hwc : w = c.rootLabel
    · refine ⟨a, ?_⟩
      rw [childrenOf_node, if_pos rfl, List.mem_map]
      exact ⟨c, hc, hwc.symm⟩
    · have hndc : c.labels.Nodup := by
        rw [labels_node, List.nodup_cons, labelsForest_eq_flatten,
          List.nodup_flatten] at hnd
        exact hnd.2.1 (labels c) (List.mem_map_of_mem hc)
      obtain ⟨v, hv⟩ := exists_parent_of_mem_labels hndc hwl hwc
      have hvc : v ∈ labels c := (mem_labels_of_mem_childrenOf hv).2
      refine ⟨v, ?_⟩
      rw [childrenOf_eq_of_mem_labels hnd hc hvc]
      exact hv
termination_by sizeOf u
decreasing_by
  have := List.sizeOf_lt_of_mem hc
  simp only [LTree.node.sizeOf_spec]
  omega

/-- **(K7)** Los listados de hijos no repiten (etiquetas sin repetición). -/
theorem nodup_childrenOf {u : LTree α} (hnd : u.labels.Nodup) (v : α) :
    (childrenOf u v).Nodup := by
  match u with
  | LTree.node a cs =>
    rw [labels_node, List.nodup_cons, labelsForest_eq_flatten,
      List.nodup_flatten] at hnd
    have hdisj := List.pairwise_map.mp hnd.2.2
    rw [childrenOf_node]
    by_cases h : a = v
    · rw [if_pos h]
      have h2 : cs.Pairwise (fun c c' => rootLabel c ≠ rootLabel c') := by
        refine hdisj.imp ?_
        intro c c' hcc' heq
        exact hcc' (rootLabel_mem_labels c) (heq.symm ▸ rootLabel_mem_labels c')
      exact List.pairwise_map.mpr h2
    · rw [if_neg h]
      by_cases hex : ∃ c ∈ cs, v ∈ labels c
      · obtain ⟨c, hc, hvc⟩ := hex
        rw [childrenOfForest_eq_of_mem hc hvc hdisj]
        exact nodup_childrenOf (hnd.2.1 (labels c) (List.mem_map_of_mem hc)) v
      · push_neg at hex
        rw [childrenOfForest_eq_nil hex]
        exact List.nodup_nil
termination_by sizeOf u
decreasing_by
  have := List.sizeOf_lt_of_mem hc
  simp only [LTree.node.sizeOf_spec]
  omega

/-- Un hijo nunca coincide con su padre. -/
theorem ne_of_mem_childrenOf {u : LTree α} (hnd : u.labels.Nodup)
    {v w : α} (hw : w ∈ childrenOf u v) : v ≠ w := by
  rintro rfl
  exact not_mem_childrenOf_of_mem_childrenOf hnd hw hw

end ChildrenOfKit

/-- **(K-alcance)** Toda etiqueta alcanza la raíz siguiendo aristas
padre-hijo. -/
theorem reachable_rootLabel_of_mem_labels
    {E : Finset (Sym2 (Fin (n + 1)))} {u : LTree (Fin (n + 1))}
    (hnd : u.labels.Nodup)
    (hE : ∀ v w : Fin (n + 1), w ∈ childrenOf u v → s(v, w) ∈ E)
    {x : Fin (n + 1)} (hx : x ∈ u.labels) :
    (fromEdgeSet (↑E : Set (Sym2 (Fin (n + 1))))).Reachable x u.rootLabel := by
  match u with
  | LTree.node a cs =>
    rw [show (LTree.node a cs).rootLabel = a from rfl]
    rw [labels_node, List.mem_cons, labelsForest_eq_flatten] at hx
    rcases hx with rfl | hx
    · exact SimpleGraph.Reachable.refl _
    · rw [List.mem_flatten] at hx
      obtain ⟨l, hl, hxl⟩ := hx
      rw [List.mem_map] at hl
      obtain ⟨c, hc, rfl⟩ := hl
      have hnd0 := hnd
      rw [labels_node, List.nodup_cons, labelsForest_eq_flatten,
        List.nodup_flatten] at hnd
      have hndc : c.labels.Nodup :=
        hnd.2.1 (labels c) (List.mem_map_of_mem hc)
      have hEc : ∀ v w : Fin (n + 1), w ∈ childrenOf c v → s(v, w) ∈ E := by
        intro v w hw
        have hvc : v ∈ labels c := (mem_labels_of_mem_childrenOf hw).2
        refine hE v w ?_
        rw [childrenOf_eq_of_mem_labels hnd0 hc hvc]
        exact hw
      have hreach := reachable_rootLabel_of_mem_labels hndc hEc hxl
      have hedge : s(a, c.rootLabel) ∈ E := by
        refine hE a c.rootLabel ?_
        rw [childrenOf_node, if_pos rfl, List.mem_map]
        exact ⟨c, hc, rfl⟩
      have hne : a ≠ c.rootLabel := by
        intro heq
        exact hnd.1 (List.mem_flatten.mpr ⟨labels c, List.mem_map_of_mem hc,
          heq.symm ▸ rootLabel_mem_labels c⟩)
      have hadj : (fromEdgeSet (↑E : Set (Sym2 (Fin (n + 1))))).Adj a
          c.rootLabel := by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨Finset.mem_coe.mpr hedge, hne⟩
      exact hreach.trans hadj.reachable.symm
termination_by sizeOf u
decreasing_by
  have := List.sizeOf_lt_of_mem hc
  simp only [LTree.node.sizeOf_spec]
  omega

/-! ### El árbol de aristas estructurales: S1 y S2 -/

/-- Las aristas padre-hijo estructurales de un árbol plano etiquetado. -/
noncomputable def treeEdges (u : LTree (Fin (n + 1))) :
    Finset (Sym2 (Fin (n + 1))) :=
  Finset.univ.biUnion
    (fun v => ((childrenOf u v).toFinset).image (fun w => s(v, w)))

theorem mem_treeEdges {u : LTree (Fin (n + 1))} {e : Sym2 (Fin (n + 1))} :
    e ∈ treeEdges u ↔ ∃ v w, w ∈ childrenOf u v ∧ s(v, w) = e := by
  simp only [treeEdges, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, List.mem_toFinset]

/-- Adyacencia en el grafo construido: exactamente la relación padre-hijo. -/
theorem adj_fromEdgeSet_treeEdges {u : LTree (Fin (n + 1))}
    (hnd : u.labels.Nodup) {x y : Fin (n + 1)} :
    (fromEdgeSet (↑(treeEdges u) : Set (Sym2 (Fin (n + 1))))).Adj x y ↔
      (y ∈ childrenOf u x ∨ x ∈ childrenOf u y) := by
  rw [SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨hmem, hne⟩
    rw [Finset.mem_coe, mem_treeEdges] at hmem
    obtain ⟨v, w, hw, heq⟩ := hmem
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hw
    · exact Or.inr hw
  · intro h
    rcases h with h | h
    · exact ⟨Finset.mem_coe.mpr (mem_treeEdges.mpr ⟨x, y, h, rfl⟩),
        ne_of_mem_childrenOf hnd h⟩
    · refine ⟨Finset.mem_coe.mpr (mem_treeEdges.mpr ⟨y, x, h, ?_⟩),
        (ne_of_mem_childrenOf hnd h).symm⟩
      exact Sym2.eq_swap

/-- El número de aristas estructurales es el número de etiquetas no-raíz. -/
theorem card_treeEdges {u : LTree (Fin (n + 1))} (hnd : u.labels.Nodup) :
    (treeEdges u).card =
      (u.labels.toFinset.filter (fun w => w ≠ u.rootLabel)).card := by
  have hedgefib : ∀ v₁ ∈ (Finset.univ : Finset (Fin (n + 1))),
      ∀ v₂ ∈ (Finset.univ : Finset (Fin (n + 1))), v₁ ≠ v₂ →
      Disjoint (((childrenOf u v₁).toFinset).image (fun w => s(v₁, w)))
        (((childrenOf u v₂).toFinset).image (fun w => s(v₂, w))) := by
    intro v₁ _ v₂ _ hne
    rw [Finset.disjoint_left]
    intro e he1 he2
    rw [Finset.mem_image] at he1 he2
    obtain ⟨w₁, hw₁, rfl⟩ := he1
    obtain ⟨w₂, hw₂, heq⟩ := he2
    rw [List.mem_toFinset] at hw₁ hw₂
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hne h1.symm
    · rw [h2] at hw₂
      rw [← h1] at hw₁
      exact not_mem_childrenOf_of_mem_childrenOf hnd hw₁ hw₂
  have hchildfib : ∀ v₁ ∈ (Finset.univ : Finset (Fin (n + 1))),
      ∀ v₂ ∈ (Finset.univ : Finset (Fin (n + 1))), v₁ ≠ v₂ →
      Disjoint ((childrenOf u v₁).toFinset) ((childrenOf u v₂).toFinset) := by
    intro v₁ _ v₂ _ hne
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rw [List.mem_toFinset] at hw1 hw2
    exact hne (childrenOf_parent_unique hnd hw1 hw2)
  have himg : ∀ v ∈ (Finset.univ : Finset (Fin (n + 1))),
      (((childrenOf u v).toFinset).image (fun w => s(v, w))).card
        = ((childrenOf u v).toFinset).card := by
    intro v _
    apply Finset.card_image_of_injOn
    intro w hw w' hw' heq
    have hw2 : w' ∈ childrenOf u v :=
      List.mem_toFinset.mp (Finset.mem_coe.mp hw')
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact absurd h1 (ne_of_mem_childrenOf hnd hw2)
  have hbiu : Finset.univ.biUnion (fun v => (childrenOf u v).toFinset)
      = u.labels.toFinset.filter (fun w => w ≠ u.rootLabel) := by
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      List.mem_toFinset, Finset.mem_filter]
    constructor
    · rintro ⟨v, hw⟩
      refine ⟨(mem_labels_of_mem_childrenOf hw).1, ?_⟩
      intro h
      exact rootLabel_not_mem_childrenOf hnd (h ▸ hw)
    · rintro ⟨hwl, hwr⟩
      exact exists_parent_of_mem_labels hnd hwl hwr
  rw [treeEdges, Finset.card_biUnion hedgefib, Finset.sum_congr rfl himg,
    ← Finset.card_biUnion hchildfib, hbiu]

/-- El grafo construido es conexo. -/
theorem treeEdges_connected {u : LTree (Fin (n + 1))} (hnd : u.labels.Nodup)
    (hall : ∀ x : Fin (n + 1), x ∈ u.labels) :
    (fromEdgeSet (↑(treeEdges u) : Set (Sym2 (Fin (n + 1))))).Connected := by
  have hE : ∀ v w : Fin (n + 1), w ∈ childrenOf u v → s(v, w) ∈ treeEdges u :=
    fun v w h => mem_treeEdges.mpr ⟨v, w, h, rfl⟩
  refine ⟨fun x y => ?_⟩
  exact (reachable_rootLabel_of_mem_labels hnd hE (hall x)).trans
    (reachable_rootLabel_of_mem_labels hnd hE (hall y)).symm

/-- El grafo construido es un árbol. -/
theorem treeEdges_isTree {u : LTree (Fin (n + 1))} (hnd : u.labels.Nodup)
    (hall : ∀ x : Fin (n + 1), x ∈ u.labels) :
    (fromEdgeSet (↑(treeEdges u) : Set (Sym2 (Fin (n + 1))))).IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨treeEdges_connected hnd hall, ?_⟩
  have hset : (fromEdgeSet (↑(treeEdges u) : Set (Sym2 (Fin (n + 1))))).edgeSet
      = (↑(treeEdges u) : Set (Sym2 (Fin (n + 1)))) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff, Finset.mem_coe]
    refine ⟨fun h => h.1, fun he => ⟨he, ?_⟩⟩
    intro hdiag
    obtain ⟨v, w, hw, heq⟩ := mem_treeEdges.mp he
    rw [← heq] at hdiag
    exact ne_of_mem_childrenOf hnd hw (Sym2.mk_isDiag_iff.mp hdiag)
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Nat.card_eq_fintype_card, Fintype.card_fin, card_treeEdges hnd]
  have htofin : u.labels.toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun x => List.mem_toFinset.mpr (hall x)
  rw [htofin, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- **(S1)** El árbol de aristas estructurales es un árbol generador del grafo
completo. -/
theorem treeEdges_mem_spanningTrees {u : LTree (Fin (n + 1))}
    (hnd : u.labels.Nodup) (hall : ∀ x : Fin (n + 1), x ∈ u.labels) :
    treeEdges u ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))) := by
  classical
  unfold spanningTrees
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun e he => ?_, treeEdges_isTree hnd hall⟩
  rw [SimpleGraph.mem_edgeFinset]
  obtain ⟨v, w, hw, heq⟩ := mem_treeEdges.mp he
  rw [← heq, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
  exact ne_of_mem_childrenOf hnd hw

/-- **La reclamación clave de S2**: el padre BFS del árbol construido es el
padre estructural, por inducción fuerte en el nivel BFS.  El caso malo (el
padre BFS resultara ser un hijo estructural) muere porque las dos ecuaciones
de nivel de `bfsParent_spec` chocan. -/
theorem mem_childrenOf_bfsParent {u : LTree (Fin (n + 1))}
    (hnd : u.labels.Nodup) (hroot : u.rootLabel = 0)
    (hconn : (fromEdgeSet
      (↑(treeEdges u) : Set (Sym2 (Fin (n + 1))))).Connected)
    (w : Fin (n + 1)) (hw : w ≠ 0) :
    w ∈ childrenOf u (bfsParent (treeEdges u) w) := by
  have hspec := bfsParent_spec hconn hw
  have hadj := hspec.1
  rw [adj_fromEdgeSet_treeEdges hnd] at hadj
  rcases hadj with h | h
  · exact h
  · exfalso
    have hb0 : bfsParent (treeEdges u) w ≠ 0 := by
      intro h0
      rw [h0] at h
      exact rootLabel_not_mem_childrenOf hnd (hroot.symm ▸ h)
    have hrec := mem_childrenOf_bfsParent hnd hroot hconn
      (bfsParent (treeEdges u) w) hb0
    have hbp : bfsParent (treeEdges u) (bfsParent (treeEdges u) w) = w :=
      childrenOf_parent_unique hnd hrec h
    have h1 := hspec.2
    have h2 := (bfsParent_spec hconn hb0).2
    rw [hbp] at h2
    omega
termination_by bfsLevel (treeEdges u) w
decreasing_by
  have h1 := hspec.2
  omega

/-- **(S2)** Las fibras BFS del árbol construido son los hijos
estructurales. -/
theorem rootedChildren_treeEdges {u : LTree (Fin (n + 1))}
    (hnd : u.labels.Nodup) (hroot : u.rootLabel = 0)
    (hconn : (fromEdgeSet
      (↑(treeEdges u) : Set (Sym2 (Fin (n + 1))))).Connected)
    (v : Fin (n + 1)) :
    rootedChildren (treeEdges u) v = (childrenOf u v).toFinset := by
  ext w
  rw [mem_rootedChildren, List.mem_toFinset]
  constructor
  · rintro ⟨hw0, hbp⟩
    have h := mem_childrenOf_bfsParent hnd hroot hconn w hw0
    rw [hbp] at h
    exact h
  · intro hw
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0] at hw
      exact rootLabel_not_mem_childrenOf hnd (hroot.symm ▸ hw)
    exact ⟨hw0, childrenOf_parent_unique hnd
      (mem_childrenOf_bfsParent hnd hroot hconn w hw0) hw⟩

/-! ### Piedra (G): la biyección y la identidad -/

/-- **La biyección de (b2)**: los pares (árbol generador, listados de hijos)
están en biyección con los árboles planos etiquetados. -/
theorem card_sigma_childListings_eq (n : ℕ) :
    ((spanningTrees (⊤ : SimpleGraph (Fin (n + 1)))).sigma
        (fun T => childListings T)).card = (labeledTreesOn n).card := by
  refine Finset.card_bij
    (fun p hp => orderedBFSTree p.1
      (isTree_of_mem_spanningTrees _ (Finset.mem_sigma.mp hp).1).isConnected
      p.2 (fun v => ((mem_childListings.mp (Finset.mem_sigma.mp hp).2) v).2) 0)
    ?_ ?_ ?_
  · intro p hp
    exact orderedBFSTree_mem_labeledTreesOn _ _ _ _
      (fun v => ((mem_childListings.mp (Finset.mem_sigma.mp hp).2) v).1)
  · intro p₁ hp₁ p₂ hp₂ heq
    rcases p₁ with ⟨T₁, L₁⟩
    rcases p₂ with ⟨T₂, L₂⟩
    rw [Finset.mem_sigma] at hp₁ hp₂
    obtain ⟨hTeq, hLeq⟩ := orderedBFSTree_injective hp₁.1 hp₂.1 _ _
      (fun v => ((mem_childListings.mp hp₁.2) v).2)
      (fun v => ((mem_childListings.mp hp₂.2) v).2)
      (fun v => ((mem_childListings.mp hp₁.2) v).1)
      (fun v => ((mem_childListings.mp hp₂.2) v).1) heq
    subst hTeq
    subst hLeq
    rfl
  · intro u hu
    obtain ⟨hperm, hroot⟩ := mem_labeledTreesOn.mp hu
    have hnd : u.labels.Nodup := hperm.nodup_iff.mpr (List.nodup_finRange _)
    have hall : ∀ x : Fin (n + 1), x ∈ u.labels :=
      fun x => hperm.mem_iff.mpr (List.mem_finRange x)
    have hT := treeEdges_mem_spanningTrees hnd hall
    have hconn := treeEdges_connected hnd hall
    have hm : (fun v => childrenOf u v) ∈ childListings (treeEdges u) := by
      rw [mem_childListings]
      intro v
      exact ⟨nodup_childrenOf hnd v,
        (rootedChildren_treeEdges hnd hroot hconn v).symm⟩
    refine ⟨⟨treeEdges u, fun v => childrenOf u v⟩,
      Finset.mem_sigma.mpr ⟨hT, hm⟩, ?_⟩
    have h := orderedBFSTree_eq_of_agree (treeEdges u)
      (isTree_of_mem_spanningTrees _ hT).isConnected
      (fun v => childrenOf u v)
      (fun v => ((mem_childListings.mp hm) v).2) u hnd (fun x _ => rfl)
    rw [hroot] at h
    exact h

/-- **(b2) COMPLETA**: la suma de pesos factoriales de conteos de hijos sobre
los árboles generadores del grafo completo es `n! * catalan n`. -/
theorem sum_prod_rootedChildCount_factorial_eq (n : ℕ) :
    (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
        ∏ v, (rootedChildCount T v)!) = n ! * catalan n := by
  rw [sum_prod_factorial_eq_card_sigma_childListings,
    card_sigma_childListings_eq, card_labeledTreesOn']

end YangMills.KP

#print axioms YangMills.KP.penroseTree_eq_of_mem_spanningTrees
#print axioms YangMills.KP.card_of_mem_spanningTrees
#print axioms YangMills.KP.bfsLevel_le_of_connected
#print axioms YangMills.KP.mem_fiberListings
#print axioms YangMills.KP.card_fiberListings
#print axioms YangMills.KP.card_childListings
#print axioms YangMills.KP.sum_prod_factorial_eq_card_sigma_childListings
#print axioms YangMills.KP.rootLabel_orderedBFSTree
#print axioms YangMills.KP.bfsLevel_parIter
#print axioms YangMills.KP.mem_labels_orderedBFSTree
#print axioms YangMills.KP.nodup_labels_orderedBFSTree
#print axioms YangMills.KP.orderedBFSTree_mem_labeledTreesOn
#print axioms YangMills.KP.childrenOf_orderedBFSTree
#print axioms YangMills.KP.spanningTree_eq_of_listings_eq
#print axioms YangMills.KP.orderedBFSTree_injective
#print axioms YangMills.KP.orderedBFSTree_eq_of_agree
#print axioms YangMills.KP.orderedBFSTree_injective
#print axioms YangMills.KP.treeEdges_mem_spanningTrees
#print axioms YangMills.KP.rootedChildren_treeEdges
#print axioms YangMills.KP.card_sigma_childListings_eq
#print axioms YangMills.KP.sum_prod_rootedChildCount_factorial_eq
