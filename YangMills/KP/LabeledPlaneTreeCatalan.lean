/-
# Labeled plane-tree rigidity count

This module proves the labeled-rigidity piece of the route toward
`YangMills.KP.RootedChildFactorialCatalanIdentity`.

It builds labeled rooted plane trees `LTree α`, forgets labels via `shape`,
reads labels in preorder via `labels`, and reconstructs a labeled tree from a
shape and a label list using `decorate`.  The round-trip theorems
`shape_decorate`, `labels_decorate`, and `decorate_shape_labels` express the
rigidity principle: a labeled plane tree is determined by its shape together
with its preorder label list.

The finite set `headZeroPerms n` contains exactly the lists over
`Fin (n + 1)` that start with `0` and enumerate every label once; its
cardinality is `n!`.  Combining this with the plane-tree Catalan count from
`PlaneTreeCatalan.lean` gives

* `card_labeledTreesOn`:
  `(labeledTreesOn n).card = catalan n * n!`;
* `card_labeledTreesOn'`:
  `(labeledTreesOn n).card = n! * catalan n`.

Checked target: Lean `leanprover/lean4:v4.29.0-rc6`, Mathlib
`07642720480157414db592fa85b626dafb71355b`.

Expected oracle for the printed theorems:
`[propext, Classical.choice, Quot.sound]`.
-/
import YangMills.KP.PlaneTreeCatalan
import Mathlib.Data.Fintype.Perm

open Nat Finset

namespace RootedTreeCatalan

universe u

/-- Árbol plano etiquetado: una etiqueta y una lista ordenada de subárboles. -/
inductive LTree (α : Type u) : Type u where
  | node : α → List (LTree α) → LTree α

namespace LTree

variable {α : Type u}

/-- Etiqueta de la raíz. -/
def rootLabel : LTree α → α
  | node a _ => a

mutual
  /-- Forma subyacente (olvida las etiquetas). -/
  def shape : LTree α → PlaneTree
    | node _ cs => .node (shapeForest cs)
  def shapeForest : List (LTree α) → List PlaneTree
    | [] => []
    | u :: us => shape u :: shapeForest us
end

mutual
  /-- Etiquetas en preorden. -/
  def labels : LTree α → List α
    | node a cs => a :: labelsForest cs
  def labelsForest : List (LTree α) → List α
    | [] => []
    | u :: us => labels u ++ labelsForest us
end

@[simp] theorem shape_node (a : α) (cs : List (LTree α)) :
    shape (node a cs) = .node (shapeForest cs) := by simp [shape]

@[simp] theorem shapeForest_nil : shapeForest ([] : List (LTree α)) = [] := by
  simp [shapeForest]

@[simp] theorem shapeForest_cons (u : LTree α) (us : List (LTree α)) :
    shapeForest (u :: us) = shape u :: shapeForest us := by simp [shapeForest]

@[simp] theorem labels_node (a : α) (cs : List (LTree α)) :
    labels (node a cs) = a :: labelsForest cs := by simp [labels]

@[simp] theorem labelsForest_nil : labelsForest ([] : List (LTree α)) = [] := by
  simp [labelsForest]

@[simp] theorem labelsForest_cons (u : LTree α) (us : List (LTree α)) :
    labelsForest (u :: us) = labels u ++ labelsForest us := by simp [labelsForest]

@[simp] theorem head?_labels (u : LTree α) :
    u.labels.head? = some u.rootLabel := by
  obtain ⟨a, cs⟩ := u
  simp [rootLabel]

/- Las etiquetas en preorden son tantas como nodos tiene la forma. -/
mutual
  theorem length_labels : ∀ u : LTree α, u.labels.length = u.shape.size
    | node a cs => by
        simp [length_labelsForest cs]
  theorem length_labelsForest : ∀ us : List (LTree α),
      (labelsForest us).length = PlaneTree.sizeForest (shapeForest us)
    | [] => by simp
    | u :: us => by
        simp [length_labels u, length_labelsForest us]
end

end LTree

open LTree

variable {α : Type u}

/- Reconstrucción por rigidez: decora una forma con una lista de etiquetas.
Total (`d` rellena si la lista es corta; el exceso se ignora); los round-trips
valen bajo las hipótesis de longitud naturales. -/
mutual
  def decorate (d : α) : PlaneTree → List α → LTree α
    | .node cs, l => .node (l.headD d) (decorateForest d cs l.tail)
  def decorateForest (d : α) : List PlaneTree → List α → List (LTree α)
    | [], _ => []
    | t :: ts, l =>
        decorate d t (l.take t.size) :: decorateForest d ts (l.drop t.size)
end

@[simp] theorem rootLabel_decorate (d : α) (t : PlaneTree) (l : List α) :
    (decorate d t l).rootLabel = l.headD d := by
  obtain ⟨cs⟩ := t
  simp [decorate, LTree.rootLabel]

/- Round-trip 1: la decoración no cambia la forma (incondicional). -/
mutual
  theorem shape_decorate (d : α) :
      ∀ (t : PlaneTree) (l : List α), (decorate d t l).shape = t
    | .node cs, l => by
        simp only [decorate, LTree.shape_node]
        rw [shapeForest_decorateForest d cs l.tail]
  theorem shapeForest_decorateForest (d : α) :
      ∀ (ts : List PlaneTree) (l : List α),
        LTree.shapeForest (decorateForest d ts l) = ts
    | [], l => by simp [decorateForest]
    | t :: ts, l => by
        simp only [decorateForest, LTree.shapeForest_cons]
        rw [shape_decorate d t (l.take t.size),
          shapeForest_decorateForest d ts (l.drop t.size)]
end

/- Round-trip 2: con la longitud correcta, las etiquetas se recuperan. -/
mutual
  theorem labels_decorate (d : α) :
      ∀ (t : PlaneTree) (l : List α), l.length = t.size →
        (decorate d t l).labels = l
    | .node cs, l, h => by
        cases l with
        | nil =>
            rw [PlaneTree.size_node] at h
            simp only [List.length_nil] at h
            omega
        | cons a l' =>
            have h' : l'.length = PlaneTree.sizeForest cs := by
              rw [PlaneTree.size_node] at h
              simp only [List.length_cons] at h
              omega
            simp only [decorate, List.headD_cons, List.tail_cons,
              LTree.labels_node, labelsForest_decorateForest d cs l' h']
  theorem labelsForest_decorateForest (d : α) :
      ∀ (ts : List PlaneTree) (l : List α), l.length = PlaneTree.sizeForest ts →
        LTree.labelsForest (decorateForest d ts l) = l
    | [], l, h => by
        simp only [PlaneTree.sizeForest_nil] at h
        cases l with
        | nil => simp [decorateForest]
        | cons a l' =>
            simp only [List.length_cons] at h
            omega
    | t :: ts, l, h => by
        rw [PlaneTree.sizeForest_cons] at h
        have h1 : (l.take t.size).length = t.size := by
          rw [List.length_take]
          omega
        have h2 : (l.drop t.size).length = PlaneTree.sizeForest ts := by
          rw [List.length_drop]
          omega
        simp only [decorateForest, LTree.labelsForest_cons,
          labels_decorate d t (l.take t.size) h1,
          labelsForest_decorateForest d ts (l.drop t.size) h2]
        exact List.take_append_drop t.size l
end

/- Round-trip 3: todo árbol etiquetado es la decoración de su forma con sus
etiquetas — la **rigidez** de los árboles planos. -/
mutual
  theorem decorate_shape_labels (d : α) :
      ∀ u : LTree α, decorate d u.shape u.labels = u
    | .node a cs => by
        simp only [LTree.shape_node, LTree.labels_node, decorate,
          List.headD_cons, List.tail_cons]
        rw [decorateForest_shapeForest_labelsForest d cs]
  theorem decorateForest_shapeForest_labelsForest (d : α) :
      ∀ us : List (LTree α),
        decorateForest d (LTree.shapeForest us) (LTree.labelsForest us) = us
    | [] => by simp [decorateForest]
    | u :: us => by
        simp only [LTree.shapeForest_cons, LTree.labelsForest_cons, decorateForest]
        have htake : (u.labels ++ LTree.labelsForest us).take u.shape.size
            = u.labels := by
          rw [← LTree.length_labels u]
          exact List.take_left
        have hdrop : (u.labels ++ LTree.labelsForest us).drop u.shape.size
            = LTree.labelsForest us := by
          rw [← LTree.length_labels u]
          exact List.drop_left
        rw [htake, hdrop, decorate_shape_labels d u,
          decorateForest_shapeForest_labelsForest d us]
end


/-- Listas sobre `Fin (n+1)` que empiezan por `0` y enumeran cada etiqueta
exactamente una vez: la imagen inyectiva de `Equiv.Perm (Fin n)`
(`σ ↦ 0 :: [σ(0).succ, …, σ(n-1).succ]`). -/
def headZeroPerms (n : ℕ) : Finset (List (Fin (n + 1))) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).map
    ⟨fun σ => (0 : Fin (n + 1)) :: List.ofFn (fun i => (σ i).succ), by
      intro σ τ h
      simp only [List.cons.injEq, true_and] at h
      exact Equiv.ext fun i =>
        Fin.succ_injective _ (congrFun (List.ofFn_inj.mp h) i)⟩

theorem card_headZeroPerms (n : ℕ) : (headZeroPerms n).card = n ! := by
  rw [headZeroPerms, Finset.card_map, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]

theorem length_of_mem_headZeroPerms {n : ℕ} {l : List (Fin (n + 1))}
    (h : l ∈ headZeroPerms n) : l.length = n + 1 := by
  simp only [headZeroPerms, Finset.mem_map, Function.Embedding.coeFn_mk,
    Finset.mem_univ, true_and] at h
  obtain ⟨σ, rfl⟩ := h
  simp

/-- Toda función inyectiva `Fin m → Fin (m+1)` que evita `0` es `succ ∘ σ`
para alguna permutación `σ`. -/
theorem exists_perm_succ_comp {m : ℕ} (F : Fin m → Fin (m + 1))
    (hinj : Function.Injective F) (h0 : ∀ i, F i ≠ 0) :
    ∃ σ : Equiv.Perm (Fin m), (fun i => (σ i).succ) = F := by
  have hpinj : Function.Injective fun i => (F i).pred (h0 i) := by
    intro i j hij
    apply hinj
    have h1 := congrArg Fin.succ hij
    rwa [Fin.succ_pred, Fin.succ_pred] at h1
  have hbij := (Fintype.bijective_iff_injective_and_card
    (fun i => (F i).pred (h0 i))).mpr ⟨hpinj, rfl⟩
  exact ⟨Equiv.ofBijective _ hbij, funext fun i => Fin.succ_pred (F i) (h0 i)⟩

/-- Reindexación de `ofFn` a lo largo de una igualdad de longitudes. -/
theorem ofFn_cast_eq {β : Type*} {m k : ℕ} (h : k = m) (f : Fin m → β) :
    List.ofFn (fun i : Fin k => f (Fin.cast h i)) = List.ofFn f := by
  subst h
  rfl

/-- Caracterización semántica: son exactamente las listas que permutan
`finRange (n+1)` y tienen cabeza `0`. -/
theorem mem_headZeroPerms {n : ℕ} {l : List (Fin (n + 1))} :
    l ∈ headZeroPerms n ↔ l.Perm (List.finRange (n + 1)) ∧ l.head? = some 0 := by
  simp only [headZeroPerms, Finset.mem_map, Function.Embedding.coeFn_mk,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨?_, rfl⟩
    apply List.perm_of_nodup_nodup_toFinset_eq
    · rw [List.nodup_cons]
      constructor
      · rw [List.mem_ofFn']
        rintro ⟨i, hi⟩
        exact Fin.succ_ne_zero (σ i) hi
      · rw [List.nodup_ofFn]
        exact fun i j hij => σ.injective (Fin.succ_injective _ hij)
    · exact List.nodup_finRange _
    · ext x
      simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
        List.mem_ofFn', Set.mem_range, List.mem_finRange, iff_true]
      rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨j, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨σ.symm j, by simp⟩
  · rintro ⟨hperm, hhead⟩
    cases l with
    | nil => simp at hhead
    | cons a l' =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      have hlen : l'.length = n := by
        have h := hperm.length_eq
        simp only [List.length_cons, List.length_finRange] at h
        omega
      have hnodup : ((0 : Fin (n + 1)) :: l').Nodup :=
        (hperm.nodup_iff).mpr (List.nodup_finRange _)
      have h0 : (0 : Fin (n + 1)) ∉ l' := (List.nodup_cons.mp hnodup).1
      have hnd' : l'.Nodup := (List.nodup_cons.mp hnodup).2
      obtain ⟨σ, hσ⟩ := exists_perm_succ_comp
        (fun i => l'.get (Fin.cast hlen.symm i))
        (fun i j hij => by
          have h1 := List.nodup_iff_injective_get.mp hnd' hij
          have h2 := congrArg Fin.val h1
          simp only [Fin.val_cast] at h2
          exact Fin.ext h2)
        (fun i hi => h0 (hi ▸ l'.get_mem _))
      refine ⟨σ, ?_⟩
      rw [hσ]
      congr 1
      rw [ofFn_cast_eq hlen.symm l'.get, List.ofFn_get]

/-! ### El Finset de árboles planos etiquetados y su cardinal -/

open scoped Classical in
/-- Árboles planos etiquetados por `Fin (n+1)`: cada etiqueta aparece
exactamente una vez (las etiquetas en preorden permutan `finRange (n+1)`) y la
raíz lleva la etiqueta `0`.  Construido como imagen inyectiva de
(forma, lista de etiquetas); la caracterización semántica es
`mem_labeledTreesOn`. -/
noncomputable def labeledTreesOn (n : ℕ) : Finset (LTree (Fin (n + 1))) :=
  ((PlaneTree.treesOfSizeSucc n) ×ˢ headZeroPerms n).image
    fun p => decorate 0 p.1 p.2

theorem mem_labeledTreesOn {n : ℕ} {u : LTree (Fin (n + 1))} :
    u ∈ labeledTreesOn n ↔
      u.labels.Perm (List.finRange (n + 1)) ∧ u.rootLabel = 0 := by
  classical
  simp only [labeledTreesOn, Finset.mem_image, Finset.mem_product,
    PlaneTree.mem_treesOfSizeSucc]
  constructor
  · rintro ⟨⟨t, l⟩, ⟨ht, hl⟩, rfl⟩
    obtain ⟨hperm, hhead⟩ := mem_headZeroPerms.mp hl
    have hlen : l.length = t.size := by
      rw [length_of_mem_headZeroPerms hl, ht]
    have hlab : (decorate 0 t l).labels = l := labels_decorate 0 t l hlen
    refine ⟨by rw [hlab]; exact hperm, ?_⟩
    rw [rootLabel_decorate]
    cases l with
    | nil => simp at hhead
    | cons a l' =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp [hhead]
  · rintro ⟨hperm, hroot⟩
    refine ⟨(u.shape, u.labels), ⟨?_, ?_⟩, decorate_shape_labels 0 u⟩
    · rw [← LTree.length_labels u, hperm.length_eq, List.length_finRange]
    · rw [mem_headZeroPerms]
      exact ⟨hperm, by rw [LTree.head?_labels, hroot]⟩

/-- **(b3) Rigidez etiquetada:** hay exactamente `catalan n · n!` árboles
planos etiquetados por `Fin (n+1)` con raíz `0`. -/
theorem card_labeledTreesOn (n : ℕ) :
    (labeledTreesOn n).card = catalan n * n ! := by
  classical
  have hinj : Set.InjOn
      (fun p : PlaneTree × List (Fin (n + 1)) => decorate 0 p.1 p.2)
      (↑(PlaneTree.treesOfSizeSucc n ×ˢ headZeroPerms n) :
        Set (PlaneTree × List (Fin (n + 1)))) := by
    rintro ⟨t₁, l₁⟩ h₁ ⟨t₂, l₂⟩ h₂ h
    simp only [Finset.mem_coe, Finset.mem_product,
      PlaneTree.mem_treesOfSizeSucc] at h₁ h₂
    have e1 : l₁.length = t₁.size := by
      rw [length_of_mem_headZeroPerms h₁.2, h₁.1]
    have e2 : l₂.length = t₂.size := by
      rw [length_of_mem_headZeroPerms h₂.2, h₂.1]
    have hs : t₁ = t₂ := by
      have hh := congrArg LTree.shape h
      rwa [shape_decorate, shape_decorate] at hh
    have hl : l₁ = l₂ := by
      have hh := congrArg LTree.labels h
      rwa [labels_decorate 0 t₁ l₁ e1, labels_decorate 0 t₂ l₂ e2] at hh
    simp [hs, hl]
  rw [labeledTreesOn, Finset.card_image_of_injOn hinj, Finset.card_product,
    PlaneTree.card_treesOfSizeSucc, card_headZeroPerms]

/-- Variante con el orden de `word_sum_eq`: `n! · catalan n`. -/
theorem card_labeledTreesOn' (n : ℕ) :
    (labeledTreesOn n).card = n ! * catalan n := by
  rw [card_labeledTreesOn, Nat.mul_comm]

end RootedTreeCatalan

#print axioms RootedTreeCatalan.mem_headZeroPerms
#print axioms RootedTreeCatalan.card_headZeroPerms
#print axioms RootedTreeCatalan.decorate_shape_labels
#print axioms RootedTreeCatalan.labels_decorate
#print axioms RootedTreeCatalan.mem_labeledTreesOn
#print axioms RootedTreeCatalan.card_labeledTreesOn'
