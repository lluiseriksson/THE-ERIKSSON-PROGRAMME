/-
# Plane-tree Catalan count and sigma-cardinality bridge

This module develops two independent pieces of the rigidity route toward
`YangMills.KP.RootedChildFactorialCatalanIdentity`.

First, it defines rooted plane-tree shapes and proves the Catalan count for
shapes with `n + 1` nodes.  The proof transports Mathlib's binary-tree
enumeration across the left-child/right-sibling equivalence
`forestEquivBinTree : List PlaneTree ≃ Tree Unit`; the main theorem is
`PlaneTree.card_treesOfSizeSucc`.

Second, it proves the general finite-cardinality lemma
`sum_card_eq_card_sigma`, turning a sum of fiber cardinalities over a finite
index set into the cardinality of the corresponding sigma type.  In the
upstream repository this is intended to compose with
`card_rootedChildOrderAssignments`, rewriting the weighted tree sum as the
cardinality of pairs `(tree, ordering of rooted child fibers)`.

The remaining route-(b) obligations are outside this file:

* a labeled-rigidity count identifying rooted labeled plane trees with
  `n! * catalan n`;
* the upstream bridge from ordered complete-graph spanning trees, using
  `spanningTrees`, `bfsParent`, and `rootedChildCount`, to rooted labeled
  plane trees.

Checked target: Lean `leanprover/lean4:v4.29.0-rc6`, Mathlib
`07642720480157414db592fa85b626dafb71355b`.

Expected oracle for the printed theorems:
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Fintype.BigOperators

open Nat Finset

namespace RootedTreeCatalan

/-- Árbol plano enraizado (solo la forma): un nodo con una lista *ordenada*
de subárboles.  Es el objeto contado por los números de Catalan. -/
inductive PlaneTree : Type where
  | node : List PlaneTree → PlaneTree

namespace PlaneTree

/-- Los hijos de la raíz. -/
def children : PlaneTree → List PlaneTree
  | node cs => cs

@[simp] theorem children_node (cs : List PlaneTree) :
    children (node cs) = cs := rfl

@[simp] theorem node_children : ∀ t : PlaneTree, node t.children = t
  | node _ => rfl

theorem node_injective : Function.Injective node := by
  intro a b h
  injection h

mutual
  /-- Número de nodos de un árbol plano. -/
  def size : PlaneTree → ℕ
    | node cs => sizeForest cs + 1
  /-- Número total de nodos de un bosque plano. -/
  def sizeForest : List PlaneTree → ℕ
    | [] => 0
    | t :: ts => size t + sizeForest ts
end

@[simp] theorem size_node (cs : List PlaneTree) :
    size (node cs) = sizeForest cs + 1 := by
  simp [size]

@[simp] theorem sizeForest_nil : sizeForest ([] : List PlaneTree) = 0 := by
  simp [sizeForest]

@[simp] theorem sizeForest_cons (t : PlaneTree) (ts : List PlaneTree) :
    sizeForest (t :: ts) = size t + sizeForest ts := by
  simp [sizeForest]

/-! ### La correspondencia hijo-izquierdo / hermano-derecho (LCRS) -/

/-- LCRS: de bosques planos a árboles binarios.  El primer árbol del bosque
aporta la raíz; su bosque de hijos va al hijo izquierdo y el resto del bosque
(sus hermanos) al hijo derecho. -/
def forestToBin : List PlaneTree → Tree Unit
  | [] => .nil
  | node cs :: ts => .node () (forestToBin cs) (forestToBin ts)

/-- Inversa de LCRS: de árboles binarios a bosques planos. -/
def binToForest : Tree Unit → List PlaneTree
  | .nil => []
  | .node _ l r => node (binToForest l) :: binToForest r

theorem binToForest_forestToBin :
    ∀ f : List PlaneTree, binToForest (forestToBin f) = f
  | [] => by simp [forestToBin, binToForest]
  | node cs :: ts => by
      simp only [forestToBin, binToForest]
      rw [binToForest_forestToBin cs, binToForest_forestToBin ts]

theorem forestToBin_binToForest :
    ∀ t : Tree Unit, forestToBin (binToForest t) = t
  | .nil => by simp [binToForest, forestToBin]
  | .node () l r => by
      simp only [binToForest, forestToBin]
      rw [forestToBin_binToForest l, forestToBin_binToForest r]

/-- **La equivalencia LCRS**: bosques planos ≃ árboles binarios. -/
def forestEquivBinTree : List PlaneTree ≃ Tree Unit where
  toFun := forestToBin
  invFun := binToForest
  left_inv := binToForest_forestToBin
  right_inv := forestToBin_binToForest

/-- Un árbol plano es exactamente su bosque de hijos. -/
def planeTreeEquivForest : PlaneTree ≃ List PlaneTree where
  toFun := children
  invFun := node
  left_inv := node_children
  right_inv := fun _ => rfl

/-- Árboles planos ≃ árboles binarios (composición). -/
def planeTreeEquivBinTree : PlaneTree ≃ Tree Unit :=
  planeTreeEquivForest.trans forestEquivBinTree

/-- LCRS preserva el número de nodos. -/
theorem numNodes_forestToBin :
    ∀ f : List PlaneTree, (forestToBin f).numNodes = sizeForest f
  | [] => by simp [forestToBin, Tree.numNodes]
  | node cs :: ts => by
      simp only [forestToBin, Tree.numNodes, sizeForest_cons, size_node]
      rw [numNodes_forestToBin cs, numNodes_forestToBin ts]
      omega

theorem sizeForest_binToForest (t : Tree Unit) :
    sizeForest (binToForest t) = t.numNodes := by
  conv_rhs => rw [← forestToBin_binToForest t]
  exact (numNodes_forestToBin _).symm

/-! ### Conteo: transporte de `Tree.treesOfNumNodesEq` por LCRS -/

/-- Bosques planos con exactamente `n` nodos en total. -/
def forestsOfSize (n : ℕ) : Finset (List PlaneTree) :=
  (Tree.treesOfNumNodesEq n).map
    ⟨binToForest, Function.LeftInverse.injective forestToBin_binToForest⟩

@[simp] theorem mem_forestsOfSize {n : ℕ} {f : List PlaneTree} :
    f ∈ forestsOfSize n ↔ sizeForest f = n := by
  simp only [forestsOfSize, Finset.mem_map, Function.Embedding.coeFn_mk,
    Tree.mem_treesOfNumNodesEq]
  constructor
  · rintro ⟨t, hn, rfl⟩
    rw [sizeForest_binToForest]
    exact hn
  · intro h
    exact ⟨forestToBin f, by rw [numNodes_forestToBin]; exact h,
      binToForest_forestToBin f⟩

theorem card_forestsOfSize (n : ℕ) : (forestsOfSize n).card = catalan n := by
  rw [forestsOfSize, Finset.card_map, Tree.treesOfNumNodesEq_card_eq_catalan]

/-- Árboles planos con exactamente `n + 1` nodos. -/
def treesOfSizeSucc (n : ℕ) : Finset PlaneTree :=
  (forestsOfSize n).map ⟨node, node_injective⟩

@[simp] theorem mem_treesOfSizeSucc {n : ℕ} {t : PlaneTree} :
    t ∈ treesOfSizeSucc n ↔ size t = n + 1 := by
  simp only [treesOfSizeSucc, Finset.mem_map, Function.Embedding.coeFn_mk,
    mem_forestsOfSize]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [size_node, hf]
  · intro h
    obtain ⟨cs⟩ := t
    rw [size_node] at h
    exact ⟨cs, by omega, rfl⟩

/-- **(b4) Hay exactamente `catalan n` formas de árbol plano con `n + 1`
nodos.**  Éste es el lado Catalan de la ruta de rigidez. -/
theorem card_treesOfSizeSucc (n : ℕ) : (treesOfSizeSucc n).card = catalan n := by
  rw [treesOfSizeSucc, Finset.card_map, card_forestsOfSize]

example : (treesOfSizeSucc 2).card = 2 := by
  rw [card_treesOfSizeSucc, catalan_two]

end PlaneTree

/-! ### (b1) La suma de factoriales de hijos como cardinal de un sigma-tipo -/

/-- Genérico: una suma de cardinales sobre un `Finset` es el cardinal del
sigma-tipo correspondiente.  Instanciado con
`A T := rootedChildOrderAssignments T` y
`card_rootedChildOrderAssignments` (ya en el repo), da

  `Σ_{T ∈ spanningTrees ⊤} ∏_v (rootedChildCount T v)!
     = Fintype.card ((T : spanningTrees ⊤) × rootedChildOrderAssignments T)`,

es decir: la suma de pesos factoriales cuenta pares (árbol, ordenación de
hijos) — el primer paso de la ruta de rigidez. -/
theorem sum_card_eq_card_sigma {ι : Type*} (S : Finset ι) (A : ι → Type*)
    [∀ i, Fintype (A i)] :
    (∑ i ∈ S, Fintype.card (A i)) = Fintype.card ((i : S) × A i) := by
  rw [Fintype.card_sigma]
  exact (Finset.sum_coe_sort (s := S) (f := fun i => Fintype.card (A i))).symm

end RootedTreeCatalan

#print axioms RootedTreeCatalan.PlaneTree.card_treesOfSizeSucc
#print axioms RootedTreeCatalan.PlaneTree.mem_treesOfSizeSucc
#print axioms RootedTreeCatalan.PlaneTree.numNodes_forestToBin
#print axioms RootedTreeCatalan.sum_card_eq_card_sigma
