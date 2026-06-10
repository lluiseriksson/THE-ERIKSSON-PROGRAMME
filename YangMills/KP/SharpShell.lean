/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.SharpMajorant
import YangMills.KP.PinnedCluster
import YangMills.KP.PenroseFiber

/-!
# Sharp KP, step 5 — the shell decomposition (combinatorial half)

`docs/SHARP-KP-PLAN.md`, remaining brick, steps C1–C4.  This file hosts the
combinatorial half of the sharp Kotecký–Preiss bound: pinned cluster sums
are dominated by the depth-recursion majorant `kpMajorant`.

Landed so far:

* **C1** (`exists_adj_reachable_in_deleted`): in a connected graph, every
  vertex other than `v₀` reaches a neighbor of `v₀` inside the
  vertex-deleted subgraph — i.e., every component of `G − v₀` is attached
  to `v₀`.  This is what makes each first-shell subtree's root polymer
  incompatible with the pinned polymer in the shell recursion (C3).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

/-- **C1 — root deletion keeps components attached:** in a connected graph,
any vertex `u ≠ v₀` can reach, *within the subgraph induced on the
complement of `v₀`*, some neighbor `w` of `v₀`.  (Equivalently: every
connected component of `G − v₀` contains a neighbor of `v₀`.) -/
theorem exists_adj_reachable_in_deleted {α : Type*} {G : SimpleGraph α}
    {v₀ : α} :
    ∀ {u b : α} (_ : G.Walk u b) (_ : b = v₀) (hu : u ≠ v₀),
      ∃ (w : α) (hw : w ≠ v₀), G.Adj v₀ w ∧
        (G.induce {x | x ≠ v₀}).Reachable ⟨u, hu⟩ ⟨w, hw⟩ := by
  intro u b p
  induction p with
  | nil => intro hb hu; exact absurd hb hu
  | @cons a c _ h q ih =>
      intro hb hu
      by_cases hc : c = v₀
      · -- `a` is itself a neighbor of `v₀`
        subst hc
        exact ⟨a, hu, h.symm, SimpleGraph.Reachable.refl _⟩
      · -- recurse along the walk, prepending the edge `a–c`
        obtain ⟨w, hw, hadj, hreach⟩ := ih hb hc
        refine ⟨w, hw, hadj, SimpleGraph.Reachable.trans ?_ hreach⟩
        refine SimpleGraph.Adj.reachable ?_
        exact (SimpleGraph.induce_adj).mpr h

/-- C1, packaged from connectivity: any non-root vertex reaches a root
neighbor in the deleted graph. -/
theorem exists_adj_reachable_in_deleted_of_connected {α : Type*}
    {G : SimpleGraph α} (hc : G.Connected) (v₀ : α) {u : α} (hu : u ≠ v₀) :
    ∃ (w : α) (hw : w ≠ v₀), G.Adj v₀ w ∧
      (G.induce {x | x ≠ v₀}).Reachable ⟨u, hu⟩ ⟨w, hw⟩ := by
  obtain ⟨p⟩ := hc.preconnected u v₀
  exact exists_adj_reachable_in_deleted p rfl hu

/-- Graph distances on a finite connected graph are bounded by the vertex
count: geodesics are realized by paths, and paths have fewer edges than
vertices.  (Bounds BFS levels into `Fin (n+1)` for the `treeSumRaw`
indexing.) -/
theorem connected_dist_lt_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) (u v : V) :
    G.dist u v < Fintype.card V := by
  classical
  obtain ⟨w, hw⟩ := (hc.preconnected u v).exists_walk_length_eq_dist
  have h1 : G.dist u v ≤ w.bypass.length :=
    SimpleGraph.dist_le _
  have h2 : w.bypass.length < Fintype.card V :=
    (SimpleGraph.Walk.bypass_isPath w).length_lt
  omega

section TreeSum

/-- **Admissibility** of a rooted parent/level structure on `Fin (n+1)`:
the root `0` sits at level `0`, and every non-root vertex's parent lies
strictly below it.  Each admissible pair encodes (at most one) rooted
forest reaching down toward the root; spanning trees of incompatibility
graphs land here via their BFS parent/level data. -/
def IsAdmissible {n D : ℕ} (p : Fin (n + 1) → Fin (n + 1))
    (lev : Fin (n + 1) → Fin (D + 1)) : Prop :=
  lev 0 = 0 ∧ ∀ v, v ≠ 0 → ((lev (p v) : ℕ) + 1 = (lev v : ℕ))

instance {n D : ℕ} (p : Fin (n + 1) → Fin (n + 1))
    (lev : Fin (n + 1) → Fin (D + 1)) : Decidable (IsAdmissible p lev) := by
  unfold IsAdmissible
  infer_instance

open Classical in
/-- **The raw depth-`D` rooted tree-sum** pinned at `c` (no factorial
normalization — fixed at assembly): the sum over admissible parent/level
structures and pinned polymer assignments of the tree-compatibility
indicator times the non-root activities.  C2 dominates pinned cluster
weights by `treeSumRaw`; C3 runs the shell recursion on it. -/
noncomputable def treeSumRaw (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) (D n : ℕ) : ℝ :=
  ∑ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
      × (Fin (n + 1) → Fin (D + 1)))).filter
      (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0),
    ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X => X 0 = c),
      ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
        (if P.incomp (X (pl.1 v)) (X v) then (1 : ℝ) else 0)
          * ‖P.activity (X v)‖

open Classical in
lemma treeSumRaw_nonneg (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) (D n : ℕ) : 0 ≤ treeSumRaw P c D n := by
  unfold treeSumRaw
  refine Finset.sum_nonneg fun pl _ => Finset.sum_nonneg fun X _ =>
    Finset.prod_nonneg fun v _ => mul_nonneg ?_ (norm_nonneg _)
  split_ifs <;> norm_num

/-- The BFS parent of the root is the root itself (no candidates one level
below `0`). -/
lemma bfsParent_zero {m : ℕ} (E : Finset (Sym2 (Fin (m + 1)))) :
    bfsParent E 0 = 0 := by
  unfold bfsParent
  rw [dif_neg]
  rintro ⟨u, hu⟩
  rw [mem_bfsParentSet] at hu
  have h2 := hu.2
  rw [bfsLevel_zero_eq] at h2
  omega

open Classical in
/-- **C2 — Penrose domination of pinned cluster weights:** every pinned
cluster weight is controlled by the raw rooted tree-sum at full depth,
with the pinned activity factored out:
`pinnedClusterWeight P c n ≤ (1/(n+1)!)·‖z(c)‖·treeSumRaw P c n n`.
Penrose expands `|φ(X)|` over spanning trees; each spanning tree embeds
injectively into the admissible parent/level index via its BFS data
(parents determine the tree — `penroseTree_of_spanningTree`), and BFS
levels fit in `Fin (n+1)` by `connected_dist_lt_card`. -/
theorem pinnedClusterWeight_le_treeSumRaw (P : PolymerSystem)
    [Fintype P.Polymer] (c : P.Polymer) (n : ℕ) :
    pinnedClusterWeight P c n
      ≤ (((n + 1).factorial : ℝ))⁻¹ * ‖P.activity c‖
          * treeSumRaw P c n n := by
  classical
  -- the universal tree shapes (as in `kp_per_size_bound`)
  set Sh : Finset (Finset (Sym2 (Fin (n + 1)))) :=
    (Finset.univ).filter (fun T : Finset (Sym2 (Fin (n + 1))) =>
      (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin (n + 1))))).IsTree ∧
        ∀ e ∈ T, ¬ e.IsDiag) with hShdef
  have htop : ∀ T ∈ Sh,
      T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))) := by
    intro T hT
    rw [hShdef, Finset.mem_filter] at hT
    unfold spanningTrees
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun e he => ?_, hT.2.1⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet]
    exact hT.2.2 e he
  have hpen : ∀ X : Fin (n + 1) → P.Polymer,
      |((ursell P X : ℤ) : ℝ)|
        ≤ ∑ T ∈ Sh, ∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet
            then (1 : ℝ) else 0 := by
    intro X
    have h1 := abs_ursell_le_card_spanningTrees P X
    have h2 : |((ursell P X : ℤ) : ℝ)|
        ≤ ((spanningTrees (incompGraph P X)).card : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast h1
    refine le_trans h2 ?_
    have hsub : spanningTrees (incompGraph P X) ⊆ Sh := by
      intro T hT
      rw [hShdef, Finset.mem_filter]
      refine ⟨Finset.mem_univ T, isTree_of_mem_spanningTrees _ hT, ?_⟩
      intro e he
      have hmem := spanningTrees_subset _ hT he
      rw [SimpleGraph.mem_edgeFinset] at hmem
      exact (incompGraph P X).not_isDiag_of_mem_edgeSet hmem
    have h3 : ((spanningTrees (incompGraph P X)).card : ℝ)
        = ∑ T ∈ spanningTrees (incompGraph P X),
            ∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet
              then (1 : ℝ) else 0 := by
      rw [Finset.sum_congr rfl (fun T hT => Finset.prod_eq_one
        (fun e he => by
          have hmem := spanningTrees_subset _ hT he
          rw [SimpleGraph.mem_edgeFinset] at hmem
          rw [if_pos hmem]))]
      simp
    rw [h3]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun T _ _ => Finset.prod_nonneg fun e _ => by
        split_ifs <;> norm_num)
  -- the BFS embedding of shapes into the admissible index
  set φ : Finset (Sym2 (Fin (n + 1)))
      → (Fin (n + 1) → Fin (n + 1)) × (Fin (n + 1) → Fin (n + 1)) :=
    fun T => (bfsParent T, fun v =>
      if hco : (SimpleGraph.fromEdgeSet
          (↑T : Set (Sym2 (Fin (n + 1))))).Connected
      then ⟨bfsLevel T v, by
        have := connected_dist_lt_card hco 0 v
        simpa [bfsLevel, Fintype.card_fin] using this⟩
      else 0) with hφdef
  -- per-tree inner sums (the quantity transported along φ)
  set G : (Fin (n + 1) → Fin (n + 1)) × (Fin (n + 1) → Fin (n + 1)) → ℝ :=
    fun pl => ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
      ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
        (if P.incomp (X (pl.1 v)) (X v) then (1 : ℝ) else 0)
          * ‖P.activity (X v)‖ with hGdef
  have hGnn : ∀ pl, 0 ≤ G pl := by
    intro pl
    rw [hGdef]
    refine Finset.sum_nonneg fun X _ =>
      Finset.prod_nonneg fun v _ => mul_nonneg ?_ (norm_nonneg _)
    split_ifs <;> norm_num
  -- each shape's compatibility-weighted pinned sum equals `G (φ T)`
  have htreeG : ∀ T ∈ Sh,
      ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
        (∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)
          * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
              ‖P.activity (X v)‖
        = G (φ T) := by
    intro T hT
    have htree := isTree_of_mem_spanningTrees _ (htop T hT)
    have hconn := htree.isConnected
    rw [hGdef]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [prod_tree_eq_prod_parents (htop T hT)
      (fun e => if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)]
    have hfac : ∀ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
        (if s(bfsParent T v, v) ∈ (incompGraph P X).edgeSet
          then (1 : ℝ) else 0)
        = if P.incomp (X (bfsParent T v)) (X v) then (1 : ℝ) else 0 := by
      intro v hv
      rw [Finset.mem_filter] at hv
      have hne : bfsParent T v ≠ v := by
        have hspec := (bfsParent_spec hconn hv.2).2
        intro hEq
        rw [hEq] at hspec
        omega
      simp [SimpleGraph.mem_edgeSet, incompGraph_adj, hne]
    rw [Finset.prod_congr rfl hfac, ← Finset.prod_mul_distrib]
  -- φ lands in the admissible index
  have hmaps : ∀ T ∈ Sh, φ T ∈ (Finset.univ :
      Finset ((Fin (n + 1) → Fin (n + 1))
        × (Fin (n + 1) → Fin (n + 1)))).filter
      (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0) := by
    intro T hT
    have htree := isTree_of_mem_spanningTrees _ (htop T hT)
    have hconn := htree.isConnected
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨?_, ?_⟩, ?_⟩
    · -- root level 0
      show (φ T).2 0 = 0
      rw [hφdef]
      simp only [dif_pos hconn]
      apply Fin.ext
      simp [bfsLevel_zero_eq]
    · -- exact level increment
      intro v hv
      show ((φ T).2 ((φ T).1 v) : ℕ) + 1 = ((φ T).2 v : ℕ)
      rw [hφdef]
      simp only [dif_pos hconn]
      have hspec := (bfsParent_spec hconn hv).2
      omega
    · -- root canonicity
      show (φ T).1 0 = 0
      rw [hφdef]
      exact bfsParent_zero T
  -- φ is injective on shapes: parents determine the tree
  have hinj : ∀ T₁ ∈ Sh, ∀ T₂ ∈ Sh, φ T₁ = φ T₂ → T₁ = T₂ := by
    intro T₁ h₁ T₂ h₂ heq
    have e₁ : penroseTree T₁ = T₁ :=
      penroseTree_of_spanningTree (htop T₁ h₁)
    have e₂ : penroseTree T₂ = T₂ :=
      penroseTree_of_spanningTree (htop T₂ h₂)
    have hpar : bfsParent T₁ = bfsParent T₂ := by
      have := congrArg Prod.fst heq
      rw [hφdef] at this
      exact this
    rw [← e₁, ← e₂]
    unfold penroseTree
    rw [hpar]
  -- assemble
  unfold pinnedClusterWeight
  have hfactor : ∀ X ∈ (Finset.univ :
      Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
      |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖
      = ‖P.activity c‖ * (|((ursell P X : ℤ) : ℝ)|
          * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
              ‖P.activity (X v)‖) := by
    intro X hX
    rw [Finset.mem_filter] at hX
    have hsplit : ∏ i, ‖P.activity (X i)‖
        = (∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
            ‖P.activity (X v)‖) * ‖P.activity (X 0)‖ := by
      rw [Finset.filter_ne',
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ 0)]
      ring
    rw [hsplit, hX.2]
    ring
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
        |((ursell P X : ℤ) : ℝ)|
          * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
              ‖P.activity (X v)‖
      ≤ ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
          (∑ T ∈ Sh, ∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet
              then (1 : ℝ) else 0)
            * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
                ‖P.activity (X v)‖ := by
        refine Finset.sum_le_sum fun X _ => ?_
        exact mul_le_mul_of_nonneg_right (hpen X)
          (Finset.prod_nonneg fun v _ => norm_nonneg _)
    _ = ∑ T ∈ Sh, ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
          (∏ e ∈ T, if e ∈ (incompGraph P X).edgeSet then (1 : ℝ) else 0)
            * ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
                ‖P.activity (X v)‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun X _ => by rw [Finset.sum_mul]
    _ = ∑ T ∈ Sh, G (φ T) := Finset.sum_congr rfl htreeG
    _ = ∑ pl ∈ Sh.image φ, G pl := (Finset.sum_image hinj).symm
    _ ≤ ∑ pl ∈ (Finset.univ :
          Finset ((Fin (n + 1) → Fin (n + 1))
            × (Fin (n + 1) → Fin (n + 1)))).filter
          (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0), G pl := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun pl _ _ => hGnn pl)
        intro pl hpl
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hpl
        exact hmaps T hT
    _ = treeSumRaw P c n n := by
        unfold treeSumRaw
        exact Finset.sum_congr rfl fun pl _ => by rw [hGdef]

open Classical in
/-- `treeSumRaw` is monotone in the depth: deeper structures include the
shallower ones (levels embed along `Fin.castSucc`; the summand reads only
the parent map). -/
lemma treeSumRaw_mono_depth (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) (D n : ℕ) :
    treeSumRaw P c D n ≤ treeSumRaw P c (D + 1) n := by
  classical
  unfold treeSumRaw
  set ψ : (Fin (n + 1) → Fin (n + 1)) × (Fin (n + 1) → Fin (D + 1))
      → (Fin (n + 1) → Fin (n + 1)) × (Fin (n + 1) → Fin (D + 2)) :=
    fun pl => (pl.1, fun v => (pl.2 v).castSucc) with hψdef
  have hinj : ∀ pl₁ ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
        × (Fin (n + 1) → Fin (D + 1)))).filter
        (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0),
      ∀ pl₂ ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
        × (Fin (n + 1) → Fin (D + 1)))).filter
        (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0),
      ψ pl₁ = ψ pl₂ → pl₁ = pl₂ := by
    intro pl₁ _ pl₂ _ h
    rw [hψdef] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    refine Prod.ext h1 ?_
    funext v
    have := congrFun h2 v
    exact Fin.castSucc_injective _ this
  set G : ((Fin (n + 1) → Fin (n + 1)) × (Fin (n + 1) → Fin (D + 2))) → ℝ :=
    fun pl => ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
      ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
        (if P.incomp (X (pl.1 v)) (X v) then (1 : ℝ) else 0)
          * ‖P.activity (X v)‖ with hGdef
  calc ∑ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
        × (Fin (n + 1) → Fin (D + 1)))).filter
        (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0),
        ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
          ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
            (if P.incomp (X (pl.1 v)) (X v) then (1 : ℝ) else 0)
              * ‖P.activity (X v)‖
      = ∑ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
          × (Fin (n + 1) → Fin (D + 1)))).filter
          (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0), G (ψ pl) :=
        Finset.sum_congr rfl fun pl _ => rfl
    _ = ∑ q ∈ ((Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
          × (Fin (n + 1) → Fin (D + 1)))).filter
          (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0)).image ψ, G q :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
          × (Fin (n + 1) → Fin (D + 2)))).filter
          (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0), G q := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => ?_)
        · intro q hq
          obtain ⟨pl, hpl, rfl⟩ := Finset.mem_image.mp hq
          rw [Finset.mem_filter] at hpl ⊢
          obtain ⟨⟨hlev0, hdesc⟩, hp0⟩ := hpl.2
          refine ⟨Finset.mem_univ _, ⟨?_, ?_⟩, ?_⟩
          · show ((ψ pl).2 0) = 0
            rw [hψdef]
            apply Fin.ext
            simp only [Fin.coe_castSucc]
            exact congrArg Fin.val hlev0
          · intro v hv
            show (((ψ pl).2 ((ψ pl).1 v)) : ℕ) + 1 = (((ψ pl).2 v) : ℕ)
            rw [hψdef]
            simpa using hdesc v hv
          · show ((ψ pl).1 0) = 0
            rw [hψdef]
            exact hp0
        · rw [hGdef]
          refine Finset.sum_nonneg fun X _ =>
            Finset.prod_nonneg fun v _ => mul_nonneg ?_ (norm_nonneg _)
          split_ifs <;> norm_num
    _ = ∑ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
          × (Fin (n + 1) → Fin (D + 2)))).filter
          (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0),
          ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
            ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
              (if P.incomp (X (pl.1 v)) (X v) then (1 : ℝ) else 0)
                * ‖P.activity (X v)‖ :=
        Finset.sum_congr rfl fun pl _ => by rw [hGdef]

open Classical in
/-- Depth `0`, size `0`: only the trivial structure, value `1`
(`= kpMajorant P 0 c`). -/
lemma treeSumRaw_zero_zero (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) : treeSumRaw P c 0 0 = 1 := by
  classical
  unfold treeSumRaw
  have hfil : (Finset.univ : Finset ((Fin 1 → Fin 1)
      × (Fin 1 → Fin 1))).filter (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0)
      = Finset.univ := by
    refine Finset.filter_true_of_mem fun pl _ => ?_
    refine ⟨⟨by omega, fun v hv => ?_⟩, by omega⟩
    exact absurd (by omega : v = 0) hv
  rw [hfil]
  have hprod : ∀ (pl : (Fin 1 → Fin 1) × (Fin 1 → Fin 1))
      (X : Fin 1 → P.Polymer),
      (∏ v ∈ Finset.univ.filter (fun v : Fin 1 => v ≠ 0),
        (if P.incomp (X (pl.1 v)) (X v) then (1 : ℝ) else 0)
          * ‖P.activity (X v)‖) = 1 := by
    intro pl X
    have : (Finset.univ : Finset (Fin 1)).filter (fun v => v ≠ 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v _
      simp [show v = 0 from by omega]
    rw [this, Finset.prod_empty]
  have hXcard : ((Finset.univ : Finset (Fin 1 → P.Polymer)).filter
      (fun X => X 0 = c)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨fun _ => c, ?_⟩
    ext X
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hX
      funext v
      have hv0 : v = 0 := by omega
      rw [hv0, hX.2]
    · intro hX
      exact ⟨Finset.mem_univ _, by rw [hX]⟩
  have hinner : ∀ pl : (Fin 1 → Fin 1) × (Fin 1 → Fin 1),
      (∑ X ∈ (Finset.univ : Finset (Fin 1 → P.Polymer)).filter
        (fun X => X 0 = c),
        ∏ v ∈ Finset.univ.filter (fun v : Fin 1 => v ≠ 0),
          (if P.incomp (X (pl.1 v)) (X v) then (1 : ℝ) else 0)
            * ‖P.activity (X v)‖) = 1 := by
    intro pl
    rw [Finset.sum_congr rfl (fun X _ => hprod pl X), Finset.sum_const,
      hXcard, one_smul]
  rw [Finset.sum_congr rfl (fun pl _ => hinner pl), Finset.sum_const]
  have hcard : (Finset.univ : Finset ((Fin 1 → Fin 1)
      × (Fin 1 → Fin 1))).card = 1 := by
    simp [Finset.card_univ]
  rw [hcard, one_smul]

open Classical in
/-- Depth `0`, positive size: no admissible structures (descent is
impossible inside `Fin 1`), value `0`. -/
lemma treeSumRaw_zero_succ (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) (n : ℕ) : treeSumRaw P c 0 (n + 1) = 0 := by
  classical
  unfold treeSumRaw
  have hfil : (Finset.univ : Finset ((Fin (n + 2) → Fin (n + 2))
      × (Fin (n + 2) → Fin 1))).filter (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0)
      = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro pl _
    intro hadm
    have h1 : (1 : Fin (n + 2)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have := hadm.1.2 1 h1
    have h2 := (pl.2 1).isLt
    omega
  rw [hfil, Finset.sum_empty]

section ShellRoot

variable {n D : ℕ} {p : Fin (n + 1) → Fin (n + 1)}
  {lev : Fin (n + 1) → Fin (D + 1)}

/-- Non-root vertices of admissible structures sit at level ≥ 1. -/
lemma IsAdmissible.one_le_lev (h : IsAdmissible p lev) {v : Fin (n + 1)}
    (hv : v ≠ 0) : 1 ≤ (lev v : ℕ) := by
  have := h.2 v hv
  omega

/-- Level `0` characterizes the root. -/
lemma IsAdmissible.lev_eq_zero_iff (h : IsAdmissible p lev)
    {v : Fin (n + 1)} : (lev v : ℕ) = 0 ↔ v = 0 := by
  constructor
  · intro hz
    by_contra hv
    have := h.one_le_lev hv
    omega
  · intro hv
    rw [hv]
    exact congrArg Fin.val h.1

/-- **The first shell is exactly the children of the root**: for `v ≠ 0`,
`p v = 0 ↔ lev v = 1` (this is what exact increments buy). -/
lemma IsAdmissible.parent_eq_zero_iff (h : IsAdmissible p lev)
    {v : Fin (n + 1)} (hv : v ≠ 0) :
    p v = 0 ↔ (lev v : ℕ) = 1 := by
  have hstep := h.2 v hv
  constructor
  · intro hp
    have : (lev (p v) : ℕ) = 0 := by
      rw [hp]
      exact congrArg Fin.val h.1
    omega
  · intro h1
    have : (lev (p v) : ℕ) = 0 := by omega
    exact h.lev_eq_zero_iff.mp this

/-- Iterating the parent map descends levels one step at a time. -/
lemma IsAdmissible.lev_iterate (h : IsAdmissible p lev) (v : Fin (n + 1)) :
    ∀ j, j ≤ (lev v : ℕ) - 1 →
      (lev (p^[j] v) : ℕ) = (lev v : ℕ) - j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      have hjle : j ≤ (lev v : ℕ) - 1 := by omega
      have hlev := ih hjle
      have hne : p^[j] v ≠ 0 := by
        intro hzero
        have : (lev (p^[j] v) : ℕ) = 0 := by
          rw [hzero]
          exact congrArg Fin.val h.1
        omega
      have hstep := h.2 _ hne
      rw [Function.iterate_succ_apply']
      omega

/-- **The shell root**: the level-`1` ancestor of a vertex, in closed form
(`p` iterated `lev v − 1` times).  This is the partition map of the shell
recursion: each non-root vertex belongs to the subtree of its shell root. -/
def shellRoot (p : Fin (n + 1) → Fin (n + 1))
    (lev : Fin (n + 1) → Fin (D + 1)) (v : Fin (n + 1)) : Fin (n + 1) :=
  p^[(lev v : ℕ) - 1] v

/-- The shell root sits at level `1`. -/
lemma IsAdmissible.lev_shellRoot (h : IsAdmissible p lev)
    {v : Fin (n + 1)} (hv : v ≠ 0) :
    (lev (shellRoot p lev v) : ℕ) = 1 := by
  have h1 := h.one_le_lev hv
  have := h.lev_iterate v ((lev v : ℕ) - 1) le_rfl
  unfold shellRoot
  omega

/-- The shell root is not the root. -/
lemma IsAdmissible.shellRoot_ne_zero (h : IsAdmissible p lev)
    {v : Fin (n + 1)} (hv : v ≠ 0) : shellRoot p lev v ≠ 0 := by
  intro hzero
  have := h.lev_shellRoot hv
  rw [hzero] at this
  have hz : (lev (0 : Fin (n + 1)) : ℕ) = 0 := congrArg Fin.val h.1
  omega

/-- The shell root is a child of the root. -/
lemma IsAdmissible.parent_shellRoot (h : IsAdmissible p lev)
    {v : Fin (n + 1)} (hv : v ≠ 0) : p (shellRoot p lev v) = 0 :=
  (h.parent_eq_zero_iff (h.shellRoot_ne_zero hv)).mpr (h.lev_shellRoot hv)

/-- Level-`1` vertices are their own shell roots. -/
lemma shellRoot_eq_self {v : Fin (n + 1)} (h1 : (lev v : ℕ) = 1) :
    shellRoot p lev v = v := by
  unfold shellRoot
  rw [h1]
  simp

/-- Deeper vertices share their parent's shell root — membership in a
shell subtree is invariant along the tree. -/
lemma IsAdmissible.shellRoot_parent (h : IsAdmissible p lev)
    {v : Fin (n + 1)} (hv : v ≠ 0) (h2 : 2 ≤ (lev v : ℕ)) :
    shellRoot p lev (p v) = shellRoot p lev v := by
  have hstep := h.2 v hv
  unfold shellRoot
  obtain ⟨m, hm⟩ : ∃ m, (lev v : ℕ) - 1 = m + 1 :=
    ⟨(lev v : ℕ) - 2, by omega⟩
  have e1 : (lev (p v) : ℕ) - 1 = m := by omega
  rw [e1, hm, Function.iterate_succ_apply]

open Classical in
/-- **The shell-fiber partition:** the non-root vertices are the disjoint
union, over the first shell (children of the root), of the `shellRoot`
fibers — each vertex belongs to exactly one shell subtree. -/
lemma shell_fiber_partition (h : IsAdmissible p lev) :
    (Finset.univ : Finset (Fin (n + 1))).filter (fun v => v ≠ 0)
      = ((Finset.univ : Finset (Fin (n + 1))).filter
          (fun s => s ≠ 0 ∧ p s = 0)).biUnion
          (fun s => (Finset.univ : Finset (Fin (n + 1))).filter
            (fun v => v ≠ 0 ∧ shellRoot p lev v = s)) := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  constructor
  · intro hv
    exact ⟨shellRoot p lev v,
      ⟨h.shellRoot_ne_zero hv, h.parent_shellRoot hv⟩, hv, rfl⟩
  · rintro ⟨s, _, hv, -⟩
    exact hv

open Classical in
/-- Shell fibers are pairwise disjoint (fibers of a function). -/
lemma shell_fiber_disjoint {s₁ s₂ : Fin (n + 1)} (hne : s₁ ≠ s₂) :
    Disjoint
      ((Finset.univ : Finset (Fin (n + 1))).filter
        (fun v => v ≠ 0 ∧ shellRoot p lev v = s₁))
      ((Finset.univ : Finset (Fin (n + 1))).filter
        (fun v => v ≠ 0 ∧ shellRoot p lev v = s₂)) := by
  rw [Finset.disjoint_left]
  intro v hv₁ hv₂
  rw [Finset.mem_filter] at hv₁ hv₂
  exact hne (hv₁.2.2 ▸ hv₂.2.2 ▸ rfl)

end ShellRoot

end TreeSum

section BlockCount

variable {n k : ℕ}

/-- **Ordered rooted-block data** with prescribed sizes: `k` pairwise
disjoint blocks covering a fixed set `U`, each with a marked root,
block `i` of size `m i + 1`.  These parametrize the fibers of the shell
decomposition (unsorted form; `U` will be the non-root vertices — see
`docs/SHARP-KP-PLAN.md`, C3 design correction). -/
def IsBlockData (U : Finset (Fin n)) (m : Fin k → ℕ)
    (ρ : Fin k → Finset (Fin n) × Fin n) : Prop :=
  (∀ i j, i ≠ j → Disjoint (ρ i).1 (ρ j).1) ∧
  (Finset.univ.biUnion (fun i => (ρ i).1) = U) ∧
  (∀ i, (ρ i).2 ∈ (ρ i).1) ∧ (∀ i, (ρ i).1.card = m i + 1)

/-- Each block sits inside the cover. -/
lemma IsBlockData.block_subset {U : Finset (Fin n)} {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData U m ρ)
    (i : Fin k) : (ρ i).1 ⊆ U := by
  classical
  rw [← hρ.2.1]
  exact Finset.subset_biUnion_of_mem (fun j => (ρ j).1) (Finset.mem_univ i)

/-- Block sizes account for the whole cover: `∑ (m i + 1) = U.card`. -/
lemma IsBlockData.sum_card {U : Finset (Fin n)} {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData U m ρ) :
    ∑ i, (m i + 1) = U.card := by
  classical
  have hcb : (Finset.univ.biUnion (fun i => (ρ i).1)).card
      = ∑ i, (ρ i).1.card :=
    Finset.card_biUnion (fun i _ j _ hij => hρ.1 i j hij)
  rw [← hρ.2.1, hcb]
  exact Finset.sum_congr rfl fun i _ => (hρ.2.2.2 i).symm

/-- Every covered vertex lies in exactly one block. -/
lemma IsBlockData.existsUnique_mem {U : Finset (Fin n)} {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData U m ρ)
    {v : Fin n} (hv : v ∈ U) : ∃! i, v ∈ (ρ i).1 := by
  have hv' : v ∈ Finset.univ.biUnion (fun i => (ρ i).1) := by
    rw [hρ.2.1]
    exact hv
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv'
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hne
  exact (Finset.disjoint_left.mp (hρ.1 j i hne) hj) hi

/-- The block index of a covered vertex. -/
noncomputable def IsBlockData.blockIndex {U : Finset (Fin n)}
    {m : Fin k → ℕ} {ρ : Fin k → Finset (Fin n) × Fin n}
    (hρ : IsBlockData U m ρ) {v : Fin n} (hv : v ∈ U) : Fin k :=
  (hρ.existsUnique_mem hv).exists.choose

lemma IsBlockData.mem_blockIndex {U : Finset (Fin n)} {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData U m ρ)
    {v : Fin n} (hv : v ∈ U) : v ∈ (ρ (hρ.blockIndex hv)).1 :=
  (hρ.existsUnique_mem hv).exists.choose_spec

lemma IsBlockData.blockIndex_eq {U : Finset (Fin n)} {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData U m ρ)
    {v : Fin n} (hv : v ∈ U) {i : Fin k} (h : v ∈ (ρ i).1) :
    hρ.blockIndex hv = i :=
  (hρ.existsUnique_mem hv).unique (hρ.mem_blockIndex hv) h

/-- **The partition equivalence:** the cover is the disjoint union of the
blocks — vertices of `U` correspond exactly to (block index, block
element) pairs.  This is the backbone of the consistent-sum factorization
(splice step S2): function spaces over `U` split along it with no
dependent-Finset machinery. -/
noncomputable def IsBlockData.partitionEquiv {U : Finset (Fin n)}
    {m : Fin k → ℕ} {ρ : Fin k → Finset (Fin n) × Fin n}
    (hρ : IsBlockData U m ρ) :
    (Σ i : Fin k, {x // x ∈ (ρ i).1}) ≃ {x // x ∈ U} := by
  refine Equiv.ofBijective
    (fun y => ⟨y.2.1, hρ.block_subset y.1 y.2.2⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩)
  · rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ h
    have hval : x = y := congrArg Subtype.val h
    subst hval
    have hij : i = j := by
      by_contra hne
      exact (Finset.disjoint_left.mp (hρ.1 i j hne) hx) hy
    subst hij
    rfl
  · have hcards : ∀ i : Fin k,
        Fintype.card {x // x ∈ (ρ i).1} = m i + 1 := fun i => by
      rw [Fintype.card_coe, hρ.2.2.2 i]
    rw [Fintype.card_sigma, Fintype.card_coe]
    simp only [hcards]
    exact hρ.sum_card

/-- **The cover-splitting equivalence:** functions on the cover are
exactly tuples of functions on the blocks. -/
noncomputable def IsBlockData.coverSplitEquiv {U : Finset (Fin n)}
    {m : Fin k → ℕ} {ρ : Fin k → Finset (Fin n) × Fin n}
    (hρ : IsBlockData U m ρ) (β : Type*) :
    ({x // x ∈ U} → β) ≃ ∀ i : Fin k, ({x // x ∈ (ρ i).1} → β) :=
  (Equiv.arrowCongr hρ.partitionEquiv.symm (Equiv.refl β)).trans
    (Equiv.piCurry fun _ _ => β)

/-- **Sums of block-products factor over the cover (S2 engine):** summing
a product of per-block factors over all functions on the cover equals the
product of the per-block sums. -/
lemma IsBlockData.sum_coverSplit {U : Finset (Fin n)} {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData U m ρ)
    {β : Type*} [Fintype β] [DecidableEq β]
    (G : ∀ i : Fin k, ({x // x ∈ (ρ i).1} → β) → ℝ) :
    ∑ g : {x // x ∈ U} → β, ∏ i, G i (hρ.coverSplitEquiv β g i)
    = ∏ i, ∑ h : {x // x ∈ (ρ i).1} → β, G i h := by
  classical
  rw [← Equiv.sum_comp (hρ.coverSplitEquiv β).symm
    (fun g => ∏ i, G i (hρ.coverSplitEquiv β g i))]
  have hsimp : ∀ t : ∀ i : Fin k, ({x // x ∈ (ρ i).1} → β),
      (∏ i, G i (hρ.coverSplitEquiv β ((hρ.coverSplitEquiv β).symm t) i))
      = ∏ i, G i (t i) := by
    intro t
    rw [Equiv.apply_symm_apply]
  rw [Finset.sum_congr rfl (fun t _ => hsimp t)]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

@[simp] lemma IsBlockData.partitionEquiv_apply_val {U : Finset (Fin n)}
    {m : Fin k → ℕ} {ρ : Fin k → Finset (Fin n) × Fin n}
    (hρ : IsBlockData U m ρ) (y : Σ i : Fin k, {x // x ∈ (ρ i).1}) :
    ((hρ.partitionEquiv y : {x // x ∈ U}) : Fin n) = y.2.1 := rfl

@[simp] lemma IsBlockData.coverSplitEquiv_apply {U : Finset (Fin n)}
    {m : Fin k → ℕ} {ρ : Fin k → Finset (Fin n) × Fin n}
    (hρ : IsBlockData U m ρ) {β : Type*} (g : {x // x ∈ U} → β)
    (i : Fin k) (x : {x // x ∈ (ρ i).1}) :
    hρ.coverSplitEquiv β g i x = g (hρ.partitionEquiv ⟨i, x⟩) := rfl

/-- Roots of distinct blocks are distinct. -/
lemma IsBlockData.root_injective {U : Finset (Fin n)} {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData U m ρ)
    {i j : Fin k} (h : (ρ i).2 = (ρ j).2) : i = j := by
  by_contra hne
  have hi := hρ.2.2.1 i
  have hj := hρ.2.2.1 j
  rw [h] at hi
  exact (Finset.disjoint_left.mp (hρ.1 i j hne) hi) hj

variable {U : Finset (Fin n)} {m : Fin k → ℕ}
  {ρ : Fin k → Finset (Fin n) × Fin n}

/-- The increasing enumeration of a block's non-root elements. -/
def IsBlockData.nonRootEmb (hρ : IsBlockData U m ρ) (i : Fin k) :
    Fin (m i) ↪o Fin n :=
  Finset.orderEmbOfFin ((ρ i).1.erase (ρ i).2) (by
    rw [Finset.card_erase_of_mem (hρ.2.2.1 i), hρ.2.2.2 i]
    omega)

lemma IsBlockData.nonRootEmb_mem (hρ : IsBlockData U m ρ) (i : Fin k)
    (j : Fin (m i)) : hρ.nonRootEmb i j ∈ (ρ i).1 :=
  Finset.mem_of_mem_erase (Finset.orderEmbOfFin_mem _ _ _)

lemma IsBlockData.nonRootEmb_ne_root (hρ : IsBlockData U m ρ) (i : Fin k)
    (j : Fin (m i)) : hρ.nonRootEmb i j ≠ (ρ i).2 :=
  (Finset.mem_erase.mp (Finset.orderEmbOfFin_mem _ _ _)).1

/-- **The placement function**: list each block root-first, then its
non-root elements in increasing order twisted by a local permutation. -/
def IsBlockData.placeFun (hρ : IsBlockData U m ρ)
    (π : ∀ i, Equiv.Perm (Fin (m i))) :
    (Σ i : Fin k, Fin (m i + 1)) → Fin n :=
  fun x => Fin.cases ((ρ x.1).2)
    (fun j => hρ.nonRootEmb x.1 ((π x.1) j)) x.2

lemma IsBlockData.placeFun_zero (hρ : IsBlockData U m ρ)
    (π : ∀ i, Equiv.Perm (Fin (m i))) (i : Fin k) :
    hρ.placeFun π ⟨i, 0⟩ = (ρ i).2 := rfl

lemma IsBlockData.placeFun_succ (hρ : IsBlockData U m ρ)
    (π : ∀ i, Equiv.Perm (Fin (m i))) (i : Fin k) (j : Fin (m i)) :
    hρ.placeFun π ⟨i, j.succ⟩ = hρ.nonRootEmb i ((π i) j) := by
  simp [IsBlockData.placeFun]

lemma IsBlockData.placeFun_mem (hρ : IsBlockData U m ρ)
    (π : ∀ i, Equiv.Perm (Fin (m i)))
    (x : Σ i : Fin k, Fin (m i + 1)) :
    hρ.placeFun π x ∈ (ρ x.1).1 := by
  obtain ⟨i, l⟩ := x
  refine Fin.cases ?_ ?_ l
  · rw [hρ.placeFun_zero]
    exact hρ.2.2.1 i
  · intro j
    rw [hρ.placeFun_succ]
    exact hρ.nonRootEmb_mem i _

lemma IsBlockData.placeFun_injective (hρ : IsBlockData U m ρ)
    (π : ∀ i, Equiv.Perm (Fin (m i))) :
    Function.Injective (hρ.placeFun π) := by
  rintro ⟨i, l⟩ ⟨i', l'⟩ h
  have hi : i = i' := by
    by_contra hne
    have h2 := hρ.placeFun_mem π ⟨i', l'⟩
    rw [← h] at h2
    exact (Finset.disjoint_left.mp (hρ.1 i i' hne)
      (hρ.placeFun_mem π ⟨i, l⟩)) h2
  subst hi
  suffices hl : l = l' by rw [hl]
  by_cases hl0 : l = 0 <;> by_cases hl'0 : l' = 0
  · rw [hl0, hl'0]
  · exfalso
    obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hl'0
    rw [hl0, hρ.placeFun_zero, hρ.placeFun_succ] at h
    exact hρ.nonRootEmb_ne_root i _ h.symm
  · exfalso
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hl0
    rw [hl'0, hρ.placeFun_succ, hρ.placeFun_zero] at h
    exact hρ.nonRootEmb_ne_root i _ h
  · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hl0
    obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hl'0
    rw [hρ.placeFun_succ, hρ.placeFun_succ] at h
    have h1 : (π i) j = (π i) j' := (hρ.nonRootEmb i).injective h
    rw [(π i).injective h1]

open Classical in
/-- **THE BLOCK-COUNTING BOUND (†′):** ordered rooted disjoint block data
covering a fixed set `U` with sizes `m i + 1` number at most
`U.card!/∏ (m i)!` — multiplicatively, `card · ∏ (m i)! ≤ U.card!`.
Proof: block data together with local permutations inject into bijections
`(Σ i, Fin (m i + 1)) ≃ U` via the placement function, and there are
exactly `U.card!` such bijections. -/
theorem card_blockData_mul_le (U : Finset (Fin n)) (m : Fin k → ℕ)
    (hsum : ∑ i, (m i + 1) = U.card) :
    ((Finset.univ : Finset (Fin k → Finset (Fin n) × Fin n)).filter
      (fun ρ => IsBlockData U m ρ)).card * ∏ i, (m i).factorial
      ≤ U.card.factorial := by
  classical
  have hcardSig : Fintype.card (Σ i : Fin k, Fin (m i + 1)) = U.card := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact hsum
  have e₀ : (Σ i : Fin k, Fin (m i + 1)) ≃ {x // x ∈ U} :=
    Fintype.equivOfCardEq (by rw [hcardSig, Fintype.card_coe])
  set f : (Fin k → Finset (Fin n) × Fin n) × (∀ i, Equiv.Perm (Fin (m i)))
      → ((Σ i : Fin k, Fin (m i + 1)) ≃ {x // x ∈ U}) :=
    fun pq => if h : IsBlockData U m pq.1
      then Equiv.ofBijective
        (fun x => ⟨h.placeFun pq.2 x,
          h.block_subset x.1 (h.placeFun_mem pq.2 x)⟩)
        ((Fintype.bijective_iff_injective_and_card _).mpr
          ⟨fun x y hxy => h.placeFun_injective pq.2
            (congrArg Subtype.val hxy),
            by rw [hcardSig, Fintype.card_coe]⟩)
      else e₀ with hfdef
  -- blocks are recovered as images of the placement function
  have hblock : ∀ (ρ : Fin k → Finset (Fin n) × Fin n)
      (h : IsBlockData U m ρ) (π : ∀ i, Equiv.Perm (Fin (m i))) (i : Fin k),
      (ρ i).1 = Finset.univ.image
        (fun l : Fin (m i + 1) => h.placeFun π ⟨i, l⟩) := by
    intro ρ h π i
    have hinj : Function.Injective
        (fun l : Fin (m i + 1) => h.placeFun π ⟨i, l⟩) := by
      intro l₁ l₂ hl
      have h2 := h.placeFun_injective π hl
      exact eq_of_heq (Sigma.mk.inj_iff.mp h2).2
    have hsub : Finset.univ.image
        (fun l : Fin (m i + 1) => h.placeFun π ⟨i, l⟩) ⊆ (ρ i).1 := by
      intro v hv
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hv
      exact h.placeFun_mem π ⟨i, l⟩
    have hcard : (ρ i).1.card ≤ (Finset.univ.image
        (fun l : Fin (m i + 1) => h.placeFun π ⟨i, l⟩)).card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
        Fintype.card_fin, h.2.2.2 i]
    exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
  -- the injection on the product set
  have hinjOn : ∀ pq₁ ∈ ((Finset.univ :
      Finset (Fin k → Finset (Fin n) × Fin n)).filter
        (fun ρ => IsBlockData U m ρ)) ×ˢ
      (Finset.univ : Finset (∀ i, Equiv.Perm (Fin (m i)))),
      ∀ pq₂ ∈ ((Finset.univ :
        Finset (Fin k → Finset (Fin n) × Fin n)).filter
          (fun ρ => IsBlockData U m ρ)) ×ˢ
        (Finset.univ : Finset (∀ i, Equiv.Perm (Fin (m i)))),
      f pq₁ = f pq₂ → pq₁ = pq₂ := by
    intro pq₁ h₁ pq₂ h₂ hf
    obtain ⟨ρ₁, π₁⟩ := pq₁
    obtain ⟨ρ₂, π₂⟩ := pq₂
    rw [Finset.mem_product, Finset.mem_filter] at h₁ h₂
    have hb₁ : IsBlockData U m ρ₁ := h₁.1.2
    have hb₂ : IsBlockData U m ρ₂ := h₂.1.2
    rw [hfdef] at hf
    simp only [dif_pos hb₁, dif_pos hb₂] at hf
    have happ : ∀ x, hb₁.placeFun π₁ x = hb₂.placeFun π₂ x := by
      intro x
      simpa using congrArg Subtype.val (DFunLike.congr_fun hf x)
    have hρ : ρ₁ = ρ₂ := by
      funext i
      refine Prod.ext ?_ ?_
      · rw [hblock ρ₁ hb₁ π₁ i, hblock ρ₂ hb₂ π₂ i]
        exact Finset.image_congr (fun l _ => happ ⟨i, l⟩)
      · have h0 := happ ⟨i, 0⟩
        rwa [hb₁.placeFun_zero, hb₂.placeFun_zero] at h0
    subst hρ
    have hπ : π₁ = π₂ := by
      funext i
      refine Equiv.ext fun j => ?_
      have hs := happ ⟨i, j.succ⟩
      rw [hb₁.placeFun_succ, hb₂.placeFun_succ] at hs
      exact (hb₁.nonRootEmb i).injective hs
    rw [hπ]
  -- count
  calc ((Finset.univ : Finset (Fin k → Finset (Fin n) × Fin n)).filter
        (fun ρ => IsBlockData U m ρ)).card * ∏ i, (m i).factorial
      = (((Finset.univ : Finset (Fin k → Finset (Fin n) × Fin n)).filter
          (fun ρ => IsBlockData U m ρ)) ×ˢ
          (Finset.univ : Finset (∀ i, Equiv.Perm (Fin (m i))))).card := by
        rw [Finset.card_product, Finset.card_univ]
        congr 1
        rw [Fintype.card_pi]
        exact (Finset.prod_congr rfl fun i _ => by
          rw [Fintype.card_perm, Fintype.card_fin]).symm
    _ ≤ (Finset.univ :
          Finset ((Σ i : Fin k, Fin (m i + 1)) ≃ {x // x ∈ U})).card :=
        Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _)
          (fun a ha b hb h => hinjOn a (Finset.mem_coe.mp ha) b
            (Finset.mem_coe.mp hb) h)
    _ = U.card.factorial := by
        rw [Finset.card_univ, Fintype.card_equiv e₀, hcardSig]

section MarkedEnum

variable {N : ℕ}

/-- **Marked enumeration** of a finite set with a distinguished element:
position `0` is the mark, positions `1..m` list the remaining elements in
increasing order.  This is the canonical relabeling that sends a shell
subtree's root to `0` — the single-block inverse of `placeFun`. -/
def markedEmb (F : Finset (Fin N)) (s : Fin N) {m : ℕ}
    (hm : (F.erase s).card = m) : Fin (m + 1) → Fin N :=
  fun l => Fin.cases s (fun j => (F.erase s).orderEmbOfFin hm j) l

@[simp] lemma markedEmb_zero (F : Finset (Fin N)) (s : Fin N) {m : ℕ}
    (hm : (F.erase s).card = m) : markedEmb F s hm 0 = s := rfl

@[simp] lemma markedEmb_succ (F : Finset (Fin N)) (s : Fin N) {m : ℕ}
    (hm : (F.erase s).card = m) (j : Fin m) :
    markedEmb F s hm j.succ = (F.erase s).orderEmbOfFin hm j := by
  simp [markedEmb]

lemma markedEmb_mem (F : Finset (Fin N)) {s : Fin N} (hs : s ∈ F) {m : ℕ}
    (hm : (F.erase s).card = m) (l : Fin (m + 1)) :
    markedEmb F s hm l ∈ F := by
  refine Fin.cases ?_ ?_ l
  · rw [markedEmb_zero]
    exact hs
  · intro j
    rw [markedEmb_succ]
    exact Finset.mem_of_mem_erase (Finset.orderEmbOfFin_mem _ _ _)

lemma markedEmb_injective (F : Finset (Fin N)) (s : Fin N) {m : ℕ}
    (hm : (F.erase s).card = m) :
    Function.Injective (markedEmb F s hm) := by
  intro l l' h
  by_cases hl0 : l = 0 <;> by_cases hl'0 : l' = 0
  · rw [hl0, hl'0]
  · exfalso
    obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hl'0
    rw [hl0, markedEmb_zero, markedEmb_succ] at h
    exact (Finset.mem_erase.mp
      (Finset.orderEmbOfFin_mem _ hm j')).1 h.symm
  · exfalso
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hl0
    rw [hl'0, markedEmb_succ, markedEmb_zero] at h
    exact (Finset.mem_erase.mp
      (Finset.orderEmbOfFin_mem _ hm j)).1 h
  · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hl0
    obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hl'0
    rw [markedEmb_succ, markedEmb_succ] at h
    rw [((F.erase s).orderEmbOfFin hm).injective h]

/-- The marked enumeration covers the set exactly. -/
lemma markedEmb_image (F : Finset (Fin N)) {s : Fin N} (hs : s ∈ F)
    {m : ℕ} (hm : (F.erase s).card = m) :
    Finset.univ.image (markedEmb F s hm) = F := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro v hv
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hv
    exact markedEmb_mem F hs hm l
  · rw [Finset.card_image_of_injective _ (markedEmb_injective F s hm),
      Finset.card_univ, Fintype.card_fin]
    have := Finset.card_erase_of_mem hs
    omega

/-- The marked enumeration as an equivalence onto the set. -/
noncomputable def markedEquiv (F : Finset (Fin N)) {s : Fin N}
    (hs : s ∈ F) {m : ℕ} (hm : (F.erase s).card = m) :
    Fin (m + 1) ≃ {x // x ∈ F} := by
  refine Equiv.ofBijective
    (fun l => ⟨markedEmb F s hm l, markedEmb_mem F hs hm l⟩) ?_
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · intro l l' h
    exact markedEmb_injective F s hm (congrArg Subtype.val h)
  · have h1 : Fintype.card {x // x ∈ F} = F.card := Fintype.card_coe F
    have h2 := Finset.card_erase_of_mem hs
    have h3 := Finset.card_pos.mpr ⟨s, hs⟩
    rw [Fintype.card_fin, h1]
    omega

@[simp] lemma markedEquiv_apply_val (F : Finset (Fin N)) {s : Fin N}
    (hs : s ∈ F) {m : ℕ} (hm : (F.erase s).card = m) (l : Fin (m + 1)) :
    (markedEquiv F hs hm l).1 = markedEmb F s hm l := rfl

@[simp] lemma markedEquiv_zero_val (F : Finset (Fin N)) {s : Fin N}
    (hs : s ∈ F) {m : ℕ} (hm : (F.erase s).card = m) :
    (markedEquiv F hs hm 0).1 = s := rfl

end MarkedEnum

section SubtreeTransport

variable {n D : ℕ} {p : Fin (n + 1) → Fin (n + 1)}
  {lev : Fin (n + 1) → Fin (D + 2)}

/-- The shell fiber of a level-1 vertex. -/
def shellFiber (p : Fin (n + 1) → Fin (n + 1))
    (lev : Fin (n + 1) → Fin (D + 2)) (s : Fin (n + 1)) :
    Finset (Fin (n + 1)) := by
  classical
  exact (Finset.univ : Finset (Fin (n + 1))).filter
    (fun v => v ≠ 0 ∧ shellRoot p lev v = s)

open Classical in
lemma mem_shellFiber {v s : Fin (n + 1)} :
    v ∈ shellFiber p lev s ↔ v ≠ 0 ∧ shellRoot p lev v = s := by
  classical
  unfold shellFiber
  rw [Finset.mem_filter]
  simp

lemma self_mem_shellFiber (hs : s ≠ 0) (hs1 : (lev s : ℕ) = 1) :
    s ∈ shellFiber p lev s := by
  classical
  unfold shellFiber
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hs, shellRoot_eq_self hs1⟩

/-- Fiber members other than the shell root sit at level ≥ 2, and their
parents stay in the fiber. -/
lemma shellFiber_parent_mem (h : IsAdmissible p lev) {s v : Fin (n + 1)}
    (hv : v ∈ shellFiber p lev s) (hvs : v ≠ s) :
    2 ≤ (lev v : ℕ) ∧ p v ≠ 0 ∧ p v ∈ shellFiber p lev s := by
  classical
  unfold shellFiber at hv ⊢
  rw [Finset.mem_filter] at hv
  obtain ⟨-, hv0, hvroot⟩ := hv
  have hlev2 : 2 ≤ (lev v : ℕ) := by
    have h1 := h.one_le_lev hv0
    rcases Nat.lt_or_ge (lev v : ℕ) 2 with h2 | h2
    · exfalso
      have hv1 : (lev v : ℕ) = 1 := by omega
      exact hvs (hvroot ▸ (shellRoot_eq_self hv1).symm)
    · exact h2
  have hstep := h.2 v hv0
  have hp0 : p v ≠ 0 := by
    intro hzero
    have : (lev (p v) : ℕ) = 0 := by
      rw [hzero]
      exact congrArg Fin.val h.1
    omega
  refine ⟨hlev2, hp0, ?_⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hp0,
    by rw [h.shellRoot_parent hv0 hlev2]; exact hvroot⟩

variable (h : IsAdmissible p lev) {s : Fin (n + 1)}
  (hs : s ≠ 0) (hs1 : (lev s : ℕ) = 1) {m : ℕ}
  (hm : ((shellFiber p lev s).erase s).card = m)

/-- **The relabeled subtree parent map** on `Fin (m+1)`: position `0` is
the shell root (a fixed point); other positions follow `p` through the
marked enumeration. -/
noncomputable def subtreeParent : Fin (m + 1) → Fin (m + 1) :=
  fun l => if hl : l = 0 then 0
    else (markedEquiv (shellFiber p lev s)
      (self_mem_shellFiber hs hs1) hm).symm
      ⟨p ((markedEquiv (shellFiber p lev s)
          (self_mem_shellFiber hs hs1) hm l).1),
        (shellFiber_parent_mem h
          ((markedEquiv (shellFiber p lev s)
            (self_mem_shellFiber hs hs1) hm l).2)
          (fun hEq => hl (((markedEquiv (shellFiber p lev s)
            (self_mem_shellFiber hs hs1) hm).injective
            (Subtype.ext (hEq.trans
              (markedEquiv_zero_val _ _ _).symm)))))).2.2⟩

/-- **The relabeled subtree levels**: shifted down by one. -/
noncomputable def subtreeLev : Fin (m + 1) → Fin (D + 1) :=
  fun l => ⟨(lev ((markedEquiv (shellFiber p lev s)
      (self_mem_shellFiber hs hs1) hm l).1) : ℕ) - 1, by
    have := (lev ((markedEquiv (shellFiber p lev s)
      (self_mem_shellFiber hs hs1) hm l).1)).isLt
    omega⟩

/-- **The subtree structure is admissible at depth `D`.** -/
theorem subtreeStructure_isAdmissible :
    IsAdmissible (subtreeParent h hs hs1 hm) (subtreeLev hs hs1 hm) := by
  classical
  constructor
  · -- root level
    apply Fin.ext
    have hval : ((subtreeLev hs hs1 hm 0 : Fin (D + 1)) : ℕ)
        = (lev ((markedEquiv (shellFiber p lev s)
            (self_mem_shellFiber hs hs1) hm 0).1) : ℕ) - 1 := rfl
    rw [hval, markedEquiv_zero_val]
    simp [hs1]
  · -- exact increments
    intro l hl
    set e := markedEquiv (shellFiber p lev s)
      (self_mem_shellFiber hs hs1) hm with hedef
    set v : Fin (n + 1) := (e l).1 with hvdef
    have hvF : v ∈ shellFiber p lev s := (e l).2
    have hvs : v ≠ s := by
      intro hEq
      exact hl (e.injective (Subtype.ext
        (hEq.trans (markedEquiv_zero_val _ _ _).symm)))
    obtain ⟨hlev2, hp0, hpF⟩ := shellFiber_parent_mem h hvF hvs
    have hv0 : v ≠ 0 := by
      classical
      unfold shellFiber at hvF
      rw [Finset.mem_filter] at hvF
      exact hvF.2.1
    have hstep := h.2 v hv0
    -- unfold the parent at l ≠ 0, in `v`-vocabulary
    show ((subtreeLev hs hs1 hm) ((subtreeParent h hs hs1 hm) l) : ℕ) + 1
      = ((subtreeLev hs hs1 hm) l : ℕ)
    have hval1 : ((subtreeLev hs hs1 hm) l : ℕ) = (lev v : ℕ) - 1 := rfl
    have hval2 : ((subtreeLev hs hs1 hm) ((subtreeParent h hs hs1 hm) l) : ℕ)
        = (lev (p v) : ℕ) - 1 := by
      unfold subtreeParent subtreeLev
      rw [dif_neg hl]
      simp only [Equiv.apply_symm_apply]
      rfl
    rw [hval1, hval2]
    omega

/-- **Parent conjugation:** through the marked enumeration, the relabeled
parent map is exactly the original parent map (away from the root). -/
lemma subtreeParent_apply_val {l : Fin (m + 1)} (hl : l ≠ 0) :
    ((markedEquiv (shellFiber p lev s) (self_mem_shellFiber hs hs1) hm)
      (subtreeParent h hs hs1 hm l)).1
    = p ((markedEquiv (shellFiber p lev s)
        (self_mem_shellFiber hs hs1) hm l).1) := by
  unfold subtreeParent
  rw [dif_neg hl, Equiv.apply_symm_apply]

/-- Reindexing a product over nonzero positions by `Fin.succ`. -/
lemma prod_filter_ne_zero_eq {M : Type*} [CommMonoid M] {m : ℕ}
    (g : Fin (m + 1) → M) :
    ∏ l ∈ (Finset.univ : Finset (Fin (m + 1))).filter (fun l => l ≠ 0),
      g l = ∏ j : Fin m, g j.succ := by
  refine (Finset.prod_nbij (fun j => j.succ) ?_ ?_ ?_ ?_).symm
  · intro j _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Fin.succ_ne_zero j⟩
  · intro j₁ _ j₂ _ h
    exact Fin.succ_injective _ h
  · intro l hl
    rw [Finset.mem_coe, Finset.mem_filter] at hl
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hl.2
    exact ⟨j, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
  · intro j _
    rfl

/-- **The per-fiber product transport:** a product of per-vertex factors
over a shell subtree (minus its root) equals the product over nonzero
relabeled positions. -/
lemma subtree_prod_transport {M : Type*} [CommMonoid M]
    (G : Fin (n + 1) → M) :
    ∏ v ∈ (shellFiber p lev s).erase s, G v
    = ∏ l ∈ (Finset.univ : Finset (Fin (m + 1))).filter (fun l => l ≠ 0),
        G ((markedEquiv (shellFiber p lev s)
          (self_mem_shellFiber hs hs1) hm l).1) := by
  rw [prod_filter_ne_zero_eq]
  refine (Finset.prod_nbij
    (fun j => ((shellFiber p lev s).erase s).orderEmbOfFin hm j)
    ?_ ?_ ?_ ?_).symm
  · intro j _
    exact Finset.orderEmbOfFin_mem _ hm j
  · intro j₁ _ j₂ _ hj
    exact (((shellFiber p lev s).erase s).orderEmbOfFin hm).injective hj
  · intro v hv
    rw [Finset.mem_coe] at hv
    have : v ∈ Set.range (((shellFiber p lev s).erase s).orderEmbOfFin hm) := by
      rw [Finset.range_orderEmbOfFin]
      exact hv
    obtain ⟨j, hj⟩ := this
    exact ⟨j, Finset.mem_coe.mpr (Finset.mem_univ _), hj⟩
  · intro j _
    rw [markedEquiv_apply_val, markedEmb_succ]

/-- **Location:** every non-root vertex lies in the fiber of its shell
root. -/
lemma mem_shellFiber_shellRoot {v : Fin (n + 1)} (hv : v ≠ 0) :
    v ∈ shellFiber p lev (shellRoot p lev v) :=
  mem_shellFiber.mpr ⟨hv, rfl⟩

/-- **Recovery of `p` at shell roots:** within a fiber, the parent of the
root is `0`. -/
lemma parent_recovery_root (h' : IsAdmissible p lev) (hs' : s ≠ 0)
    (hs1' : (lev s : ℕ) = 1) :
    p s = 0 := (h'.parent_eq_zero_iff hs').mpr hs1'

/-- **Recovery of `p` away from roots:** the original parent map is read
back from the subtree structure through the marked enumeration.  This is
the reconstruction equation making the shell decomposition injective. -/
lemma parent_recovery {v : Fin (n + 1)} (hv : v ∈ shellFiber p lev s)
    (hvs : v ≠ s) :
    p v = markedEmb (shellFiber p lev s) s hm
      (subtreeParent h hs hs1 hm
        ((markedEquiv (shellFiber p lev s)
          (self_mem_shellFiber hs hs1) hm).symm ⟨v, hv⟩)) := by
  set e := markedEquiv (shellFiber p lev s)
    (self_mem_shellFiber hs hs1) hm with hedef
  set l : Fin (m + 1) := e.symm ⟨v, hv⟩ with hldef
  have hl0 : l ≠ 0 := by
    intro hEq
    have : e l = e 0 := by rw [hEq]
    rw [hldef, Equiv.apply_symm_apply] at this
    have hval := congrArg Subtype.val this
    rw [markedEquiv_zero_val] at hval
    exact hvs hval
  have hkey := subtreeParent_apply_val h hs hs1 hm hl0
  have hev : (e l).1 = v := by
    rw [hldef, Equiv.apply_symm_apply]
  rw [hev] at hkey
  rw [← hkey, markedEquiv_apply_val]

/-- **Recovery of `lev`:** original levels are the subtree levels plus
one. -/
lemma lev_recovery (h' : IsAdmissible p lev) {v : Fin (n + 1)}
    (hv : v ∈ shellFiber p lev s) :
    (lev v : ℕ)
    = ((subtreeLev hs hs1 hm
        ((markedEquiv (shellFiber p lev s)
          (self_mem_shellFiber hs hs1) hm).symm ⟨v, hv⟩)) : ℕ) + 1 := by
  have hv0 : v ≠ 0 := (mem_shellFiber.mp hv).1
  have hge := h'.one_le_lev hv0
  have hval : ((subtreeLev hs hs1 hm
      ((markedEquiv (shellFiber p lev s)
        (self_mem_shellFiber hs hs1) hm).symm ⟨v, hv⟩)) : ℕ)
      = (lev ((markedEquiv (shellFiber p lev s)
          (self_mem_shellFiber hs hs1) hm
          ((markedEquiv (shellFiber p lev s)
            (self_mem_shellFiber hs hs1) hm).symm ⟨v, hv⟩)).1) : ℕ) - 1 :=
    rfl
  rw [hval, Equiv.apply_symm_apply]
  show (lev v : ℕ) = ((lev v : ℕ) - 1) + 1
  omega

end SubtreeTransport

section MasterAssembly

variable {n D : ℕ} {p : Fin (n + 1) → Fin (n + 1)}
  {lev : Fin (n + 1) → Fin (D + 2)}

open Classical in
/-- **Master factorization, stage 1:** the edge-factor product of an
admissible structure splits over the first shell — one root-edge factor
`G 0 s` per shell element, times the subtree products.  Pure partition
plus root-edge extraction; the relabeling happens per subtree via
`subtree_prod_transport`. -/
lemma master_partition (h : IsAdmissible p lev) {M : Type*} [CommMonoid M]
    (G : Fin (n + 1) → Fin (n + 1) → M) :
    ∏ v ∈ (Finset.univ : Finset (Fin (n + 1))).filter (fun v => v ≠ 0),
      G (p v) v
    = ∏ s ∈ (Finset.univ : Finset (Fin (n + 1))).filter
        (fun s => s ≠ 0 ∧ p s = 0),
        (G 0 s * ∏ v ∈ (shellFiber p lev s).erase s, G (p v) v) := by
  classical
  have hpart := shell_fiber_partition h
  calc ∏ v ∈ (Finset.univ : Finset (Fin (n + 1))).filter (fun v => v ≠ 0),
        G (p v) v
      = ∏ v ∈ ((Finset.univ : Finset (Fin (n + 1))).filter
          (fun s => s ≠ 0 ∧ p s = 0)).biUnion
          (fun s => (Finset.univ : Finset (Fin (n + 1))).filter
            (fun v => v ≠ 0 ∧ shellRoot p lev v = s)),
          G (p v) v := by rw [← hpart]
    _ = ∏ s ∈ (Finset.univ : Finset (Fin (n + 1))).filter
          (fun s => s ≠ 0 ∧ p s = 0),
          ∏ v ∈ (Finset.univ : Finset (Fin (n + 1))).filter
            (fun v => v ≠ 0 ∧ shellRoot p lev v = s),
            G (p v) v :=
        Finset.prod_biUnion (fun a _ b _ hab => shell_fiber_disjoint hab)
    _ = ∏ s ∈ (Finset.univ : Finset (Fin (n + 1))).filter
          (fun s => s ≠ 0 ∧ p s = 0),
          (G 0 s * ∏ v ∈ (shellFiber p lev s).erase s, G (p v) v) := by
        refine Finset.prod_congr rfl fun s hs => ?_
        rw [Finset.mem_filter] at hs
        obtain ⟨-, hs0, hps⟩ := hs
        have hs1 : (lev s : ℕ) = 1 := (h.parent_eq_zero_iff hs0).mp hps
        have hsF : s ∈ shellFiber p lev s := self_mem_shellFiber hs0 hs1
        have hFib : (Finset.univ : Finset (Fin (n + 1))).filter
            (fun v => v ≠ 0 ∧ shellRoot p lev v = s)
            = shellFiber p lev s := rfl
        rw [hFib, ← Finset.mul_prod_erase _ _ hsF, hps]

open Classical in
/-- **The shell forms block data over the non-root vertices:** for any
enumeration `σ` of the first shell, the shell fibers with their roots are
ordered rooted disjoint block data covering `univ.erase 0` — the bridge
from admissible structures to the counting lemma. -/
lemma shell_blockData (h : IsAdmissible p lev) {k : ℕ}
    (σ : Fin k ≃ {s : Fin (n + 1) //
      s ∈ (Finset.univ : Finset (Fin (n + 1))).filter
        (fun s => s ≠ 0 ∧ p s = 0)}) :
    IsBlockData ((Finset.univ : Finset (Fin (n + 1))).erase 0)
      (fun i => ((shellFiber p lev (σ i).1).erase (σ i).1).card)
      (fun i => (shellFiber p lev (σ i).1, (σ i).1)) := by
  classical
  have hshell : ∀ i : Fin k, (σ i).1 ≠ 0 ∧ p (σ i).1 = 0 :=
    fun i => (Finset.mem_filter.mp (σ i).2).2
  have hlev1 : ∀ i : Fin k, ((lev (σ i).1 : ℕ)) = 1 :=
    fun i => (h.parent_eq_zero_iff (hshell i).1).mp (hshell i).2
  have hroot : ∀ i : Fin k, (σ i).1 ∈ shellFiber p lev (σ i).1 :=
    fun i => self_mem_shellFiber (hshell i).1 (hlev1 i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- disjoint
    intro i j hij
    refine shell_fiber_disjoint ?_
    intro hEq
    exact hij (σ.injective (Subtype.ext hEq))
  · -- cover: the fibers exhaust the non-root vertices
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro ⟨i, hv⟩
      exact ⟨(mem_shellFiber.mp hv).1, trivial⟩
    · rintro ⟨hv0, -⟩
      have hsr0 : shellRoot p lev v ≠ 0 := h.shellRoot_ne_zero hv0
      have hsrp : p (shellRoot p lev v) = 0 := h.parent_shellRoot hv0
      have hmem : shellRoot p lev v ∈ (Finset.univ :
          Finset (Fin (n + 1))).filter (fun s => s ≠ 0 ∧ p s = 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsr0, hsrp⟩
      refine ⟨σ.symm ⟨shellRoot p lev v, hmem⟩, ?_⟩
      rw [mem_shellFiber]
      refine ⟨hv0, ?_⟩
      have := σ.apply_symm_apply ⟨shellRoot p lev v, hmem⟩
      rw [this]
  · -- roots
    exact hroot
  · -- cards
    intro i
    have h1 := Finset.card_erase_of_mem (hroot i)
    have hpos := Finset.card_pos.mpr ⟨(σ i).1, hroot i⟩
    dsimp only
    omega

open Classical in
/-- **Symmetrization (assembly step 2):** summing over structures equals
summing over (structure, shell-enumeration) pairs weighted by `1/k!` —
each structure has exactly `k!` enumerations of its first shell.  The
`1/k!` of the exponential series enters the recursion exactly here. -/
lemma sum_symmetrize {α : Type*} [DecidableEq α] (A : Finset α)
    (F : α → ℝ) (S : α → Finset (Fin (n + 1))) :
    ∑ pl ∈ A, F pl
    = ∑ x ∈ A.sigma (fun pl => (Finset.univ :
        Finset (Fin (S pl).card ≃ {s // s ∈ S pl}))),
      (((S x.1).card.factorial : ℝ))⁻¹ * F x.1 := by
  classical
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun pl _ => ?_
  dsimp only
  rw [Finset.sum_const, Finset.card_univ]
  have e : Fin (S pl).card ≃ {s // s ∈ S pl} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe])).symm
  have hcard : Fintype.card (Fin (S pl).card ≃ {s // s ∈ S pl})
      = (S pl).card.factorial := by
    rw [Fintype.card_equiv e, Fintype.card_fin]
  rw [hcard, nsmul_eq_mul]
  have hne : (((S pl).card.factorial : ℝ)) ≠ 0 := by positivity
  field_simp

open Classical in
/-- **The shell forms block data — cast-free enumeration form:** same as
`shell_blockData`, with the enumeration given as an injective function
with prescribed range (the form the function-version symmetrization
produces). -/
lemma shell_blockData_fn (h : IsAdmissible p lev) {k : ℕ}
    {σ : Fin k → Fin (n + 1)} (hσinj : Function.Injective σ)
    (hσrange : Finset.univ.image σ
      = (Finset.univ : Finset (Fin (n + 1))).filter
          (fun s => s ≠ 0 ∧ p s = 0)) :
    IsBlockData ((Finset.univ : Finset (Fin (n + 1))).erase 0)
      (fun i => ((shellFiber p lev (σ i)).erase (σ i)).card)
      (fun i => (shellFiber p lev (σ i), σ i)) := by
  classical
  have hmem : ∀ i : Fin k, σ i ∈ (Finset.univ :
      Finset (Fin (n + 1))).filter (fun s => s ≠ 0 ∧ p s = 0) := by
    intro i
    rw [← hσrange]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hshell : ∀ i : Fin k, σ i ≠ 0 ∧ p (σ i) = 0 :=
    fun i => (Finset.mem_filter.mp (hmem i)).2
  have hlev1 : ∀ i : Fin k, ((lev (σ i) : ℕ)) = 1 :=
    fun i => (h.parent_eq_zero_iff (hshell i).1).mp (hshell i).2
  have hroot : ∀ i : Fin k, σ i ∈ shellFiber p lev (σ i) :=
    fun i => self_mem_shellFiber (hshell i).1 (hlev1 i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    refine shell_fiber_disjoint ?_
    intro hEq
    exact hij (hσinj hEq)
  · ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro ⟨i, hv⟩
      exact ⟨(mem_shellFiber.mp hv).1, trivial⟩
    · rintro ⟨hv0, -⟩
      have hsr0 : shellRoot p lev v ≠ 0 := h.shellRoot_ne_zero hv0
      have hsrp : p (shellRoot p lev v) = 0 := h.parent_shellRoot hv0
      have hmem2 : shellRoot p lev v ∈ Finset.univ.image σ := by
        rw [hσrange]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsr0, hsrp⟩
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem2
      refine ⟨i, ?_⟩
      rw [mem_shellFiber]
      exact ⟨hv0, hi.symm⟩
  · exact hroot
  · intro i
    have h1 := Finset.card_erase_of_mem (hroot i)
    have hpos := Finset.card_pos.mpr ⟨σ i, hroot i⟩
    dsimp only
    omega

open Classical in
/-- **The inner assignment sum** of `treeSumRaw` at a fixed parent map:
the object the shell recursion factorizes. -/
noncomputable def treeSumRawInner (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) {m : ℕ} (q : Fin (m + 1) → Fin (m + 1)) : ℝ :=
  ∑ X ∈ (Finset.univ : Finset (Fin (m + 1) → P.Polymer)).filter
    (fun X => X 0 = c),
    ∏ l ∈ Finset.univ.filter (fun l : Fin (m + 1) => l ≠ 0),
      (if P.incomp (X (q l)) (X l) then (1 : ℝ) else 0)
        * ‖P.activity (X l)‖

open Classical in
/-- `treeSumRaw` is the sum of the inner assignment sums over admissible
canonical structures. -/
lemma treeSumRaw_eq_sum_inner (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) (D n : ℕ) :
    treeSumRaw P c D n
    = ∑ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
        × (Fin (n + 1) → Fin (D + 1)))).filter
        (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0),
      treeSumRawInner P c pl.1 := by
  unfold treeSumRaw treeSumRawInner
  rfl

open Classical in
lemma treeSumRawInner_nonneg (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) {m : ℕ} (q : Fin (m + 1) → Fin (m + 1)) :
    0 ≤ treeSumRawInner P c q := by
  unfold treeSumRawInner
  refine Finset.sum_nonneg fun X _ =>
    Finset.prod_nonneg fun l _ => mul_nonneg ?_ (norm_nonneg _)
  split_ifs <;> norm_num

open Classical in
/-- **Pinned sums are free sums over the non-root coordinates:** summing
over functions with prescribed value at `0` equals summing over their
restrictions away from `0`. -/
lemma sum_pinned_eq {β : Type*} [Fintype β] [DecidableEq β] {N : ℕ}
    (c : β) (F : (Fin (N + 1) → β) → ℝ) :
    ∑ X ∈ (Finset.univ : Finset (Fin (N + 1) → β)).filter
      (fun X => X 0 = c), F X
    = ∑ g : {v : Fin (N + 1) // v ≠ 0} → β,
        F (fun v => if h : v = 0 then c else g ⟨v, h⟩) := by
  classical
  refine Finset.sum_nbij' (i := fun X => fun v => X v.1)
    (j := fun g => fun v => if h : v = 0 then c else g ⟨v, h⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro X _
    exact Finset.mem_univ _
  · intro g _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, dif_pos rfl⟩
  · intro X hX
    rw [Finset.mem_filter] at hX
    funext v
    dsimp only
    by_cases hv : v = 0
    · rw [dif_pos hv, hv, hX.2]
    · rw [dif_neg hv]
  · intro g _
    funext v
    dsimp only
    rw [dif_neg v.2]
  · intro X hX
    rw [Finset.mem_filter] at hX
    congr 1
    funext v
    dsimp only
    by_cases hv : v = 0
    · rw [dif_pos hv, hv, hX.2]
    · rw [dif_neg hv]

open Classical in
/-- **The fully factored edge product (the per-ρ inequality's term side):**
for an admissible structure with enumerated shell, the edge-factor product
splits into per-block factors — root edge at `σ i`, then the relabeled
subtree product through the marked enumeration.  Composition of
`master_partition`, the image reindex, `subtree_prod_transport`, and the
parent conjugation. -/
lemma master_factorization_fn {n D : ℕ} {p : Fin (n + 1) → Fin (n + 1)}
    {lev : Fin (n + 1) → Fin (D + 2)} (h : IsAdmissible p lev) {k : ℕ}
    {σ : Fin k → Fin (n + 1)} (hσinj : Function.Injective σ)
    (hσrange : Finset.univ.image σ
      = (Finset.univ : Finset (Fin (n + 1))).filter
          (fun s => s ≠ 0 ∧ p s = 0))
    {M : Type*} [CommMonoid M] (G : Fin (n + 1) → Fin (n + 1) → M)
    (hs : ∀ i, σ i ≠ 0) (hs1 : ∀ i, ((lev (σ i) : ℕ)) = 1) :
    ∏ v ∈ (Finset.univ : Finset (Fin (n + 1))).filter (fun v => v ≠ 0),
      G (p v) v
    = ∏ i : Fin k,
        (G 0 (σ i) * ∏ l ∈ (Finset.univ :
          Finset (Fin (((shellFiber p lev (σ i)).erase (σ i)).card + 1))).filter
            (fun l => l ≠ 0),
          G (markedEmb (shellFiber p lev (σ i)) (σ i) rfl
              (subtreeParent h (hs i) (hs1 i) rfl l))
            (markedEmb (shellFiber p lev (σ i)) (σ i) rfl l)) := by
  classical
  rw [master_partition h G, ← hσrange]
  rw [Finset.prod_image (fun i _ j _ hij => hσinj hij)]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  rw [subtree_prod_transport (hs i) (hs1 i) rfl
    (fun v => G (p v) v)]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Finset.mem_filter] at hl
  have hkey := subtreeParent_apply_val h (hs i) (hs1 i) rfl hl.2
  rw [markedEquiv_apply_val] at hkey
  rw [← hkey, markedEquiv_apply_val]

open Classical in
/-- **Enumerations of a `k`-set number `k!`:** injective functions
`Fin k → α` with image exactly `S` (where `S.card = k`) are in bijection
with `Fin k ≃ S`.  This is the cast-free form of shell-enumeration
counting: the `σ`-functions have a type independent of the structure
being enumerated. -/
lemma card_enumerations {α : Type*} [DecidableEq α] [Fintype α]
    {S : Finset α} {k : ℕ} (hk : S.card = k) :
    ((Finset.univ : Finset (Fin k → α)).filter
      (fun σ => Function.Injective σ ∧ Finset.univ.image σ = S)).card
    = k.factorial := by
  classical
  have hcardS : Fintype.card {x // x ∈ S} = k := by
    rw [Fintype.card_coe, hk]
  have e : {σ : Fin k → α //
      Function.Injective σ ∧ Finset.univ.image σ = S}
      ≃ (Fin k ≃ {x // x ∈ S}) := by
    refine
      { toFun := fun σ => Equiv.ofBijective
          (fun i => ⟨σ.1 i, by
            have hmem : σ.1 i ∈ Finset.univ.image σ.1 :=
              Finset.mem_image_of_mem _ (Finset.mem_univ i)
            rw [σ.2.2] at hmem
            exact hmem⟩)
          ((Fintype.bijective_iff_injective_and_card _).mpr
            ⟨fun i j hij => σ.2.1 (congrArg Subtype.val hij),
              by rw [hcardS, Fintype.card_fin]⟩)
        invFun := fun e => ⟨fun i => (e i).1, ?_, ?_⟩
        left_inv := fun σ => Subtype.ext (funext fun i => rfl)
        right_inv := fun e => Equiv.ext fun i => Subtype.ext rfl }
    · intro i j hij
      exact e.injective (Subtype.ext hij)
    · refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro v hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        exact (e i).2
      · rw [Finset.card_image_of_injective _
          (fun i j hij => e.injective (Subtype.ext hij)),
          Finset.card_univ, Fintype.card_fin, hk]
  calc ((Finset.univ : Finset (Fin k → α)).filter
        (fun σ => Function.Injective σ ∧ Finset.univ.image σ = S)).card
      = Fintype.card {σ : Fin k → α //
          Function.Injective σ ∧ Finset.univ.image σ = S} :=
        (Fintype.card_subtype _).symm
    _ = Fintype.card (Fin k ≃ {x // x ∈ S}) := Fintype.card_congr e
    _ = k.factorial := by
        have e₀ : Fin k ≃ {x // x ∈ S} :=
          (Fintype.equivFinOfCardEq hcardS).symm
        rw [Fintype.card_equiv e₀, Fintype.card_fin]

open Classical in
/-- **The block-local sum identification (assembly step S3):** the sum over
assignments of a single rooted block — root factor times relabeled subtree
product — equals `∑_{c'} 𝟙[incomp c c']·‖z(c')‖·treeSumRawInner`.
Reindex along the marked enumeration, then split at the root value. -/
lemma block_sum_eq (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) {N m : ℕ} {V : Finset (Fin N)} {s : Fin N}
    (hsV : s ∈ V) (hm : (V.erase s).card = m)
    (q : Fin (m + 1) → Fin (m + 1)) :
    ∑ h : {x // x ∈ V} → P.Polymer,
      (((if P.incomp c (h ⟨markedEmb V s hm 0, markedEmb_mem V hsV hm 0⟩)
          then (1 : ℝ) else 0)
        * ‖P.activity (h ⟨markedEmb V s hm 0, markedEmb_mem V hsV hm 0⟩)‖)
      * ∏ l ∈ Finset.univ.filter (fun l : Fin (m + 1) => l ≠ 0),
          (if P.incomp (h ⟨markedEmb V s hm (q l), markedEmb_mem V hsV hm (q l)⟩)
              (h ⟨markedEmb V s hm l, markedEmb_mem V hsV hm l⟩)
            then (1 : ℝ) else 0)
            * ‖P.activity (h ⟨markedEmb V s hm l, markedEmb_mem V hsV hm l⟩)‖)
    = ∑ c' : P.Polymer, (if P.incomp c c' then (1 : ℝ) else 0)
        * ‖P.activity c'‖ * treeSumRawInner P c' q := by
  classical
  -- reindex along the marked enumeration
  have hreindex : ∀ (Y : Fin (m + 1) → P.Polymer) (l : Fin (m + 1)),
      (Y ∘ (markedEquiv V hsV hm).symm)
        ⟨markedEmb V s hm l, markedEmb_mem V hsV hm l⟩ = Y l := by
    intro Y l
    have : (⟨markedEmb V s hm l, markedEmb_mem V hsV hm l⟩ :
        {x // x ∈ V}) = markedEquiv V hsV hm l :=
      Subtype.ext (markedEquiv_apply_val V hsV hm l).symm
    rw [Function.comp_apply, this, Equiv.symm_apply_apply]
  rw [← Equiv.sum_comp (Equiv.arrowCongr (markedEquiv V hsV hm)
    (Equiv.refl P.Polymer))]
  have hcongr : ∀ Y : Fin (m + 1) → P.Polymer,
      ((((if P.incomp c (((Equiv.arrowCongr (markedEquiv V hsV hm)
          (Equiv.refl P.Polymer)) Y)
            ⟨markedEmb V s hm 0, markedEmb_mem V hsV hm 0⟩)
          then (1 : ℝ) else 0)
        * ‖P.activity (((Equiv.arrowCongr (markedEquiv V hsV hm)
            (Equiv.refl P.Polymer)) Y)
            ⟨markedEmb V s hm 0, markedEmb_mem V hsV hm 0⟩)‖)
      * ∏ l ∈ Finset.univ.filter (fun l : Fin (m + 1) => l ≠ 0),
          (if P.incomp (((Equiv.arrowCongr (markedEquiv V hsV hm)
              (Equiv.refl P.Polymer)) Y)
              ⟨markedEmb V s hm (q l), markedEmb_mem V hsV hm (q l)⟩)
              (((Equiv.arrowCongr (markedEquiv V hsV hm)
                (Equiv.refl P.Polymer)) Y)
                ⟨markedEmb V s hm l, markedEmb_mem V hsV hm l⟩)
            then (1 : ℝ) else 0)
            * ‖P.activity (((Equiv.arrowCongr (markedEquiv V hsV hm)
                (Equiv.refl P.Polymer)) Y)
                ⟨markedEmb V s hm l, markedEmb_mem V hsV hm l⟩)‖))
      = (((if P.incomp c (Y 0) then (1 : ℝ) else 0) * ‖P.activity (Y 0)‖)
        * ∏ l ∈ Finset.univ.filter (fun l : Fin (m + 1) => l ≠ 0),
            (if P.incomp (Y (q l)) (Y l) then (1 : ℝ) else 0)
              * ‖P.activity (Y l)‖) := by
    intro Y
    have happ : ∀ l : Fin (m + 1),
        ((Equiv.arrowCongr (markedEquiv V hsV hm)
          (Equiv.refl P.Polymer)) Y)
          ⟨markedEmb V s hm l, markedEmb_mem V hsV hm l⟩ = Y l := by
      intro l
      exact hreindex Y l
    rw [happ 0]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [happ l, happ (q l)]
  rw [Finset.sum_congr rfl (fun Y _ => hcongr Y)]
  -- split at the root value
  have hmaps : ∀ Y ∈ (Finset.univ : Finset (Fin (m + 1) → P.Polymer)),
      Y 0 ∈ (Finset.univ : Finset P.Polymer) := fun Y _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun c' _ => ?_
  have hterm : ∀ Y ∈ (Finset.univ :
      Finset (Fin (m + 1) → P.Polymer)).filter (fun Y => Y 0 = c'),
      (((if P.incomp c (Y 0) then (1 : ℝ) else 0) * ‖P.activity (Y 0)‖)
        * ∏ l ∈ Finset.univ.filter (fun l : Fin (m + 1) => l ≠ 0),
            (if P.incomp (Y (q l)) (Y l) then (1 : ℝ) else 0)
              * ‖P.activity (Y l)‖)
      = (((if P.incomp c c' then (1 : ℝ) else 0) * ‖P.activity c'‖)
        * ∏ l ∈ Finset.univ.filter (fun l : Fin (m + 1) => l ≠ 0),
            (if P.incomp (Y (q l)) (Y l) then (1 : ℝ) else 0)
              * ‖P.activity (Y l)‖) := by
    intro Y hY
    rw [(Finset.mem_filter.mp hY).2]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  unfold treeSumRawInner
  ring

open Classical in
/-- **The block functional** (top-level, per the §5d prescription): the
integrand of `block_sum_eq` as a named function — root factor times
relabeled subtree product, reading an assignment of one rooted block. -/
noncomputable def blockFunctional (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) {N m : ℕ} (V : Finset (Fin N)) (s : Fin N)
    (hsV : s ∈ V) (hm : (V.erase s).card = m)
    (q : Fin (m + 1) → Fin (m + 1))
    (hfun : {x // x ∈ V} → P.Polymer) : ℝ :=
  (((if P.incomp c (hfun ⟨markedEmb V s hm 0, markedEmb_mem V hsV hm 0⟩)
      then (1 : ℝ) else 0)
    * ‖P.activity (hfun ⟨markedEmb V s hm 0, markedEmb_mem V hsV hm 0⟩)‖)
  * ∏ l ∈ Finset.univ.filter (fun l : Fin (m + 1) => l ≠ 0),
      (if P.incomp (hfun ⟨markedEmb V s hm (q l), markedEmb_mem V hsV hm (q l)⟩)
          (hfun ⟨markedEmb V s hm l, markedEmb_mem V hsV hm l⟩)
        then (1 : ℝ) else 0)
        * ‖P.activity (hfun ⟨markedEmb V s hm l, markedEmb_mem V hsV hm l⟩)‖)

open Classical in
/-- `block_sum_eq`, packaged through the named functional. -/
lemma sum_blockFunctional (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) {N m : ℕ} {V : Finset (Fin N)} {s : Fin N}
    (hsV : s ∈ V) (hm : (V.erase s).card = m)
    (q : Fin (m + 1) → Fin (m + 1)) :
    ∑ hfun : {x // x ∈ V} → P.Polymer,
      blockFunctional P c V s hsV hm q hfun
    = ∑ c' : P.Polymer, (if P.incomp c c' then (1 : ℝ) else 0)
        * ‖P.activity c'‖ * treeSumRawInner P c' q :=
  block_sum_eq P c hsV hm q

open Classical in
/-- **THE X-SUM FACTORIZATION (the recursion's heart):** for an admissible
structure with enumerated shell, the inner assignment sum factorizes into
the product over shell indices of `∑_{c'} 𝟙[incomp c c']·‖z(c')‖·
treeSumRawInner` at the subtree parent maps. -/
theorem inner_factorization {n D : ℕ} {p : Fin (n + 1) → Fin (n + 1)}
    {lev : Fin (n + 1) → Fin (D + 2)} (h : IsAdmissible p lev) {k : ℕ}
    {σ : Fin k → Fin (n + 1)} (hσinj : Function.Injective σ)
    (hσrange : Finset.univ.image σ
      = (Finset.univ : Finset (Fin (n + 1))).filter
          (fun s => s ≠ 0 ∧ p s = 0))
    (P : PolymerSystem) [Fintype P.Polymer] (c : P.Polymer)
    (hs : ∀ i, σ i ≠ 0) (hs1 : ∀ i, ((lev (σ i) : ℕ)) = 1) :
    treeSumRawInner P c p
    = ∏ i : Fin k, ∑ c' : P.Polymer,
        (if P.incomp c c' then (1 : ℝ) else 0) * ‖P.activity c'‖
          * treeSumRawInner P c' (subtreeParent h (hs i) (hs1 i) rfl) := by
  classical
  have hρ := shell_blockData_fn h hσinj hσrange
  have hsV : ∀ i, σ i ∈ shellFiber p lev (σ i) :=
    fun i => self_mem_shellFiber (hs i) (hs1 i)
  calc treeSumRawInner P c p
      = ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => X 0 = c),
          ∏ i : Fin k, blockFunctional P c (shellFiber p lev (σ i)) (σ i)
            (hsV i) rfl (subtreeParent h (hs i) (hs1 i) rfl)
            (fun x => X x.1) := by
        unfold treeSumRawInner
        refine Finset.sum_congr rfl fun X hX => ?_
        refine (master_factorization_fn h hσinj hσrange
          (fun u v => (if P.incomp (X u) (X v) then (1 : ℝ) else 0)
            * ‖P.activity (X v)‖) hs hs1).trans ?_
        refine Finset.prod_congr rfl fun i _ => ?_
        have hroot : ((if P.incomp (X 0) (X (σ i)) then (1 : ℝ) else 0)
              * ‖P.activity (X (σ i))‖)
            = ((if P.incomp c
                  (X (markedEmb (shellFiber p lev (σ i)) (σ i) rfl 0))
                then (1 : ℝ) else 0)
              * ‖P.activity
                  (X (markedEmb (shellFiber p lev (σ i)) (σ i) rfl 0))‖) := by
          rw [markedEmb_zero, (Finset.mem_filter.mp hX).2]
        unfold blockFunctional
        dsimp only
        rw [hroot]
      _ = ∑ g : {v : Fin (n + 1) // v ≠ 0} → P.Polymer,
          ∏ i : Fin k, blockFunctional P c (shellFiber p lev (σ i)) (σ i)
            (hsV i) rfl (subtreeParent h (hs i) (hs1 i) rfl)
            (fun x => g ⟨x.1, (mem_shellFiber.mp x.2).1⟩) := by
        refine (sum_pinned_eq c (fun X =>
          ∏ i : Fin k, blockFunctional P c (shellFiber p lev (σ i)) (σ i)
            (hsV i) rfl (subtreeParent h (hs i) (hs1 i) rfl)
            (fun x => X x.1))).trans ?_
        refine Finset.sum_congr rfl fun g _ => ?_
        refine Finset.prod_congr rfl fun i _ => ?_
        congr 1
        funext x
        dsimp only
        rw [dif_neg (mem_shellFiber.mp x.2).1]
      _ = ∑ g' : {v // v ∈ (Finset.univ :
            Finset (Fin (n + 1))).erase 0} → P.Polymer,
          ∏ i : Fin k, blockFunctional P c (shellFiber p lev (σ i)) (σ i)
            (hsV i) rfl (subtreeParent h (hs i) (hs1 i) rfl)
            (fun x => g' ⟨x.1, by
              rw [Finset.mem_erase]
              exact ⟨(mem_shellFiber.mp x.2).1, Finset.mem_univ _⟩⟩) := by
        refine Finset.sum_nbij'
          (i := fun g => fun v => g ⟨v.1, by
            have hv := v.2
            rw [Finset.mem_erase] at hv
            exact hv.1⟩)
          (j := fun g' => fun v => g' ⟨v.1, by
            rw [Finset.mem_erase]
            exact ⟨v.2, Finset.mem_univ _⟩⟩)
          (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
          (fun g _ => rfl) (fun g' _ => rfl) (fun g _ => rfl)
      _ = ∏ i : Fin k, ∑ hfun : {x // x ∈ shellFiber p lev (σ i)} → P.Polymer,
          blockFunctional P c (shellFiber p lev (σ i)) (σ i)
            (hsV i) rfl (subtreeParent h (hs i) (hs1 i) rfl) hfun :=
        hρ.sum_coverSplit (fun i =>
          blockFunctional P c (shellFiber p lev (σ i)) (σ i)
            (hsV i) rfl (subtreeParent h (hs i) (hs1 i) rfl))
      _ = ∏ i : Fin k, ∑ c' : P.Polymer,
          (if P.incomp c c' then (1 : ℝ) else 0) * ‖P.activity c'‖
            * treeSumRawInner P c' (subtreeParent h (hs i) (hs1 i) rfl) :=
        Finset.prod_congr rfl fun i _ =>
          sum_blockFunctional P c (hsV i) rfl _

open Classical in
/-- **Per-block structure sums recombine into `treeSumRaw`:** summing the
heart's per-block factor over all canonical depth-`D` structures yields
`∑_{c'} 𝟙[incomp c c']·‖z(c')‖·treeSumRaw P c' D m` — the quantity the
recursion's right-hand side reads. -/
lemma sum_structures_blockSum (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) (D m : ℕ) :
    ∑ pl ∈ (Finset.univ : Finset ((Fin (m + 1) → Fin (m + 1))
        × (Fin (m + 1) → Fin (D + 1)))).filter
        (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0),
      ∑ c' : P.Polymer, (if P.incomp c c' then (1 : ℝ) else 0)
        * ‖P.activity c'‖ * treeSumRawInner P c' pl.1
    = ∑ c' : P.Polymer, (if P.incomp c c' then (1 : ℝ) else 0)
        * ‖P.activity c'‖ * treeSumRaw P c' D m := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [treeSumRaw_eq_sum_inner, Finset.mul_sum]

open Classical in
/-- **Structures are determined by their fiber interiors (the injection's
spine):** two canonical admissible structures with the same enumerated
shell and the same fibers, agreeing on parents and levels away from the
shell roots, are equal — roots and the origin are forced (`p = 0`,
`lev = 1` at roots; canonicity at `0`), and the fibers cover everything
else. -/
lemma structure_determined {n D : ℕ}
    {p₁ p₂ : Fin (n + 1) → Fin (n + 1)}
    {lev₁ lev₂ : Fin (n + 1) → Fin (D + 2)}
    (h₁ : IsAdmissible p₁ lev₁) (h₂ : IsAdmissible p₂ lev₂)
    (hc₁ : p₁ 0 = 0) (hc₂ : p₂ 0 = 0) {k : ℕ}
    {σ : Fin k → Fin (n + 1)}
    (hσr₁ : Finset.univ.image σ
      = (Finset.univ : Finset (Fin (n + 1))).filter
          (fun s => s ≠ 0 ∧ p₁ s = 0))
    (hσr₂ : Finset.univ.image σ
      = (Finset.univ : Finset (Fin (n + 1))).filter
          (fun s => s ≠ 0 ∧ p₂ s = 0))
    (hpar : ∀ (i : Fin k) (v : Fin (n + 1)),
      v ∈ shellFiber p₁ lev₁ (σ i) → v ≠ σ i →
        p₁ v = p₂ v ∧ (lev₁ v : ℕ) = (lev₂ v : ℕ)) :
    p₁ = p₂ ∧ lev₁ = lev₂ := by
  classical
  have hroots : ∀ i : Fin k,
      (σ i ≠ 0 ∧ p₁ (σ i) = 0) ∧ p₂ (σ i) = 0 := by
    intro i
    have hm₁ : σ i ∈ (Finset.univ : Finset (Fin (n + 1))).filter
        (fun s => s ≠ 0 ∧ p₁ s = 0) := by
      rw [← hσr₁]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have hm₂ : σ i ∈ (Finset.univ : Finset (Fin (n + 1))).filter
        (fun s => s ≠ 0 ∧ p₂ s = 0) := by
      rw [← hσr₂]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    exact ⟨(Finset.mem_filter.mp hm₁).2, (Finset.mem_filter.mp hm₂).2.2⟩
  have hlev1 : ∀ i : Fin k,
      ((lev₁ (σ i) : ℕ)) = 1 ∧ ((lev₂ (σ i) : ℕ)) = 1 := fun i =>
    ⟨(h₁.parent_eq_zero_iff (hroots i).1.1).mp (hroots i).1.2,
      (h₂.parent_eq_zero_iff (hroots i).1.1).mp (hroots i).2⟩
  have hloc : ∀ v : Fin (n + 1), v ≠ 0 →
      ∃ i, v ∈ shellFiber p₁ lev₁ (σ i) := by
    intro v hv0
    have hsr0 := h₁.shellRoot_ne_zero hv0
    have hsrp := h₁.parent_shellRoot hv0
    have hmem : shellRoot p₁ lev₁ v ∈ Finset.univ.image σ := by
      rw [hσr₁]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsr0, hsrp⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    exact ⟨i, mem_shellFiber.mpr ⟨hv0, hi.symm⟩⟩
  constructor
  · funext v
    by_cases hv0 : v = 0
    · rw [hv0, hc₁, hc₂]
    · obtain ⟨i, hvfib⟩ := hloc v hv0
      by_cases hvs : v = σ i
      · rw [hvs, (hroots i).1.2, (hroots i).2]
      · exact (hpar i v hvfib hvs).1
  · funext v
    apply Fin.ext
    by_cases hv0 : v = 0
    · rw [hv0, congrArg Fin.val h₁.1, congrArg Fin.val h₂.1]
    · obtain ⟨i, hvfib⟩ := hloc v hv0
      by_cases hvs : v = σ i
      · rw [hvs, (hlev1 i).1, (hlev1 i).2]
      · exact (hpar i v hvfib hvs).2

open Classical in
/-- **The class parent map** — `subtreeParent` rebuilt against a *fixed*
block `(F, s)` (the per-class form of the final injection; no dependence
on the structure's own fiber in the type). -/
noncomputable def classParent (F : Finset (Fin (n + 1))) (s : Fin (n + 1))
    (hsF : s ∈ F) {m : ℕ} (hm : (F.erase s).card = m)
    (p : Fin (n + 1) → Fin (n + 1))
    (hstab : ∀ l : Fin (m + 1), l ≠ 0 → p (markedEmb F s hm l) ∈ F) :
    Fin (m + 1) → Fin (m + 1) :=
  fun l => if hl : l = 0 then 0
    else (markedEquiv F hsF hm).symm
      ⟨p (markedEmb F s hm l), hstab l hl⟩

open Classical in
/-- On a structure's own fiber, the class parent map is the subtree
parent map. -/
lemma classParent_eq_subtreeParent {n D : ℕ}
    {p : Fin (n + 1) → Fin (n + 1)} {lev : Fin (n + 1) → Fin (D + 2)}
    (h : IsAdmissible p lev) {s : Fin (n + 1)} (hs : s ≠ 0)
    (hs1 : (lev s : ℕ) = 1)
    (hstab : ∀ l : Fin (((shellFiber p lev s).erase s).card + 1), l ≠ 0 →
      p (markedEmb (shellFiber p lev s) s rfl l) ∈ shellFiber p lev s) :
    classParent (shellFiber p lev s) s (self_mem_shellFiber hs hs1) rfl
      p hstab = subtreeParent h hs hs1 rfl := by
  funext l
  unfold classParent subtreeParent
  by_cases hl : l = 0
  · rw [dif_pos hl, dif_pos hl]
  · rw [dif_neg hl, dif_neg hl]
    congr 1

open Classical in
/-- The stability hypothesis holds on a structure's own fiber. -/
lemma shellFiber_stab {n D : ℕ} {p : Fin (n + 1) → Fin (n + 1)}
    {lev : Fin (n + 1) → Fin (D + 2)} (h : IsAdmissible p lev)
    {s : Fin (n + 1)} (hs : s ≠ 0) (hs1 : (lev s : ℕ) = 1) :
    ∀ l : Fin (((shellFiber p lev s).erase s).card + 1), l ≠ 0 →
      p (markedEmb (shellFiber p lev s) s rfl l) ∈ shellFiber p lev s := by
  intro l hl
  have hmem : markedEmb (shellFiber p lev s) s rfl l ∈ shellFiber p lev s :=
    markedEmb_mem _ (self_mem_shellFiber hs hs1) rfl l
  have hne : markedEmb (shellFiber p lev s) s rfl l ≠ s := by
    intro hEq
    apply hl
    have h0 : markedEmb (shellFiber p lev s) s rfl 0 = s :=
      markedEmb_zero _ _ _
    exact markedEmb_injective _ _ rfl (hEq.trans h0.symm)
  exact (shellFiber_parent_mem h hmem hne).2.2

open Classical in
/-- **The class level map** — `subtreeLev` against a fixed block. -/
noncomputable def classLev {D : ℕ} (F : Finset (Fin (n + 1)))
    (s : Fin (n + 1)) {m : ℕ} (hm : (F.erase s).card = m)
    (lev : Fin (n + 1) → Fin (D + 2)) : Fin (m + 1) → Fin (D + 1) :=
  fun l => ⟨(lev (markedEmb F s hm l) : ℕ) - 1, by
    have := (lev (markedEmb F s hm l)).isLt
    omega⟩

open Classical in
/-- **Interior agreement from carrier equality:** if two structures have
equal class parent and level maps on a block, they agree pointwise on the
block's interior — the hypothesis `structure_determined` consumes,
extracted with no transport (the marked equivalence is injective). -/
lemma class_data_interior_agreement {D : ℕ}
    {F : Finset (Fin (n + 1))} {s : Fin (n + 1)} (hsF : s ∈ F)
    {m : ℕ} (hm : (F.erase s).card = m)
    {p₁ p₂ : Fin (n + 1) → Fin (n + 1)}
    {lev₁ lev₂ : Fin (n + 1) → Fin (D + 2)}
    (h₁ : IsAdmissible p₁ lev₁) (h₂ : IsAdmissible p₂ lev₂)
    (hF0 : (0 : Fin (n + 1)) ∉ F)
    {hstab₁ : ∀ l : Fin (m + 1), l ≠ 0 → p₁ (markedEmb F s hm l) ∈ F}
    {hstab₂ : ∀ l : Fin (m + 1), l ≠ 0 → p₂ (markedEmb F s hm l) ∈ F}
    (hq : classParent F s hsF hm p₁ hstab₁
      = classParent F s hsF hm p₂ hstab₂)
    (hl : classLev F s hm lev₁ = classLev F s hm lev₂) :
    ∀ v ∈ F, v ≠ s → p₁ v = p₂ v ∧ (lev₁ v : ℕ) = (lev₂ v : ℕ) := by
  intro v hv hvs
  set l : Fin (m + 1) := (markedEquiv F hsF hm).symm ⟨v, hv⟩ with hldef
  have hemb : markedEmb F s hm l = v := by
    have := congrArg Subtype.val
      ((markedEquiv F hsF hm).apply_symm_apply ⟨v, hv⟩)
    rwa [markedEquiv_apply_val] at this
  have hl0 : l ≠ 0 := by
    intro hEq
    apply hvs
    rw [← hemb, hEq, markedEmb_zero]
  constructor
  · have hq' := congrFun hq l
    unfold classParent at hq'
    rw [dif_neg hl0, dif_neg hl0] at hq'
    have h2 := (markedEquiv F hsF hm).symm.injective hq'
    have h3 := congrArg Subtype.val h2
    simp only at h3
    rwa [hemb] at h3
  · have hv0 : v ≠ 0 := fun hEq => hF0 (hEq ▸ hv)
    have hge₁ := h₁.one_le_lev hv0
    have hge₂ := h₂.one_le_lev hv0
    have hl' := congrArg Fin.val (congrFun hl l)
    unfold classLev at hl'
    simp only at hl'
    rw [hemb] at hl'
    omega

open Classical in
/-- **The totalized per-block factor** (§5f convention): defined for any
`(V, s)` with no side conditions, so fiber-equalities transport its value
by plain `congrArg`. -/
noncomputable def blockS (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) (D : ℕ) {N : ℕ} (V : Finset (Fin N)) (s : Fin N) : ℝ :=
  ∑ c' : P.Polymer, (if P.incomp c c' then (1 : ℝ) else 0)
    * ‖P.activity c'‖ * treeSumRaw P c' D ((V.erase s).card)

open Classical in
lemma blockS_nonneg (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) (D : ℕ) {N : ℕ} (V : Finset (Fin N)) (s : Fin N) :
    0 ≤ blockS P c D V s := by
  unfold blockS
  refine Finset.sum_nonneg fun c' _ => ?_
  refine mul_nonneg (mul_nonneg ?_ (norm_nonneg _)) ?_
  · split_ifs <;> norm_num
  · -- treeSumRaw is a sum of nonneg inner sums
    rw [treeSumRaw_eq_sum_inner]
    exact Finset.sum_nonneg fun pl _ => treeSumRawInner_nonneg P c' pl.1

open Classical in
/-- **Per-block structure sums are `blockS`** — the recombination, in the
totalized form the wrapper's right-hand side reads. -/
lemma sum_structures_eq_blockS (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) (D : ℕ) {N : ℕ} (V : Finset (Fin N)) (s : Fin N) :
    ∑ pl ∈ (Finset.univ : Finset ((Fin ((V.erase s).card + 1)
        → Fin ((V.erase s).card + 1))
        × (Fin ((V.erase s).card + 1) → Fin (D + 1)))).filter
        (fun pl => IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0),
      ∑ c' : P.Polymer, (if P.incomp c c' then (1 : ℝ) else 0)
        * ‖P.activity c'‖ * treeSumRawInner P c' pl.1
    = blockS P c D V s :=
  sum_structures_blockSum P c D ((V.erase s).card)

open Classical in
/-- **Class carriers of class members are canonical-admissible** (the
wrapper's maps-into condition): for a structure whose fiber at `σ i` is
the class block `F i`, the class parent/level maps form a canonical
admissible depth-`D` structure.  Proved by rewriting the block back to
the structure's own fiber wholesale (`← hFi` — everything is functorial
in the plain `Finset` argument) and invoking the subtree machinery. -/
lemma class_carrier_admissible {n D : ℕ}
    {p : Fin (n + 1) → Fin (n + 1)} {lev : Fin (n + 1) → Fin (D + 2)}
    (h : IsAdmissible p lev) {s : Fin (n + 1)} {F : Finset (Fin (n + 1))}
    (hs : s ≠ 0) (hs1 : (lev s : ℕ) = 1)
    (hF : shellFiber p lev s = F) (hsF : s ∈ F)
    (hstab : ∀ l : Fin ((F.erase s).card + 1), l ≠ 0 →
      p (markedEmb F s rfl l) ∈ F) :
    IsAdmissible (classParent F s hsF rfl p hstab)
      (classLev F s rfl lev)
    ∧ classParent F s hsF rfl p hstab 0 = 0 := by
  subst hF
  constructor
  · rw [classParent_eq_subtreeParent h hs hs1 hstab]
    have hlev : classLev (shellFiber p lev s) s rfl lev
        = subtreeLev hs hs1 rfl := by
      funext l
      apply Fin.ext
      show (lev (markedEmb (shellFiber p lev s) s rfl l) : ℕ) - 1
        = ((subtreeLev hs hs1 rfl l : Fin (D + 1)) : ℕ)
      have hval : ((subtreeLev hs hs1 rfl l : Fin (D + 1)) : ℕ)
          = (lev ((markedEquiv (shellFiber p lev s)
              (self_mem_shellFiber hs hs1) rfl l).1) : ℕ) - 1 := rfl
      rw [hval, markedEquiv_apply_val]
    rw [hlev]
    exact subtreeStructure_isAdmissible h hs hs1 rfl
  · unfold classParent
    rw [dif_pos rfl]

open Classical in
/-- **Per-block value transport:** the heart's block sum at the subtree
parent equals the same sum at the class carrier (one `subst`, one
agreement). -/
lemma class_value_block {n D : ℕ}
    {p : Fin (n + 1) → Fin (n + 1)} {lev : Fin (n + 1) → Fin (D + 2)}
    (h : IsAdmissible p lev) {s : Fin (n + 1)} (hs : s ≠ 0)
    (hs1 : (lev s : ℕ) = 1) {F : Finset (Fin (n + 1))}
    (hF : shellFiber p lev s = F) (hsF : s ∈ F)
    (hstab : ∀ l : Fin ((F.erase s).card + 1), l ≠ 0 →
      p (markedEmb F s rfl l) ∈ F)
    (P : PolymerSystem) [Fintype P.Polymer] (c : P.Polymer) :
    (∑ c' : P.Polymer, (if P.incomp c c' then (1 : ℝ) else 0)
      * ‖P.activity c'‖
      * treeSumRawInner P c' (subtreeParent h hs hs1 rfl))
    = ∑ c' : P.Polymer, (if P.incomp c c' then (1 : ℝ) else 0)
      * ‖P.activity c'‖
      * treeSumRawInner P c' (classParent F s hsF rfl p hstab) := by
  subst hF
  rw [classParent_eq_subtreeParent h hs hs1 hstab]

open Classical in
/-- **The heart at the class carriers:** for a class member, the inner
assignment sum equals the product of block sums at the class parent
maps — `inner_factorization` transported block-by-block. -/
theorem class_value_eq {n D : ℕ}
    {p : Fin (n + 1) → Fin (n + 1)} {lev : Fin (n + 1) → Fin (D + 2)}
    (h : IsAdmissible p lev) {k : ℕ} {σ : Fin k → Fin (n + 1)}
    (hσinj : Function.Injective σ)
    (hσrange : Finset.univ.image σ
      = (Finset.univ : Finset (Fin (n + 1))).filter
          (fun s => s ≠ 0 ∧ p s = 0))
    (P : PolymerSystem) [Fintype P.Polymer] (c : P.Polymer)
    (hs : ∀ i, σ i ≠ 0) (hs1 : ∀ i, ((lev (σ i) : ℕ)) = 1)
    {F : Fin k → Finset (Fin (n + 1))}
    (hF : ∀ i, shellFiber p lev (σ i) = F i)
    (hsF : ∀ i, σ i ∈ F i)
    (hstab : ∀ i, ∀ l : Fin (((F i).erase (σ i)).card + 1), l ≠ 0 →
      p (markedEmb (F i) (σ i) rfl l) ∈ F i) :
    treeSumRawInner P c p
    = ∏ i : Fin k, ∑ c' : P.Polymer,
        (if P.incomp c c' then (1 : ℝ) else 0) * ‖P.activity c'‖
          * treeSumRawInner P c'
              (classParent (F i) (σ i) (hsF i) rfl p (hstab i)) :=
  (inner_factorization h hσinj hσrange P c hs hs1).trans
    (Finset.prod_congr rfl fun i _ =>
      class_value_block h (hs i) (hs1 i) (hF i) (hsF i) (hstab i) P c)

open Classical in
/-- **THE CLASS-SUM WRAPPER (the final injection):** the inner sums of a
class of structures — fixed shell enumeration `σ`, fixed fibers `F` —
are bounded by the product of the totalized block factors. -/
theorem class_sum_le {n D : ℕ} {k : ℕ} {σ : Fin k → Fin (n + 1)}
    (hσinj : Function.Injective σ)
    (F : Fin k → Finset (Fin (n + 1)))
    (P : PolymerSystem) [Fintype P.Polymer] (c : P.Polymer) :
    ∑ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
        × (Fin (n + 1) → Fin (D + 2)))).filter
        (fun pl => (IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0)
          ∧ (Finset.univ.image σ
              = (Finset.univ : Finset (Fin (n + 1))).filter
                  (fun s => s ≠ 0 ∧ pl.1 s = 0))
          ∧ ∀ i, shellFiber pl.1 pl.2 (σ i) = F i),
      treeSumRawInner P c pl.1
    ≤ ∏ i : Fin k, blockS P c D (F i) (σ i) := by
  classical
  set T : ∀ i : Fin k, Finset
      ((Fin (((F i).erase (σ i)).card + 1)
        → Fin (((F i).erase (σ i)).card + 1))
      × (Fin (((F i).erase (σ i)).card + 1) → Fin (D + 1))) :=
    fun i => (Finset.univ).filter
      (fun q => IsAdmissible q.1 q.2 ∧ q.1 0 = 0) with hTdef
  set Cond : ((Fin (n + 1) → Fin (n + 1))
      × (Fin (n + 1) → Fin (D + 2))) → Prop :=
    fun pl => (IsAdmissible pl.1 pl.2 ∧ pl.1 0 = 0)
      ∧ (Finset.univ.image σ
          = (Finset.univ : Finset (Fin (n + 1))).filter
              (fun s => s ≠ 0 ∧ pl.1 s = 0))
      ∧ ∀ i, shellFiber pl.1 pl.2 (σ i) = F i with hConddef
  have hshell : ∀ pl, Cond pl → ∀ i : Fin k,
      σ i ≠ 0 ∧ pl.1 (σ i) = 0 ∧ ((pl.2 (σ i) : ℕ)) = 1 := by
    intro pl hc i
    have hmem : σ i ∈ (Finset.univ : Finset (Fin (n + 1))).filter
        (fun s => s ≠ 0 ∧ pl.1 s = 0) := by
      rw [← hc.2.1]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have h2 := (Finset.mem_filter.mp hmem).2
    exact ⟨h2.1, h2.2, (hc.1.1.parent_eq_zero_iff h2.1).mp h2.2⟩
  have hpack : ∀ pl, Cond pl → ∀ i : Fin k, (σ i ∈ F i)
      ∧ ∀ l : Fin (((F i).erase (σ i)).card + 1), l ≠ 0 →
          pl.1 (markedEmb (F i) (σ i) rfl l) ∈ F i := by
    intro pl hc i
    obtain ⟨hs, -, hs1⟩ := hshell pl hc i
    constructor
    · rw [← hc.2.2 i]
      exact self_mem_shellFiber hs hs1
    · have hstab := shellFiber_stab hc.1.1 hs hs1
      rw [hc.2.2 i] at hstab
      exact hstab
  have hF0 : ∀ pl, Cond pl → ∀ i : Fin k, (0 : Fin (n + 1)) ∉ F i := by
    intro pl hc i h0
    rw [← hc.2.2 i, mem_shellFiber] at h0
    exact h0.1 rfl
  -- the total injection map
  set Φ : ((Fin (n + 1) → Fin (n + 1)) × (Fin (n + 1) → Fin (D + 2)))
      → ∀ i : Fin k,
        ((Fin (((F i).erase (σ i)).card + 1)
          → Fin (((F i).erase (σ i)).card + 1))
        × (Fin (((F i).erase (σ i)).card + 1) → Fin (D + 1))) :=
    fun pl => if hc : Cond pl
      then fun i => (classParent (F i) (σ i) (hpack pl hc i).1 rfl
          pl.1 (hpack pl hc i).2,
        classLev (F i) (σ i) rfl pl.2)
      else fun i => (fun _ => 0, fun _ => 0) with hΦdef
  -- the value of each class member factors through Φ
  set G : (∀ i : Fin k,
      ((Fin (((F i).erase (σ i)).card + 1)
        → Fin (((F i).erase (σ i)).card + 1))
      × (Fin (((F i).erase (σ i)).card + 1) → Fin (D + 1)))) → ℝ :=
    fun t => ∏ i : Fin k, ∑ c' : P.Polymer,
      (if P.incomp c c' then (1 : ℝ) else 0) * ‖P.activity c'‖
        * treeSumRawInner P c' ((t i).1) with hGdef
  have hval : ∀ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
      × (Fin (n + 1) → Fin (D + 2)))).filter Cond,
      treeSumRawInner P c pl.1 = G (Φ pl) := by
    intro pl hpl
    have hc : Cond pl := (Finset.mem_filter.mp hpl).2
    have hkey := class_value_eq hc.1.1 hσinj hc.2.1 P c
      (fun i => (hshell pl hc i).1) (fun i => (hshell pl hc i).2.2)
      hc.2.2 (fun i => (hpack pl hc i).1) (fun i => (hpack pl hc i).2)
    rw [hkey, hGdef]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hΦdef]
    dsimp only
    rw [dif_pos hc]
  have hGnn : ∀ t, 0 ≤ G t := by
    intro t
    rw [hGdef]
    refine Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun c' _ => ?_
    refine mul_nonneg (mul_nonneg ?_ (norm_nonneg _))
      (treeSumRawInner_nonneg P c' _)
    split_ifs <;> norm_num
  -- injectivity on the class
  have hinj : ∀ pl₁ ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
      × (Fin (n + 1) → Fin (D + 2)))).filter Cond,
      ∀ pl₂ ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
        × (Fin (n + 1) → Fin (D + 2)))).filter Cond,
      Φ pl₁ = Φ pl₂ → pl₁ = pl₂ := by
    intro pl₁ h₁ pl₂ h₂ heq
    have hc₁ : Cond pl₁ := (Finset.mem_filter.mp h₁).2
    have hc₂ : Cond pl₂ := (Finset.mem_filter.mp h₂).2
    rw [hΦdef] at heq
    simp only [dif_pos hc₁, dif_pos hc₂] at heq
    have hinterior : ∀ i : Fin k, ∀ v ∈ F i, v ≠ σ i →
        pl₁.1 v = pl₂.1 v ∧ ((pl₁.2 v : ℕ)) = ((pl₂.2 v : ℕ)) := by
      intro i
      have hpair := congrFun heq i
      exact class_data_interior_agreement (hpack pl₁ hc₁ i).1 rfl
        hc₁.1.1 hc₂.1.1 (hF0 pl₁ hc₁ i)
        (congrArg Prod.fst hpair) (congrArg Prod.snd hpair)
    have hdet := structure_determined hc₁.1.1 hc₂.1.1
      hc₁.1.2 hc₂.1.2 hc₁.2.1 hc₂.2.1
      (fun i v hv hvs => by
        rw [hc₁.2.2 i] at hv
        exact hinterior i v hv hvs)
    exact Prod.ext hdet.1 hdet.2
  -- maps into the canonical product space
  have hmaps : ∀ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
      × (Fin (n + 1) → Fin (D + 2)))).filter Cond,
      Φ pl ∈ Fintype.piFinset T := by
    intro pl hpl
    have hc : Cond pl := (Finset.mem_filter.mp hpl).2
    rw [Fintype.mem_piFinset]
    intro i
    rw [hΦdef]
    dsimp only
    rw [dif_pos hc, hTdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact class_carrier_admissible hc.1.1 (hshell pl hc i).1
      (hshell pl hc i).2.2 (hc.2.2 i) (hpack pl hc i).1
      (hpack pl hc i).2
  -- assemble
  calc ∑ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
        × (Fin (n + 1) → Fin (D + 2)))).filter Cond,
        treeSumRawInner P c pl.1
      = ∑ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
          × (Fin (n + 1) → Fin (D + 2)))).filter Cond, G (Φ pl) :=
        Finset.sum_congr rfl hval
    _ = ∑ t ∈ ((Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
          × (Fin (n + 1) → Fin (D + 2)))).filter Cond).image Φ, G t :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ t ∈ Fintype.piFinset T, G t := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun t _ _ => hGnn t)
        intro t ht
        obtain ⟨pl, hpl, rfl⟩ := Finset.mem_image.mp ht
        exact hmaps pl hpl
    _ = ∏ i : Fin k, ∑ q ∈ T i, ∑ c' : P.Polymer,
          (if P.incomp c c' then (1 : ℝ) else 0) * ‖P.activity c'‖
            * treeSumRawInner P c' q.1 := by
        rw [hGdef]
        exact (Finset.prod_univ_sum T (fun i q =>
          ∑ c' : P.Polymer, (if P.incomp c c' then (1 : ℝ) else 0)
            * ‖P.activity c'‖ * treeSumRawInner P c' q.1)).symm
    _ = ∏ i : Fin k, blockS P c D (F i) (σ i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hTdef]
        exact sum_structures_eq_blockS P c D (F i) (σ i)

open Classical in
/-- No enumerations at the wrong cardinality. -/
lemma card_enumerations_ne {α : Type*} [DecidableEq α] [Fintype α]
    {S : Finset α} {k : ℕ} (hk : S.card ≠ k) :
    ((Finset.univ : Finset (Fin k → α)).filter
      (fun σ => Function.Injective σ ∧ Finset.univ.image σ = S)) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro σ _ hσ
  apply hk
  rw [← hσ.2, Finset.card_image_of_injective _ hσ.1,
    Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **Function-form symmetrization (outer step O1):** a sum over objects
equals the `1/k!`-weighted sum over (object, shell enumeration) pairs,
the enumerations ranging over injective functions with prescribed image —
only the matching cardinality contributes, with exactly `k!` terms. -/
lemma sum_symmetrize_fn {N' nmax : ℕ} {α : Type*} [Fintype α]
    [DecidableEq α] (A : Finset α) (G : α → ℝ)
    (S : α → Finset (Fin N')) (hSle : ∀ a ∈ A, (S a).card ≤ nmax) :
    ∑ a ∈ A, G a
    = ∑ k ∈ Finset.range (nmax + 1), ((k.factorial : ℝ))⁻¹ *
        ∑ a ∈ A, ∑ _σ ∈ (Finset.univ : Finset (Fin k → Fin N')).filter
          (fun σ => Function.Injective σ ∧ Finset.univ.image σ = S a),
          G a := by
  classical
  have hswap : ∀ k : ℕ, ((k.factorial : ℝ))⁻¹ *
      ∑ a ∈ A, ∑ _σ ∈ (Finset.univ : Finset (Fin k → Fin N')).filter
        (fun σ => Function.Injective σ ∧ Finset.univ.image σ = S a), G a
      = ∑ a ∈ A, ((k.factorial : ℝ))⁻¹ *
          (((Finset.univ : Finset (Fin k → Fin N')).filter
            (fun σ => Function.Injective σ ∧ Finset.univ.image σ = S a)).card
            : ℝ) * G a := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  calc ∑ a ∈ A, G a
      = ∑ a ∈ A, ∑ k ∈ Finset.range (nmax + 1),
          ((k.factorial : ℝ))⁻¹ *
          (((Finset.univ : Finset (Fin k → Fin N')).filter
            (fun σ => Function.Injective σ ∧ Finset.univ.image σ = S a)).card
            : ℝ) * G a := by
        refine Finset.sum_congr rfl fun a ha => ?_
        have hk0 : (S a).card ∈ Finset.range (nmax + 1) := by
          rw [Finset.mem_range]
          exact Nat.lt_succ_of_le (hSle a ha)
        rw [Finset.sum_eq_single_of_mem (S a).card hk0]
        · rw [card_enumerations rfl]
          have hne : (((S a).card.factorial : ℝ)) ≠ 0 := by positivity
          field_simp
        · intro k _ hk
          rw [card_enumerations_ne (fun h => hk h.symm)]
          simp
    _ = ∑ k ∈ Finset.range (nmax + 1), ((k.factorial : ℝ))⁻¹ *
        ∑ a ∈ A, ∑ _σ ∈ (Finset.univ : Finset (Fin k → Fin N')).filter
          (fun σ => Function.Injective σ ∧ Finset.univ.image σ = S a),
          G a := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (hswap k).symm

end MasterAssembly

end BlockCount

end YangMills.KP
