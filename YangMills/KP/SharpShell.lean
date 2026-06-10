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
      (fun pl => IsAdmissible pl.1 pl.2),
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
      (fun pl => IsAdmissible pl.1 pl.2) := by
    intro T hT
    have htree := isTree_of_mem_spanningTrees _ (htop T hT)
    have hconn := htree.isConnected
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
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
          (fun pl => IsAdmissible pl.1 pl.2), G pl := by
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
        (fun pl => IsAdmissible pl.1 pl.2),
      ∀ pl₂ ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
        × (Fin (n + 1) → Fin (D + 1)))).filter
        (fun pl => IsAdmissible pl.1 pl.2),
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
        (fun pl => IsAdmissible pl.1 pl.2),
        ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
          ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
            (if P.incomp (X (pl.1 v)) (X v) then (1 : ℝ) else 0)
              * ‖P.activity (X v)‖
      = ∑ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
          × (Fin (n + 1) → Fin (D + 1)))).filter
          (fun pl => IsAdmissible pl.1 pl.2), G (ψ pl) :=
        Finset.sum_congr rfl fun pl _ => rfl
    _ = ∑ q ∈ ((Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
          × (Fin (n + 1) → Fin (D + 1)))).filter
          (fun pl => IsAdmissible pl.1 pl.2)).image ψ, G q :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
          × (Fin (n + 1) → Fin (D + 2)))).filter
          (fun pl => IsAdmissible pl.1 pl.2), G q := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => ?_)
        · intro q hq
          obtain ⟨pl, hpl, rfl⟩ := Finset.mem_image.mp hq
          rw [Finset.mem_filter] at hpl ⊢
          obtain ⟨hlev0, hdesc⟩ := hpl.2
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · show ((ψ pl).2 0) = 0
            rw [hψdef]
            apply Fin.ext
            simp only [Fin.coe_castSucc]
            exact congrArg Fin.val hlev0
          · intro v hv
            show (((ψ pl).2 ((ψ pl).1 v)) : ℕ) + 1 = (((ψ pl).2 v) : ℕ)
            rw [hψdef]
            simpa using hdesc v hv
        · rw [hGdef]
          refine Finset.sum_nonneg fun X _ =>
            Finset.prod_nonneg fun v _ => mul_nonneg ?_ (norm_nonneg _)
          split_ifs <;> norm_num
    _ = ∑ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
          × (Fin (n + 1) → Fin (D + 2)))).filter
          (fun pl => IsAdmissible pl.1 pl.2),
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
      × (Fin 1 → Fin 1))).filter (fun pl => IsAdmissible pl.1 pl.2)
      = Finset.univ := by
    refine Finset.filter_true_of_mem fun pl _ => ?_
    refine ⟨by omega, fun v hv => ?_⟩
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
      × (Fin (n + 2) → Fin 1))).filter (fun pl => IsAdmissible pl.1 pl.2)
      = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro pl _
    intro hadm
    have h1 : (1 : Fin (n + 2)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have := hadm.2 1 h1
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
disjoint blocks covering `Fin n`, each with a marked root, block `i` of
size `m i + 1`.  These parametrize the fibers of the shell decomposition
(unsorted form — see `docs/SHARP-KP-PLAN.md`, C3 design correction). -/
def IsBlockData (m : Fin k → ℕ) (ρ : Fin k → Finset (Fin n) × Fin n) :
    Prop :=
  (∀ i j, i ≠ j → Disjoint (ρ i).1 (ρ j).1) ∧
  (Finset.univ.biUnion (fun i => (ρ i).1) = Finset.univ) ∧
  (∀ i, (ρ i).2 ∈ (ρ i).1) ∧ (∀ i, (ρ i).1.card = m i + 1)

/-- Block sizes account for every vertex: `∑ (m i + 1) = n`. -/
lemma IsBlockData.sum_card {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData m ρ) :
    ∑ i, (m i + 1) = n := by
  classical
  have h1 : (Finset.univ : Finset (Fin n)).card = n := by simp
  rw [← h1, ← hρ.2.1, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun i _ => (hρ.2.2.2 i).symm
  · intro i _ j _ hij
    exact hρ.1 i j hij

/-- Every vertex lies in exactly one block. -/
lemma IsBlockData.existsUnique_mem {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData m ρ)
    (v : Fin n) : ∃! i, v ∈ (ρ i).1 := by
  have hv : v ∈ Finset.univ.biUnion (fun i => (ρ i).1) := by
    rw [hρ.2.1]
    exact Finset.mem_univ v
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hne
  exact (Finset.disjoint_left.mp (hρ.1 j i hne) hj) hi

/-- The block index of a vertex. -/
noncomputable def IsBlockData.blockIndex {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData m ρ)
    (v : Fin n) : Fin k :=
  (hρ.existsUnique_mem v).exists.choose

lemma IsBlockData.mem_blockIndex {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData m ρ)
    (v : Fin n) : v ∈ (ρ (hρ.blockIndex v)).1 :=
  (hρ.existsUnique_mem v).exists.choose_spec

lemma IsBlockData.blockIndex_eq {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData m ρ)
    {v : Fin n} {i : Fin k} (h : v ∈ (ρ i).1) :
    hρ.blockIndex v = i := by
  have huniq := hρ.existsUnique_mem v
  exact (huniq.unique (hρ.mem_blockIndex v) h)

/-- Roots of distinct blocks are distinct. -/
lemma IsBlockData.root_injective {m : Fin k → ℕ}
    {ρ : Fin k → Finset (Fin n) × Fin n} (hρ : IsBlockData m ρ)
    {i j : Fin k} (h : (ρ i).2 = (ρ j).2) : i = j := by
  by_contra hne
  have hi := hρ.2.2.1 i
  have hj := hρ.2.2.1 j
  rw [h] at hi
  exact (Finset.disjoint_left.mp (hρ.1 i j hne) hi) hj

variable {m : Fin k → ℕ} {ρ : Fin k → Finset (Fin n) × Fin n}

/-- The increasing enumeration of a block's non-root elements. -/
def IsBlockData.nonRootEmb (hρ : IsBlockData m ρ) (i : Fin k) :
    Fin (m i) ↪o Fin n :=
  Finset.orderEmbOfFin ((ρ i).1.erase (ρ i).2) (by
    rw [Finset.card_erase_of_mem (hρ.2.2.1 i), hρ.2.2.2 i]
    omega)

lemma IsBlockData.nonRootEmb_mem (hρ : IsBlockData m ρ) (i : Fin k)
    (j : Fin (m i)) : hρ.nonRootEmb i j ∈ (ρ i).1 :=
  Finset.mem_of_mem_erase (Finset.orderEmbOfFin_mem _ _ _)

lemma IsBlockData.nonRootEmb_ne_root (hρ : IsBlockData m ρ) (i : Fin k)
    (j : Fin (m i)) : hρ.nonRootEmb i j ≠ (ρ i).2 :=
  (Finset.mem_erase.mp (Finset.orderEmbOfFin_mem _ _ _)).1

/-- **The placement function**: list each block root-first, then its
non-root elements in increasing order twisted by a local permutation. -/
def IsBlockData.placeFun (hρ : IsBlockData m ρ)
    (π : ∀ i, Equiv.Perm (Fin (m i))) :
    (Σ i : Fin k, Fin (m i + 1)) → Fin n :=
  fun x => Fin.cases ((ρ x.1).2)
    (fun j => hρ.nonRootEmb x.1 ((π x.1) j)) x.2

lemma IsBlockData.placeFun_zero (hρ : IsBlockData m ρ)
    (π : ∀ i, Equiv.Perm (Fin (m i))) (i : Fin k) :
    hρ.placeFun π ⟨i, 0⟩ = (ρ i).2 := rfl

lemma IsBlockData.placeFun_succ (hρ : IsBlockData m ρ)
    (π : ∀ i, Equiv.Perm (Fin (m i))) (i : Fin k) (j : Fin (m i)) :
    hρ.placeFun π ⟨i, j.succ⟩ = hρ.nonRootEmb i ((π i) j) := by
  simp [IsBlockData.placeFun]

lemma IsBlockData.placeFun_mem (hρ : IsBlockData m ρ)
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

lemma IsBlockData.placeFun_injective (hρ : IsBlockData m ρ)
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
/-- **THE BLOCK-COUNTING BOUND (†′):** ordered rooted disjoint covering
block data with sizes `m i + 1` number at most `n!/∏ (m i)!` —
multiplicatively, `card · ∏ (m i)! ≤ n!`.  Proof: block data together
with local permutations inject into bijections
`(Σ i, Fin (m i + 1)) ≃ Fin n` via the placement function, and there are
exactly `n!` such bijections. -/
theorem card_blockData_mul_le (m : Fin k → ℕ)
    (hsum : ∑ i, (m i + 1) = n) :
    ((Finset.univ : Finset (Fin k → Finset (Fin n) × Fin n)).filter
      (fun ρ => IsBlockData m ρ)).card * ∏ i, (m i).factorial
      ≤ n.factorial := by
  classical
  have hcardSig : Fintype.card (Σ i : Fin k, Fin (m i + 1)) = n := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact hsum
  have e₀ : (Σ i : Fin k, Fin (m i + 1)) ≃ Fin n :=
    Fintype.equivFinOfCardEq hcardSig
  set f : (Fin k → Finset (Fin n) × Fin n) × (∀ i, Equiv.Perm (Fin (m i)))
      → ((Σ i : Fin k, Fin (m i + 1)) ≃ Fin n) :=
    fun pq => if h : IsBlockData m pq.1
      then Equiv.ofBijective (h.placeFun pq.2)
        ((Fintype.bijective_iff_injective_and_card _).mpr
          ⟨h.placeFun_injective pq.2, by rw [hcardSig, Fintype.card_fin]⟩)
      else e₀ with hfdef
  -- blocks are recovered as images of the placement function
  have hblock : ∀ (ρ : Fin k → Finset (Fin n) × Fin n)
      (h : IsBlockData m ρ) (π : ∀ i, Equiv.Perm (Fin (m i))) (i : Fin k),
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
        (fun ρ => IsBlockData m ρ)) ×ˢ
      (Finset.univ : Finset (∀ i, Equiv.Perm (Fin (m i)))),
      ∀ pq₂ ∈ ((Finset.univ :
        Finset (Fin k → Finset (Fin n) × Fin n)).filter
          (fun ρ => IsBlockData m ρ)) ×ˢ
        (Finset.univ : Finset (∀ i, Equiv.Perm (Fin (m i)))),
      f pq₁ = f pq₂ → pq₁ = pq₂ := by
    intro pq₁ h₁ pq₂ h₂ hf
    obtain ⟨ρ₁, π₁⟩ := pq₁
    obtain ⟨ρ₂, π₂⟩ := pq₂
    rw [Finset.mem_product, Finset.mem_filter] at h₁ h₂
    have hb₁ : IsBlockData m ρ₁ := h₁.1.2
    have hb₂ : IsBlockData m ρ₂ := h₂.1.2
    rw [hfdef] at hf
    simp only [dif_pos hb₁, dif_pos hb₂] at hf
    have happ : ∀ x, hb₁.placeFun π₁ x = hb₂.placeFun π₂ x := by
      intro x
      simpa using DFunLike.congr_fun hf x
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
        (fun ρ => IsBlockData m ρ)).card * ∏ i, (m i).factorial
      = (((Finset.univ : Finset (Fin k → Finset (Fin n) × Fin n)).filter
          (fun ρ => IsBlockData m ρ)) ×ˢ
          (Finset.univ : Finset (∀ i, Equiv.Perm (Fin (m i))))).card := by
        rw [Finset.card_product, Finset.card_univ]
        congr 1
        rw [Fintype.card_pi]
        exact (Finset.prod_congr rfl fun i _ => by
          rw [Fintype.card_perm, Fintype.card_fin]).symm
    _ ≤ (Finset.univ :
          Finset ((Σ i : Fin k, Fin (m i + 1)) ≃ Fin n)).card :=
        Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _)
          (fun a ha b hb h => hinjOn a (Finset.mem_coe.mp ha) b
            (Finset.mem_coe.mp hb) h)
    _ = n.factorial := by
        rw [Finset.card_univ, Fintype.card_equiv e₀, hcardSig]

end BlockCount

end YangMills.KP
