/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.ClayCore.ConnectingClusterCountExp

/-!
# Lattice-animal count scaffolding

This module starts the concrete F3-count route by putting the plaquette
adjacency graph used by the lattice-animal argument into the main Lean tree.

The final target is a uniform witness for
`ShiftedConnectingClusterCountBoundExp`.  The definitions here are deliberately
small: they isolate the graph and the symmetry facts needed to translate
`PolymerConnected` into graph-connected finite sets.
-/

namespace YangMills

open scoped Classical

/-! ### Plaquette adjacency graph -/

/-- Symmetry of the concrete lattice distance between finite-box sites. -/
theorem siteLatticeDist_symm {d N : ℕ} (p q : FinBox d N) :
    siteLatticeDist p q = siteLatticeDist q p := by
  rw [siteLatticeDist_eq_dist, siteLatticeDist_eq_dist, dist_comm]

/-- The plaquette graph whose edges are nearest-neighbour base-site
relations.  This is the graph form of the `PolymerConnected` adjacency
predicate used by the F3 count frontier. -/
def plaquetteGraph (d L : ℕ) [NeZero d] [NeZero L] :
    SimpleGraph (ConcretePlaquette d L) where
  Adj p q := p ≠ q ∧ siteLatticeDist p.site q.site ≤ 1
  symm := by
    intro p q h
    exact ⟨h.1.symm, by rw [siteLatticeDist_symm]; exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance plaquetteGraph_decidableRel
    (d L : ℕ) [NeZero d] [NeZero L] :
    DecidableRel (plaquetteGraph d L).Adj := by
  classical
  intro p q
  unfold plaquetteGraph
  infer_instance

/-- Adjacency in `plaquetteGraph` exposes the site-distance bound used by
`PolymerConnected`. -/
theorem plaquetteGraph_adj_siteLatticeDist_le_one
    {d L : ℕ} [NeZero d] [NeZero L]
    {p q : ConcretePlaquette d L}
    (h : (plaquetteGraph d L).Adj p q) :
    siteLatticeDist p.site q.site ≤ 1 :=
  h.2

/-- The graph adjacency constructor from distinct plaquettes and the
site-distance bound. -/
theorem plaquetteGraph_adj_of_ne_of_siteLatticeDist_le_one
    {d L : ℕ} [NeZero d] [NeZero L]
    {p q : ConcretePlaquette d L}
    (hne : p ≠ q) (hdist : siteLatticeDist p.site q.site ≤ 1) :
    (plaquetteGraph d L).Adj p q :=
  ⟨hne, hdist⟩

/-! ### Local neighbor enumeration -/

/-- The finite set of plaquettes whose base site is within graph range of `p`.
This is the local bucket that will later be bounded uniformly in the volume. -/
noncomputable def plaquetteSiteBall (d L : ℕ) [NeZero d] [NeZero L]
    (p : ConcretePlaquette d L) : Finset (ConcretePlaquette d L) :=
  (Finset.univ.filter fun q => siteLatticeDist p.site q.site ≤ 1)

/-- The finite set of base sites within graph range of `x`. -/
noncomputable def siteNeighborBall (d L : ℕ) [NeZero d] [NeZero L]
    (x : FinBox d L) : Finset (FinBox d L) :=
  (Finset.univ.filter fun y => siteLatticeDist x y ≤ 1)

/-- The `plaquetteGraph` neighbor finset is exactly the concrete local bucket
with `p` itself removed. -/
theorem plaquetteGraph_neighborFinset_eq_filter
    {d L : ℕ} [NeZero d] [NeZero L]
    (p : ConcretePlaquette d L) :
    (plaquetteGraph d L).neighborFinset p =
      (Finset.univ.filter
        fun q : ConcretePlaquette d L =>
          q ≠ p ∧ siteLatticeDist p.site q.site ≤ 1) := by
  ext q
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
    Finset.mem_univ, true_and, plaquetteGraph]
  exact ⟨fun h => ⟨fun hqp => h.1 hqp.symm, h.2⟩,
    fun h => ⟨fun hpq => h.1 hpq.symm, h.2⟩⟩

/-- Every graph-neighbour of `p` lies in the site-distance local bucket. -/
theorem plaquetteGraph_neighborFinset_subset_siteBall
    {d L : ℕ} [NeZero d] [NeZero L]
    (p : ConcretePlaquette d L) :
    (plaquetteGraph d L).neighborFinset p ⊆ plaquetteSiteBall d L p := by
  intro q hq
  rw [plaquetteGraph_neighborFinset_eq_filter] at hq
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ q, (Finset.mem_filter.mp hq).2.2⟩

/-- The degree of a plaquette in `plaquetteGraph` is bounded by the cardinality
of the corresponding site-distance local bucket. -/
theorem plaquetteGraph_degree_le_siteBall_card
    {d L : ℕ} [NeZero d] [NeZero L]
    (p : ConcretePlaquette d L) :
    (plaquetteGraph d L).degree p ≤ (plaquetteSiteBall d L p).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_le_card (plaquetteGraph_neighborFinset_subset_siteBall p)

/-- The plaquette local bucket injects into nearby base sites together with two
orientation choices.  This isolates the remaining geometric site-neighborhood
count from the purely orientational factor. -/
theorem plaquetteSiteBall_card_le_siteNeighborBall_card_mul_dir_sq
    {d L : ℕ} [NeZero d] [NeZero L]
    (p : ConcretePlaquette d L) :
    (plaquetteSiteBall d L p).card ≤
      (siteNeighborBall d L p.site).card *
        Fintype.card (Fin d) * Fintype.card (Fin d) := by
  let f :
      {q : ConcretePlaquette d L // q ∈ plaquetteSiteBall d L p} →
        (siteNeighborBall d L p.site) × Fin d × Fin d :=
    fun q =>
      (⟨q.1.site, by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ q.1.site, (Finset.mem_filter.mp q.2).2⟩⟩,
        q.1.dir1, q.1.dir2)
  have hf : Function.Injective f := by
    intro a b h
    cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        have hsite :
            (f ⟨a, ha⟩).1 = (f ⟨b, hb⟩).1 := congrArg Prod.fst h
        have hdir1 :
            (f ⟨a, ha⟩).2.1 = (f ⟨b, hb⟩).2.1 :=
          congrArg (fun z => z.2.1) h
        have hdir2 :
            (f ⟨a, ha⟩).2.2 = (f ⟨b, hb⟩).2.2 :=
          congrArg (fun z => z.2.2) h
        simp only [f] at hsite hdir1 hdir2
        have hsite_val : a.site = b.site := congrArg Subtype.val hsite
        apply Subtype.ext
        cases a with
        | mk as ai aj ah =>
          cases b with
          | mk bs bi bj bh =>
            simp only at hsite_val hdir1 hdir2
            subst bs
            subst bi
            subst bj
            rfl
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, mul_assoc] using hcard

/-! ### Local branching bound interface -/

/-- Fixed-dimension uniform bound on the site-neighborhood bucket. -/
def SiteNeighborBallBoundDim (d B : ℕ) [NeZero d] : Prop :=
  ∀ {L : ℕ} [NeZero L] (x : FinBox d L),
    (siteNeighborBall d L x).card ≤ B

/-- A site-neighborhood bucket is bounded by any finite type into which it
injects. -/
theorem siteNeighborBall_card_le_of_injective_code
    {d L : ℕ} [NeZero d] [NeZero L]
    (x : FinBox d L)
    {α : Type} [Fintype α]
    (code : {y : FinBox d L // y ∈ siteNeighborBall d L x} → α)
    (hcode : Function.Injective code) :
    (siteNeighborBall d L x).card ≤ Fintype.card α := by
  simpa using Fintype.card_le_of_injective code hcode

/-- A volume-uniform finite coding of site-neighborhood buckets gives a
fixed-dimension site-neighborhood bound. -/
theorem siteNeighborBallBoundDim_of_injective_code
    {d B : ℕ} [NeZero d]
    {α : Type} [Fintype α]
    (hα : Fintype.card α ≤ B)
    (hcode : ∀ {L : ℕ} [NeZero L] (x : FinBox d L),
      ∃ code : {y : FinBox d L // y ∈ siteNeighborBall d L x} → α,
        Function.Injective code) :
    SiteNeighborBallBoundDim d B := by
  intro L _ x
  obtain ⟨code, hinj⟩ := hcode x
  exact (siteNeighborBall_card_le_of_injective_code x code hinj).trans hα

/-- Fixed-dimension uniform degree bound for `plaquetteGraph`. -/
def PlaquetteGraphDegreeBoundDim (d D : ℕ) [NeZero d] : Prop :=
  ∀ {L : ℕ} [NeZero L] (p : ConcretePlaquette d L),
    (plaquetteGraph d L).degree p ≤ D

/-- A uniform site-neighborhood bound gives a uniform plaquette-graph degree
bound, with the explicit orientation overhead `d*d`. -/
theorem plaquetteGraph_degreeBoundDim_of_siteNeighborBallBoundDim
    {d B : ℕ} [NeZero d]
    (hB : SiteNeighborBallBoundDim d B) :
    PlaquetteGraphDegreeBoundDim d (B * Fintype.card (Fin d) * Fintype.card (Fin d)) := by
  intro L _ p
  exact (plaquetteGraph_degree_le_siteBall_card p).trans
    ((plaquetteSiteBall_card_le_siteNeighborBall_card_mul_dir_sq p).trans
      (Nat.mul_le_mul_right (Fintype.card (Fin d))
        (Nat.mul_le_mul_right (Fintype.card (Fin d)) (hB p.site))))

/-- A nodup `PolymerConnected`-style site-distance chain is a chain in the
plaquette adjacency graph. -/
theorem plaquetteGraph_isChain_of_nodup_siteLatticeDist_isChain
    {d L : ℕ} [NeZero d] [NeZero L] :
    ∀ (path : List (ConcretePlaquette d L)),
      path.Nodup →
      List.IsChain (fun a b => siteLatticeDist a.site b.site ≤ 1) path →
      List.IsChain (plaquetteGraph d L).Adj path := by
  intro path
  induction path with
  | nil =>
      intro _ _
      exact List.IsChain.nil
  | cons a rest ih =>
      intro hnodup hchain
      match rest, hchain with
      | [], _ =>
          exact List.IsChain.singleton (R := (plaquetteGraph d L).Adj) a
      | b :: rest', List.IsChain.cons_cons hdist htail =>
          have hnot_mem : a ∉ b :: rest' := (List.nodup_cons.mp hnodup).1
          have htail_nodup : (b :: rest').Nodup := (List.nodup_cons.mp hnodup).2
          have hne : a ≠ b := by
            intro hab
            exact hnot_mem (by simp [hab])
          exact List.IsChain.cons_cons
            (plaquetteGraph_adj_of_ne_of_siteLatticeDist_le_one hne hdist)
            (ih htail_nodup htail)

/-- `PolymerConnected` supplies graph chains in `plaquetteGraph`, still
carrying the original path endpoints, nodup proof, and containment in the
polymer. -/
theorem polymerConnected_exists_plaquetteGraph_chain
    {d L : ℕ} [NeZero d] [NeZero L]
    {X : Finset (ConcretePlaquette d L)}
    {p q : ConcretePlaquette d L}
    (hconn : PolymerConnected X) (hpX : p ∈ X) (hqX : q ∈ X) :
    ∃ path : List (ConcretePlaquette d L),
      path.head? = some p ∧
      path.getLast? = some q ∧
      path.Nodup ∧
      (∀ x ∈ path, x ∈ X) ∧
      List.IsChain (plaquetteGraph d L).Adj path := by
  obtain ⟨path, hhead, hlast, hnodup, hsub, hchain⟩ := hconn p hpX q hqX
  exact ⟨path, hhead, hlast, hnodup, hsub,
    plaquetteGraph_isChain_of_nodup_siteLatticeDist_isChain path hnodup hchain⟩

/-- A `plaquetteGraph` chain with recorded endpoints gives graph reachability
between those endpoints. -/
theorem plaquetteGraph_reachable_of_chain_endpoints
    {d L : ℕ} [NeZero d] [NeZero L] :
    ∀ {p q : ConcretePlaquette d L} (path : List (ConcretePlaquette d L)),
      path.head? = some p →
      path.getLast? = some q →
      List.IsChain (plaquetteGraph d L).Adj path →
      (plaquetteGraph d L).Reachable p q := by
  intro p q path
  induction path generalizing p q with
  | nil =>
      intro hhead _ _
      simp at hhead
  | cons a rest ih =>
      intro hhead hlast hchain
      have hap : a = p := by
        rw [List.head?_cons, Option.some.injEq] at hhead
        exact hhead
      subst hap
      match rest, hchain, hlast with
      | [], _, hlast =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst hlast
          exact SimpleGraph.Reachable.refl _
      | b :: rest', List.IsChain.cons_cons hpb htail, hlast =>
          have hhead' : (b :: rest').head? = some b := by simp
          have hlast' : (b :: rest').getLast? = some q := by
            simpa [List.getLast?] using hlast
          exact (SimpleGraph.Adj.reachable hpb).trans
            (ih hhead' hlast' htail)

/-- `PolymerConnected` implies reachability in the plaquette graph. -/
theorem polymerConnected_plaquetteGraph_reachable
    {d L : ℕ} [NeZero d] [NeZero L]
    {X : Finset (ConcretePlaquette d L)}
    {p q : ConcretePlaquette d L}
    (hconn : PolymerConnected X) (hpX : p ∈ X) (hqX : q ∈ X) :
    (plaquetteGraph d L).Reachable p q := by
  obtain ⟨path, hhead, hlast, _, _, hchain⟩ :=
    polymerConnected_exists_plaquetteGraph_chain hconn hpX hqX
  exact plaquetteGraph_reachable_of_chain_endpoints path hhead hlast hchain

/-- A `plaquetteGraph` chain contained in `X` gives reachability in the
subgraph induced by `X`. -/
theorem plaquetteGraph_induce_reachable_of_chain_endpoints
    {d L : ℕ} [NeZero d] [NeZero L]
    {X : Finset (ConcretePlaquette d L)} :
    ∀ {p q : ConcretePlaquette d L}
      (hpX : p ∈ X) (hqX : q ∈ X)
      (path : List (ConcretePlaquette d L)),
      path.head? = some p →
      path.getLast? = some q →
      (∀ x ∈ path, x ∈ X) →
      List.IsChain (plaquetteGraph d L).Adj path →
      ((plaquetteGraph d L).induce {x | x ∈ X}).Reachable
        ⟨p, hpX⟩ ⟨q, hqX⟩ := by
  intro p q hpX hqX path
  induction path generalizing p q with
  | nil =>
      intro hhead _ _ _
      simp at hhead
  | cons a rest ih =>
      intro hhead hlast hsub hchain
      have hap : a = p := by
        rw [List.head?_cons, Option.some.injEq] at hhead
        exact hhead
      subst hap
      match rest, hchain, hlast with
      | [], _, hlast =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst hlast
          exact SimpleGraph.Reachable.refl _
      | b :: rest', List.IsChain.cons_cons hpb htail, hlast =>
          have hbX : b ∈ X := hsub b (by simp)
          have hhead' : (b :: rest').head? = some b := by simp
          have hlast' : (b :: rest').getLast? = some q := by
            simpa [List.getLast?] using hlast
          have hsub' : ∀ x ∈ b :: rest', x ∈ X := by
            intro x hx
            exact hsub x (by simp [hx])
          have hind :
              ((plaquetteGraph d L).induce {x | x ∈ X}).Adj
                ⟨_, hpX⟩ ⟨b, hbX⟩ := by
            exact SimpleGraph.induce_adj.mpr hpb
          exact (SimpleGraph.Adj.reachable hind).trans
            (ih hbX hqX hhead' hlast' hsub' htail)

/-- `PolymerConnected X` gives reachability in the subgraph of
`plaquetteGraph` induced by `X`. -/
theorem polymerConnected_plaquetteGraph_induce_reachable
    {d L : ℕ} [NeZero d] [NeZero L]
    {X : Finset (ConcretePlaquette d L)}
    {p q : ConcretePlaquette d L}
    (hconn : PolymerConnected X) (hpX : p ∈ X) (hqX : q ∈ X) :
    ((plaquetteGraph d L).induce {x | x ∈ X}).Reachable
      ⟨p, hpX⟩ ⟨q, hqX⟩ := by
  obtain ⟨path, hhead, hlast, _, hsub, hchain⟩ :=
    polymerConnected_exists_plaquetteGraph_chain hconn hpX hqX
  exact plaquetteGraph_induce_reachable_of_chain_endpoints
    hpX hqX path hhead hlast hsub hchain

/-- `PolymerConnected X` gives preconnectedness of the plaquette graph induced
by `X`.  This is the graph-theoretic connected-subset direction needed by the
lattice-animal counting interface. -/
theorem polymerConnected_plaquetteGraph_induce_preconnected
    {d L : ℕ} [NeZero d] [NeZero L]
    {X : Finset (ConcretePlaquette d L)}
    (hconn : PolymerConnected X) :
    ((plaquetteGraph d L).induce {x | x ∈ X}).Preconnected := by
  intro p q
  exact polymerConnected_plaquetteGraph_induce_reachable
    hconn p.property q.property

#print axioms siteLatticeDist_symm
#print axioms plaquetteGraph_adj_siteLatticeDist_le_one
#print axioms plaquetteGraph_adj_of_ne_of_siteLatticeDist_le_one
#print axioms plaquetteGraph_neighborFinset_eq_filter
#print axioms plaquetteGraph_neighborFinset_subset_siteBall
#print axioms plaquetteGraph_degree_le_siteBall_card
#print axioms plaquetteSiteBall_card_le_siteNeighborBall_card_mul_dir_sq
#print axioms siteNeighborBall_card_le_of_injective_code
#print axioms siteNeighborBallBoundDim_of_injective_code
#print axioms plaquetteGraph_degreeBoundDim_of_siteNeighborBallBoundDim
#print axioms plaquetteGraph_isChain_of_nodup_siteLatticeDist_isChain
#print axioms polymerConnected_exists_plaquetteGraph_chain
#print axioms plaquetteGraph_reachable_of_chain_endpoints
#print axioms polymerConnected_plaquetteGraph_reachable
#print axioms plaquetteGraph_induce_reachable_of_chain_endpoints
#print axioms polymerConnected_plaquetteGraph_induce_reachable
#print axioms polymerConnected_plaquetteGraph_induce_preconnected

end YangMills
