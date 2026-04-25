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

/-! ### Ternary displacement coding -/

/-- The ternary code for a one-coordinate displacement.  The intended inputs
are `-1`, `0`, and `1`; all other integers collapse to the last code. -/
noncomputable def intTernaryCode (z : ℤ) : Fin 3 :=
  if z = -1 then 0 else if z = 0 then 1 else 2

/-- `intTernaryCode` is injective on the intended alphabet `{-1, 0, 1}`. -/
theorem intTernaryCode_inj_on_unit
    {a b : ℤ}
    (ha : a = -1 ∨ a = 0 ∨ a = 1)
    (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (h : intTernaryCode a = intTernaryCode b) :
    a = b := by
  rcases ha with ha | ha | ha <;>
    rcases hb with hb | hb | hb <;>
    subst ha <;> subst hb <;>
    simp [intTernaryCode] at h ⊢

/-- Ternary displacement code for a site-neighborhood element. -/
noncomputable def siteNeighborTernaryCode
    {d L : ℕ} [NeZero d] [NeZero L]
    (x : FinBox d L)
    (y : {y : FinBox d L // y ∈ siteNeighborBall d L x}) :
    Fin d → Fin 3 :=
  fun i => intTernaryCode (siteDisplacement x y.1 i)

/-- Equality of all displacement coordinates from the same base site forces
equality of the target finite-box sites. -/
theorem finBox_eq_of_siteDisplacement_eq
    {d L : ℕ} {x y z : FinBox d L}
    (h : ∀ i, siteDisplacement x y i = siteDisplacement x z i) :
    y = z := by
  funext i
  have hi := h i
  unfold siteDisplacement at hi
  have hyz : ((y i : ℤ) : ℤ) = ((z i : ℤ) : ℤ) := by
    omega
  exact Fin.ext (by exact_mod_cast hyz)

/-- The ternary displacement code is injective once all site-neighbor
displacements have coordinates in `{-1, 0, 1}`. -/
theorem siteNeighborTernaryCode_injective
    {d L : ℕ} [NeZero d] [NeZero L]
    (x : FinBox d L)
    (hcoord : ∀ y ∈ siteNeighborBall d L x, ∀ i : Fin d,
      siteDisplacement x y i = -1 ∨
        siteDisplacement x y i = 0 ∨
        siteDisplacement x y i = 1) :
    Function.Injective (siteNeighborTernaryCode x) := by
  intro a b h
  apply Subtype.ext
  apply finBox_eq_of_siteDisplacement_eq
  intro i
  exact intTernaryCode_inj_on_unit
    (hcoord a.1 a.2 i) (hcoord b.1 b.2 i)
    (congrFun h i)

/-- A coordinate-wise ternary displacement proof gives the uniform
`3^d` site-neighborhood bound. -/
theorem siteNeighborBallBoundDim_of_ternary_displacements
    {d : ℕ} [NeZero d]
    (hcoord : ∀ {L : ℕ} [NeZero L] (x : FinBox d L)
      (y : FinBox d L), y ∈ siteNeighborBall d L x → ∀ i : Fin d,
        siteDisplacement x y i = -1 ∨
          siteDisplacement x y i = 0 ∨
          siteDisplacement x y i = 1) :
    SiteNeighborBallBoundDim d (3 ^ d) := by
  apply siteNeighborBallBoundDim_of_injective_code
    (α := Fin d → Fin 3)
  · simp
  · intro L _ x
    exact ⟨siteNeighborTernaryCode x,
      siteNeighborTernaryCode_injective x (hcoord x)⟩

/-! ### Coordinate bound from unit site distance -/

/-- If an integer has real square at most one, it is one of `-1, 0, 1`. -/
theorem int_eq_neg_one_or_zero_or_one_of_sq_le_one
    (z : ℤ) (hz : ((z : ℝ) ^ 2) ≤ 1) :
    z = -1 ∨ z = 0 ∨ z = 1 := by
  have h_le : z ≤ 1 := by
    by_contra h
    have hzge : (2 : ℤ) ≤ z := by omega
    have hzge_real : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzge
    nlinarith
  have h_ge : -1 ≤ z := by
    by_contra h
    have hzle : z ≤ (-2 : ℤ) := by omega
    have hzle_real : (z : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast hzle
    nlinarith
  omega

/-- Unit site distance forces each integer displacement coordinate to have
real square at most one. -/
theorem siteDisplacement_sq_le_one_of_siteLatticeDist_le_one
    {d L : ℕ} (x y : FinBox d L)
    (hdist : siteLatticeDist x y ≤ 1) (i : Fin d) :
    ((siteDisplacement x y i : ℝ) ^ 2) ≤ 1 := by
  let S : ℝ := ∑ j, ((siteDisplacement x y j : ℝ) ^ 2)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hS_le_one : S ≤ 1 := by
    unfold siteLatticeDist latticeDist at hdist
    dsimp [S]
    have hsqrt_sq_le : (Real.sqrt S) ^ 2 ≤ (1 : ℝ) ^ 2 := by
      nlinarith [Real.sqrt_nonneg S, hdist]
    simpa [Real.sq_sqrt hS_nonneg] using hsqrt_sq_le
  have hterm_le_sum :
      ((siteDisplacement x y i : ℝ) ^ 2) ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin d)))
      (a := i)
      (f := fun j => ((siteDisplacement x y j : ℝ) ^ 2))
      (fun _ _ => by positivity) (Finset.mem_univ i)
  exact hterm_le_sum.trans hS_le_one

/-- Unit site distance forces every displacement coordinate to lie in the
ternary alphabet `{-1, 0, 1}`. -/
theorem siteDisplacement_mem_unit_of_siteLatticeDist_le_one
    {d L : ℕ} (x y : FinBox d L)
    (hdist : siteLatticeDist x y ≤ 1) (i : Fin d) :
    siteDisplacement x y i = -1 ∨
      siteDisplacement x y i = 0 ∨
      siteDisplacement x y i = 1 :=
  int_eq_neg_one_or_zero_or_one_of_sq_le_one _
    (siteDisplacement_sq_le_one_of_siteLatticeDist_le_one x y hdist i)

/-- Concrete uniform `3^d` site-neighborhood bound. -/
theorem siteNeighborBallBoundDim_ternary
    {d : ℕ} [NeZero d] :
    SiteNeighborBallBoundDim d (3 ^ d) := by
  apply siteNeighborBallBoundDim_of_ternary_displacements
  intro L _ x y hy i
  exact siteDisplacement_mem_unit_of_siteLatticeDist_le_one x y
    (Finset.mem_filter.mp hy).2 i

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

/-- Concrete fixed-dimension plaquette-graph degree bound obtained from the
ternary site-neighborhood code. -/
theorem plaquetteGraph_degreeBoundDim_ternary
    {d : ℕ} [NeZero d] :
    PlaquetteGraphDegreeBoundDim d
      ((3 ^ d) * Fintype.card (Fin d) * Fintype.card (Fin d)) :=
  plaquetteGraph_degreeBoundDim_of_siteNeighborBallBoundDim
    siteNeighborBallBoundDim_ternary

/-- Physical four-dimensional plaquette-graph degree bound from the ternary
site-neighborhood code. -/
theorem plaquetteGraph_degreeBoundDim_physical_ternary :
    PlaquetteGraphDegreeBoundDim physicalClayDimension 1296 := by
  intro L _ p
  have h :=
    (plaquetteGraph_degreeBoundDim_ternary
      (d := physicalClayDimension) (L := L) p)
  have h' :
      (plaquetteGraph physicalClayDimension L).degree p ≤ 81 * 4 * 4 := by
    simpa [physicalClayDimension, Fintype.card_fin] using h
  norm_num at h'
  exact h'

/-- Direct application form of the physical local branching bound. -/
theorem plaquetteGraph_degree_le_physical_ternary
    {L : ℕ} [NeZero L]
    (p : ConcretePlaquette physicalClayDimension L) :
    (plaquetteGraph physicalClayDimension L).degree p ≤ 1296 :=
  plaquetteGraph_degreeBoundDim_physical_ternary p

/-- Generic neighbor-finset cardinality form of the ternary plaquette-graph
branching bound.  This is the shape used by BFS/tree-count arguments. -/
theorem plaquetteGraph_neighborFinset_card_le_ternary
    {d L : ℕ} [NeZero d] [NeZero L]
    (p : ConcretePlaquette d L) :
    ((plaquetteGraph d L).neighborFinset p).card ≤
      (3 ^ d) * Fintype.card (Fin d) * Fintype.card (Fin d) := by
  rw [SimpleGraph.card_neighborFinset_eq_degree]
  exact plaquetteGraph_degreeBoundDim_ternary p

/-- Physical four-dimensional neighbor-finset cardinality bound. -/
theorem plaquetteGraph_neighborFinset_card_le_physical_ternary
    {L : ℕ} [NeZero L]
    (p : ConcretePlaquette physicalClayDimension L) :
    ((plaquetteGraph physicalClayDimension L).neighborFinset p).card ≤ 1296 := by
  rw [SimpleGraph.card_neighborFinset_eq_degree]
  exact plaquetteGraph_degree_le_physical_ternary p

/-! ### Branching-bound interface -/

/-- Fixed-dimension uniform branching bound for the plaquette graph, stated in
the neighbor-finset form used by BFS/tree-count arguments. -/
def PlaquetteGraphBranchingBoundDim (d D : ℕ) [NeZero d] : Prop :=
  ∀ {L : ℕ} [NeZero L] (p : ConcretePlaquette d L),
    ((plaquetteGraph d L).neighborFinset p).card ≤ D

/-- A degree bound gives the equivalent neighbor-finset branching bound. -/
theorem plaquetteGraph_branchingBoundDim_of_degreeBoundDim
    {d D : ℕ} [NeZero d]
    (hD : PlaquetteGraphDegreeBoundDim d D) :
    PlaquetteGraphBranchingBoundDim d D := by
  intro L _ p
  rw [SimpleGraph.card_neighborFinset_eq_degree]
  exact hD p

/-- Generic ternary plaquette-graph branching bound. -/
theorem plaquetteGraph_branchingBoundDim_ternary
    {d : ℕ} [NeZero d] :
    PlaquetteGraphBranchingBoundDim d
      ((3 ^ d) * Fintype.card (Fin d) * Fintype.card (Fin d)) :=
  plaquetteGraph_branchingBoundDim_of_degreeBoundDim
    plaquetteGraph_degreeBoundDim_ternary

/-- Physical four-dimensional plaquette-graph branching bound. -/
theorem plaquetteGraph_branchingBoundDim_physical_ternary :
    PlaquetteGraphBranchingBoundDim physicalClayDimension 1296 :=
  plaquetteGraph_branchingBoundDim_of_degreeBoundDim
    plaquetteGraph_degreeBoundDim_physical_ternary

/-- Direct application form of the physical branching bound. -/
theorem plaquetteGraph_branching_le_physical_ternary
    {L : ℕ} [NeZero L]
    (p : ConcretePlaquette physicalClayDimension L) :
    ((plaquetteGraph physicalClayDimension L).neighborFinset p).card ≤ 1296 :=
  plaquetteGraph_branchingBoundDim_physical_ternary p

/-! ### Finite walk coding interface -/

/-- A graph walk of edge-length `n` starting at `p`, represented as a finite
sequence of `n+1` plaquettes.  This function representation is finite by
construction and is better suited to coding arguments than unrestricted
lists. -/
def PlaquetteWalk
    (d L n : ℕ) [NeZero d] [NeZero L]
    (p : ConcretePlaquette d L) : Type :=
  { path : Fin (n + 1) → ConcretePlaquette d L //
    path 0 = p ∧
      ∀ i : Fin n,
        (plaquetteGraph d L).Adj (path i.castSucc) (path i.succ) }

noncomputable instance plaquetteWalk_fintype
    (d L n : ℕ) [NeZero d] [NeZero L]
    (p : ConcretePlaquette d L) :
    Fintype (PlaquetteWalk d L n p) := by
  classical
  unfold PlaquetteWalk
  infer_instance

/-- A finite coding of length-`n` walks by words over `D` symbols gives the
expected `D^n` walk-count bound. -/
theorem plaquetteWalk_card_le_of_injective_code
    {d L n D : ℕ} [NeZero d] [NeZero L]
    (p : ConcretePlaquette d L)
    (code : PlaquetteWalk d L n p → (Fin n → Fin D))
    (hcode : Function.Injective code) :
    Fintype.card (PlaquetteWalk d L n p) ≤ D ^ n := by
  have hcard :=
    Fintype.card_le_of_injective code hcode
  simpa [Fintype.card_fun] using hcard

/-- Fixed-dimension walk-count bound driven by a word code of size `D`. -/
def PlaquetteWalkCodeBoundDim (d D : ℕ) [NeZero d] : Prop :=
  ∀ {L : ℕ} [NeZero L] (p : ConcretePlaquette d L) (n : ℕ),
    ∃ code : PlaquetteWalk d L n p → (Fin n → Fin D),
      Function.Injective code

/-- A fixed-dimension walk code gives a fixed-dimension `D^n` walk-count
bound. -/
theorem plaquetteWalk_card_le_of_codeBoundDim
    {d D : ℕ} [NeZero d]
    (hcode : PlaquetteWalkCodeBoundDim d D)
    {L : ℕ} [NeZero L] (p : ConcretePlaquette d L) (n : ℕ) :
    Fintype.card (PlaquetteWalk d L n p) ≤ D ^ n := by
  obtain ⟨code, hinj⟩ := hcode p n
  exact plaquetteWalk_card_le_of_injective_code p code hinj

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
#print axioms intTernaryCode_inj_on_unit
#print axioms finBox_eq_of_siteDisplacement_eq
#print axioms siteNeighborTernaryCode_injective
#print axioms siteNeighborBallBoundDim_of_ternary_displacements
#print axioms int_eq_neg_one_or_zero_or_one_of_sq_le_one
#print axioms siteDisplacement_sq_le_one_of_siteLatticeDist_le_one
#print axioms siteDisplacement_mem_unit_of_siteLatticeDist_le_one
#print axioms siteNeighborBallBoundDim_ternary
#print axioms plaquetteGraph_degreeBoundDim_of_siteNeighborBallBoundDim
#print axioms plaquetteGraph_degreeBoundDim_ternary
#print axioms plaquetteGraph_degreeBoundDim_physical_ternary
#print axioms plaquetteGraph_degree_le_physical_ternary
#print axioms plaquetteGraph_neighborFinset_card_le_ternary
#print axioms plaquetteGraph_neighborFinset_card_le_physical_ternary
#print axioms plaquetteGraph_branchingBoundDim_of_degreeBoundDim
#print axioms plaquetteGraph_branchingBoundDim_ternary
#print axioms plaquetteGraph_branchingBoundDim_physical_ternary
#print axioms plaquetteGraph_branching_le_physical_ternary
#print axioms plaquetteWalk_card_le_of_injective_code
#print axioms plaquetteWalk_card_le_of_codeBoundDim
#print axioms plaquetteGraph_isChain_of_nodup_siteLatticeDist_isChain
#print axioms polymerConnected_exists_plaquetteGraph_chain
#print axioms plaquetteGraph_reachable_of_chain_endpoints
#print axioms polymerConnected_plaquetteGraph_reachable
#print axioms plaquetteGraph_induce_reachable_of_chain_endpoints
#print axioms polymerConnected_plaquetteGraph_induce_reachable
#print axioms polymerConnected_plaquetteGraph_induce_preconnected

end YangMills
