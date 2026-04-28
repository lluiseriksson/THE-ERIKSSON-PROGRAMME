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

/-! ### Neighbor-choice coding -/

/-- Any finset with at most `D` elements has a canonical injection into
`Fin D`, obtained by enumerating it as `Fin s.card` and casting along the
cardinality bound. -/
noncomputable def finsetCodeOfCardLe {α : Type} (s : Finset α) {D : ℕ}
    (hD : s.card ≤ D) : {x : α // x ∈ s} → Fin D :=
  fun x => Fin.castLE hD ((Finset.equivFin s) x)

/-- The canonical bounded-cardinality finset code is injective. -/
theorem finsetCodeOfCardLe_injective {α : Type} (s : Finset α) {D : ℕ}
    (hD : s.card ≤ D) :
    Function.Injective (finsetCodeOfCardLe s hD) := by
  intro a b h
  apply (Finset.equivFin s).injective
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [finsetCodeOfCardLe, Fin.castLE] using hv

/-- Fixed-dimension uniform finite coding of each plaquette neighbor finset. -/
def PlaquetteNeighborChoiceCodeBoundDim (d D : ℕ) [NeZero d] : Prop :=
  ∀ {L : ℕ} [NeZero L] (p : ConcretePlaquette d L),
    ∃ code : {q : ConcretePlaquette d L //
        q ∈ (plaquetteGraph d L).neighborFinset p} → Fin D,
      Function.Injective code

/-- A uniform branching bound produces a uniform finite neighbor-choice code. -/
theorem plaquetteNeighborChoiceCodeBoundDim_of_branchingBoundDim
    {d D : ℕ} [NeZero d]
    (hD : PlaquetteGraphBranchingBoundDim d D) :
    PlaquetteNeighborChoiceCodeBoundDim d D := by
  intro L _ p
  exact ⟨finsetCodeOfCardLe ((plaquetteGraph d L).neighborFinset p) (hD p),
    finsetCodeOfCardLe_injective ((plaquetteGraph d L).neighborFinset p) (hD p)⟩

/-- Physical four-dimensional plaquette neighbor choices have `1296` codes. -/
theorem plaquetteNeighborChoiceCodeBoundDim_physical_ternary :
    PlaquetteNeighborChoiceCodeBoundDim physicalClayDimension 1296 :=
  plaquetteNeighborChoiceCodeBoundDim_of_branchingBoundDim
    plaquetteGraph_branchingBoundDim_physical_ternary

/-- A global step-code function, injective on the actual neighbors of each
plaquette.  This non-dependent packaging is convenient for reconstructing
finite walks from their per-step codes. -/
def PlaquetteNeighborStepCodeBoundDim (d D : ℕ) [NeZero d] : Prop :=
  ∀ {L : ℕ} [NeZero L],
    ∃ code : ConcretePlaquette d L → ConcretePlaquette d L → Fin D,
      ∀ p, Set.InjOn (code p)
        {q | q ∈ (plaquetteGraph d L).neighborFinset p}

/-- Turn dependent neighbor-choice codes into a global step-code function by
using an arbitrary default value off the neighbor set. -/
noncomputable def plaquetteNeighborStepCodeOfChoice
    {d D : ℕ} [NeZero d] [NeZero D]
    (hchoice : PlaquetteNeighborChoiceCodeBoundDim d D)
    {L : ℕ} [NeZero L] :
    ConcretePlaquette d L → ConcretePlaquette d L → Fin D :=
  fun p q =>
    if hq : q ∈ (plaquetteGraph d L).neighborFinset p then
      Classical.choose (hchoice p) ⟨q, hq⟩
    else 0

/-- The step-code extracted from dependent neighbor-choice codes is injective
on the actual neighbor set. -/
theorem plaquetteNeighborStepCodeOfChoice_injOn
    {d D : ℕ} [NeZero d] [NeZero D]
    (hchoice : PlaquetteNeighborChoiceCodeBoundDim d D)
    {L : ℕ} [NeZero L] (p : ConcretePlaquette d L) :
    Set.InjOn (plaquetteNeighborStepCodeOfChoice hchoice p)
      {q | q ∈ (plaquetteGraph d L).neighborFinset p} := by
  intro q hq r hr h
  have hq' : q ∈ (plaquetteGraph d L).neighborFinset p := hq
  have hr' : r ∈ (plaquetteGraph d L).neighborFinset p := hr
  have hinj := Classical.choose_spec (hchoice p)
  unfold plaquetteNeighborStepCodeOfChoice at h
  rw [dif_pos hq', dif_pos hr'] at h
  have hsub :
      (⟨q, hq'⟩ :
        {q : ConcretePlaquette d L // q ∈ (plaquetteGraph d L).neighborFinset p}) =
        ⟨r, hr'⟩ := by
    exact hinj h
  exact congrArg Subtype.val hsub

/-- Dependent neighbor-choice codes give global step codes. -/
theorem plaquetteNeighborStepCodeBoundDim_of_choiceCodeBoundDim
    {d D : ℕ} [NeZero d] [NeZero D]
    (hchoice : PlaquetteNeighborChoiceCodeBoundDim d D) :
    PlaquetteNeighborStepCodeBoundDim d D := by
  intro L _
  exact ⟨plaquetteNeighborStepCodeOfChoice hchoice,
    plaquetteNeighborStepCodeOfChoice_injOn hchoice⟩

/-- A uniform branching bound gives global step codes. -/
theorem plaquetteNeighborStepCodeBoundDim_of_branchingBoundDim
    {d D : ℕ} [NeZero d] [NeZero D]
    (hD : PlaquetteGraphBranchingBoundDim d D) :
    PlaquetteNeighborStepCodeBoundDim d D :=
  plaquetteNeighborStepCodeBoundDim_of_choiceCodeBoundDim
    (plaquetteNeighborChoiceCodeBoundDim_of_branchingBoundDim hD)

/-- Physical four-dimensional plaquette steps have a global `1296`-code. -/
theorem plaquetteNeighborStepCodeBoundDim_physical_ternary :
    PlaquetteNeighborStepCodeBoundDim physicalClayDimension 1296 :=
  plaquetteNeighborStepCodeBoundDim_of_branchingBoundDim
    plaquetteGraph_branchingBoundDim_physical_ternary

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

/-- Code a finite plaquette walk by the global step-code at each edge. -/
noncomputable def plaquetteWalkCodeOfStepCode
    {d D : ℕ} [NeZero d]
    (hstep : PlaquetteNeighborStepCodeBoundDim d D)
    {L : ℕ} [NeZero L] (p : ConcretePlaquette d L) (n : ℕ) :
    PlaquetteWalk d L n p → (Fin n → Fin D) :=
  let code := Classical.choose (hstep (L := L))
  fun w i => code (w.1 i.castSucc) (w.1 i.succ)

/-- The per-step code of a finite walk is injective: the start point is fixed,
and each next plaquette is recovered from the current plaquette by local
injectivity on the neighbor set. -/
theorem plaquetteWalkCodeOfStepCode_injective
    {d D : ℕ} [NeZero d]
    (hstep : PlaquetteNeighborStepCodeBoundDim d D)
    {L : ℕ} [NeZero L] (p : ConcretePlaquette d L) (n : ℕ) :
    Function.Injective (plaquetteWalkCodeOfStepCode hstep p n) := by
  intro a b h
  apply Subtype.ext
  funext j
  refine Fin.induction ?zero ?succ j
  · exact a.2.1.trans b.2.1.symm
  · intro i hcur
    have hcode := Classical.choose_spec (hstep (L := L))
    have hinj := hcode (b.1 i.castSucc)
    have hstepEq := congrFun h i
    dsimp [plaquetteWalkCodeOfStepCode] at hstepEq
    have ha : a.1 i.succ ∈ (plaquetteGraph d L).neighborFinset (b.1 i.castSucc) := by
      rw [← hcur]
      exact
        (SimpleGraph.mem_neighborFinset
          (plaquetteGraph d L) (a.1 i.castSucc) (a.1 i.succ)).mpr
          (a.2.2 i)
    have hb : b.1 i.succ ∈ (plaquetteGraph d L).neighborFinset (b.1 i.castSucc) :=
      (SimpleGraph.mem_neighborFinset
        (plaquetteGraph d L) (b.1 i.castSucc) (b.1 i.succ)).mpr
        (b.2.2 i)
    rw [hcur] at hstepEq
    exact hinj ha hb hstepEq

/-- A global neighbor step-code gives a finite-walk word code. -/
theorem plaquetteWalkCodeBoundDim_of_neighborStepCodeBoundDim
    {d D : ℕ} [NeZero d]
    (hstep : PlaquetteNeighborStepCodeBoundDim d D) :
    PlaquetteWalkCodeBoundDim d D := by
  intro L _ p n
  exact ⟨plaquetteWalkCodeOfStepCode hstep p n,
    plaquetteWalkCodeOfStepCode_injective hstep p n⟩

/-- A dependent neighbor-choice code gives a finite-walk word code. -/
theorem plaquetteWalkCodeBoundDim_of_neighborChoiceCodeBoundDim
    {d D : ℕ} [NeZero d] [NeZero D]
    (hchoice : PlaquetteNeighborChoiceCodeBoundDim d D) :
    PlaquetteWalkCodeBoundDim d D :=
  plaquetteWalkCodeBoundDim_of_neighborStepCodeBoundDim
    (plaquetteNeighborStepCodeBoundDim_of_choiceCodeBoundDim hchoice)

/-- A uniform branching bound gives a finite-walk word code. -/
theorem plaquetteWalkCodeBoundDim_of_branchingBoundDim
    {d D : ℕ} [NeZero d] [NeZero D]
    (hD : PlaquetteGraphBranchingBoundDim d D) :
    PlaquetteWalkCodeBoundDim d D :=
  plaquetteWalkCodeBoundDim_of_neighborChoiceCodeBoundDim
    (plaquetteNeighborChoiceCodeBoundDim_of_branchingBoundDim hD)

/-- Physical four-dimensional plaquette walks have a `1296`-symbol word
code. -/
theorem plaquetteWalkCodeBoundDim_physical_ternary :
    PlaquetteWalkCodeBoundDim physicalClayDimension 1296 :=
  plaquetteWalkCodeBoundDim_of_branchingBoundDim
    plaquetteGraph_branchingBoundDim_physical_ternary

/-- Physical four-dimensional length-`n` plaquette walks from a fixed start
are bounded by `1296^n`. -/
theorem plaquetteWalk_card_le_physical_ternary
    {L : ℕ} [NeZero L]
    (p : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    Fintype.card (PlaquetteWalk physicalClayDimension L n p) ≤ 1296 ^ n :=
  plaquetteWalk_card_le_of_codeBoundDim
    plaquetteWalkCodeBoundDim_physical_ternary p n

/-! ### Walk-range decoder scaffold -/

/-- The finite set of vertices visited by a finite plaquette walk. -/
noncomputable def plaquetteWalkRangeFinset
    {d L n : ℕ} [NeZero d] [NeZero L]
    {p : ConcretePlaquette d L}
    (w : PlaquetteWalk d L n p) : Finset (ConcretePlaquette d L) :=
  Finset.univ.image w.1

/-- The start plaquette belongs to the visited set of a finite walk. -/
theorem plaquetteWalk_start_mem_rangeFinset
    {d L n : ℕ} [NeZero d] [NeZero L]
    {p : ConcretePlaquette d L}
    (w : PlaquetteWalk d L n p) :
    p ∈ plaquetteWalkRangeFinset w := by
  unfold plaquetteWalkRangeFinset
  refine Finset.mem_image.mpr ?_
  exact ⟨0, Finset.mem_univ _, w.2.1⟩

/-- Every indexed vertex of a finite walk belongs to its visited set. -/
theorem plaquetteWalk_vertex_mem_rangeFinset
    {d L n : ℕ} [NeZero d] [NeZero L]
    {p : ConcretePlaquette d L}
    (w : PlaquetteWalk d L n p) (i : Fin (n + 1)) :
    w.1 i ∈ plaquetteWalkRangeFinset w := by
  unfold plaquetteWalkRangeFinset
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- A length-`n` walk visits at most `n+1` plaquettes. -/
theorem plaquetteWalk_rangeFinset_card_le
    {d L n : ℕ} [NeZero d] [NeZero L]
    {p : ConcretePlaquette d L}
    (w : PlaquetteWalk d L n p) :
    (plaquetteWalkRangeFinset w).card ≤ n + 1 := by
  unfold plaquetteWalkRangeFinset
  have h :=
    Finset.card_image_le
      (s := (Finset.univ : Finset (Fin (n + 1)))) (f := w.1)
  simpa using h

/-! ### Connecting-cluster bucket to walk-count interface -/

/-- The exact connecting-cluster bucket used by the shifted F3 count frontier,
repackaged as a subtype for coding arguments. -/
def ConnectingClusterBucket
    (d L : ℕ) [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ) : Type :=
  {X : Finset (ConcretePlaquette d L) //
    p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
      X.card = n + ⌈siteLatticeDist p.site q.site⌉₊}

noncomputable instance connectingClusterBucket_fintype
    (d L : ℕ) [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ) :
    Fintype (ConnectingClusterBucket d L p q n) := by
  classical
  unfold ConnectingClusterBucket
  infer_instance

/-- The subtype bucket has the same cardinality as the filtered finset bucket
appearing in `ShiftedConnectingClusterCountBoundExp`. -/
theorem connectingClusterBucket_card_eq_filter
    {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ) :
    Fintype.card (ConnectingClusterBucket d L p q n) =
      ((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun X =>
          p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
            X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card := by
  classical
  unfold ConnectingClusterBucket
  rw [Fintype.card_subtype]

/-- The remaining graph-theoretic coding target: each shifted physical
connecting-cluster bucket injects into finite walks of the matching length
from the marked start plaquette. -/
def PhysicalConnectingClusterWalkCodeBound : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ),
    ∃ code :
      ConnectingClusterBucket physicalClayDimension L p q n →
        PlaquetteWalk physicalClayDimension L
          (n + ⌈siteLatticeDist p.site q.site⌉₊) p,
      Function.Injective code

/-- A bucket-to-walk injection bounds the physical connecting-cluster bucket by
the corresponding finite-walk count. -/
theorem connectingClusterBucket_card_le_walks_of_walkCode
    (hcode : PhysicalConnectingClusterWalkCodeBound)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    Fintype.card (ConnectingClusterBucket physicalClayDimension L p q n) ≤
      Fintype.card
        (PlaquetteWalk physicalClayDimension L
          (n + ⌈siteLatticeDist p.site q.site⌉₊) p) := by
  obtain ⟨code, hinj⟩ := hcode p q n
  exact Fintype.card_le_of_injective code hinj

/-- A bucket-to-walk injection and the physical walk bound give the concrete
`1296` exponential bound for one shifted connecting-cluster bucket. -/
theorem connectingClusterBucket_card_le_physical_walk_exp_of_walkCode
    (hcode : PhysicalConnectingClusterWalkCodeBound)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    Fintype.card (ConnectingClusterBucket physicalClayDimension L p q n) ≤
      1296 ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
  exact (connectingClusterBucket_card_le_walks_of_walkCode hcode p q n).trans
    (plaquetteWalk_card_le_physical_ternary p
      (n + ⌈siteLatticeDist p.site q.site⌉₊))

/-- Filter-form version of the physical bucket bound, matching the count
expression in the exponential F3 frontier. -/
theorem physical_connectingCluster_filter_card_le_walk_exp_of_walkCode
    (hcode : PhysicalConnectingClusterWalkCodeBound)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    ((Finset.univ :
      Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
        (fun X =>
          p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
            X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card ≤
      1296 ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
  rw [← connectingClusterBucket_card_eq_filter p q n]
  exact connectingClusterBucket_card_le_physical_walk_exp_of_walkCode hcode p q n

/-- Stronger extra-size coding target.  This is the F3-count shape that
matches the shifted exponential frontier directly: the code length is the
extra cardinality `n`, while the distance baseline is already accounted for in
the bucket definition. -/
def PhysicalConnectingClusterExtraWalkCodeBound : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ),
    ∃ code :
      ConnectingClusterBucket physicalClayDimension L p q n →
        PlaquetteWalk physicalClayDimension L n p,
      Function.Injective code

/-- The extra-size walk-code target gives the exact `1296^n` natural-number
bound for the physical shifted connecting-cluster bucket. -/
theorem physical_connectingCluster_filter_card_le_extra_walk_exp_of_walkCode
    (hcode : PhysicalConnectingClusterExtraWalkCodeBound)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    ((Finset.univ :
      Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
        (fun X =>
          p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
            X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card ≤
      1296 ^ n := by
  rw [← connectingClusterBucket_card_eq_filter p q n]
  obtain ⟨code, hinj⟩ := hcode p q n
  exact (Fintype.card_le_of_injective code hinj).trans
    (plaquetteWalk_card_le_physical_ternary p n)

/-- The extra-size walk-code target discharges the physical shifted
exponential F3 count frontier with constants `C_conn = 1`, `K = 1296`. -/
theorem physicalShiftedConnectingClusterCountBoundExp_of_extraWalkCode
    (hcode : PhysicalConnectingClusterExtraWalkCodeBound) :
    PhysicalShiftedConnectingClusterCountBoundExp 1 1296 := by
  intro L _ p q n _hn _hdist
  have hnat :=
    physical_connectingCluster_filter_card_le_extra_walk_exp_of_walkCode
      hcode p q n
  have hreal :
      (((Finset.univ :
        Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
          (fun X =>
            p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
              X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        ((1296 ^ n : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simpa using hreal

/-- Decoder-form version of the remaining F3-count target.  Instead of
directly producing an injection from clusters to words, it is enough to give a
decoder from words to clusters whose image covers every shifted bucket. -/
def PhysicalConnectingClusterExtraWalkDecoderBound : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ),
    ∃ decode : PlaquetteWalk physicalClayDimension L n p →
        Finset (ConcretePlaquette physicalClayDimension L),
      ∀ X : ConnectingClusterBucket physicalClayDimension L p q n,
        ∃ w : PlaquetteWalk physicalClayDimension L n p, decode w = X.1

/-- Choose, for each bucket element, one walk decoding to it. -/
noncomputable def physicalConnectingClusterExtraWalkCodeOfDecoder
    (hdecode : PhysicalConnectingClusterExtraWalkDecoderBound)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    ConnectingClusterBucket physicalClayDimension L p q n →
      PlaquetteWalk physicalClayDimension L n p :=
  let hcover := Classical.choose_spec (hdecode p q n)
  fun X => Classical.choose (hcover X)

/-- The code chosen from a covering decoder is injective, because decoding the
chosen walk recovers the original bucket element. -/
theorem physicalConnectingClusterExtraWalkCodeOfDecoder_injective
    (hdecode : PhysicalConnectingClusterExtraWalkDecoderBound)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    Function.Injective
      (physicalConnectingClusterExtraWalkCodeOfDecoder hdecode p q n) := by
  intro X Y h
  apply Subtype.ext
  let decode := Classical.choose (hdecode p q n)
  let hcover := Classical.choose_spec (hdecode p q n)
  have hX : decode (Classical.choose (hcover X)) = X.1 := by
    exact Classical.choose_spec (hcover X)
  have hY : decode (Classical.choose (hcover Y)) = Y.1 := by
    exact Classical.choose_spec (hcover Y)
  have hdec := congrArg decode h
  dsimp [physicalConnectingClusterExtraWalkCodeOfDecoder] at hdec
  change decode (Classical.choose (hcover X)) =
    decode (Classical.choose (hcover Y)) at hdec
  rw [hX, hY] at hdec
  exact hdec

/-- A covering decoder gives the injective extra-walk code target. -/
theorem physicalConnectingClusterExtraWalkCodeBound_of_decoderBound
    (hdecode : PhysicalConnectingClusterExtraWalkDecoderBound) :
    PhysicalConnectingClusterExtraWalkCodeBound := by
  intro L _ p q n
  exact ⟨physicalConnectingClusterExtraWalkCodeOfDecoder hdecode p q n,
    physicalConnectingClusterExtraWalkCodeOfDecoder_injective hdecode p q n⟩

/-- Decoder-form terminal F3-count bridge. -/
theorem physicalShiftedConnectingClusterCountBoundExp_of_extraWalkDecoder
    (hdecode : PhysicalConnectingClusterExtraWalkDecoderBound) :
    PhysicalShiftedConnectingClusterCountBoundExp 1 1296 :=
  physicalShiftedConnectingClusterCountBoundExp_of_extraWalkCode
    (physicalConnectingClusterExtraWalkCodeBound_of_decoderBound hdecode)

/-- Concrete range-decoder coverage target: every shifted physical bucket is
the visited set of some length-`n` walk from `p`. -/
def PhysicalConnectingClusterRangeDecoderCovers : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ)
    (X : ConnectingClusterBucket physicalClayDimension L p q n),
    ∃ w : PlaquetteWalk physicalClayDimension L n p,
      plaquetteWalkRangeFinset w = X.1

/-- If the concrete walk-range decoder covers every bucket, then the abstract
decoder-form F3-count target holds. -/
theorem physicalConnectingClusterExtraWalkDecoderBound_of_rangeDecoderCovers
    (hcover : PhysicalConnectingClusterRangeDecoderCovers) :
    PhysicalConnectingClusterExtraWalkDecoderBound := by
  intro L _ p q n
  exact ⟨fun w => plaquetteWalkRangeFinset w, hcover p q n⟩

/-- Concrete range-decoder terminal F3-count bridge. -/
theorem physicalShiftedConnectingClusterCountBoundExp_of_rangeDecoderCovers
    (hcover : PhysicalConnectingClusterRangeDecoderCovers) :
    PhysicalShiftedConnectingClusterCountBoundExp 1 1296 :=
  physicalShiftedConnectingClusterCountBoundExp_of_extraWalkDecoder
    (physicalConnectingClusterExtraWalkDecoderBound_of_rangeDecoderCovers hcover)

/-- Audit obstruction for the exact range-decoder target: because a length-`n`
walk visits at most `n+1` plaquettes, exact coverage of a shifted bucket of
cardinality `n + ⌈dist(p,q)⌉₊` forces `⌈dist(p,q)⌉₊ ≤ 1`.

Thus the exact visited-set decoder is useful local scaffolding, but it is too
strong as a global replacement for the BFS/tree coding theorem when the marked
plaquettes are farther apart. -/
theorem physicalConnectingClusterRangeDecoderCovers_forces_dist_ceiling_le_one
    (hcover : PhysicalConnectingClusterRangeDecoderCovers)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ)
    (X : ConnectingClusterBucket physicalClayDimension L p q n) :
    ⌈siteLatticeDist p.site q.site⌉₊ ≤ 1 := by
  obtain ⟨w, hw⟩ := hcover p q n X
  have hrange_card := plaquetteWalk_rangeFinset_card_le w
  rw [hw] at hrange_card
  have hXcard :
      X.1.card = n + ⌈siteLatticeDist p.site q.site⌉₊ := X.2.2.2.2
  omega

/-! ### Baseline-plus-extra decoder target -/

/-- Corrected concrete decoder shape after the exact range obstruction: first
fix a deterministic baseline set accounting for the marked-plaquette distance,
then let a length-`n` walk/word encode the extra plaquettes.

This is still a target, not the BFS/tree proof itself.  The key point is that
the decoded set is `baseline ∪ decodeExtra w`, so its cardinality can include
the distance baseline plus the `n` extra plaquettes without being forced to be
the literal range of a length-`n` walk. -/
def PhysicalConnectingClusterBaselineExtraDecoderCovers : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ),
    ∃ baseline : Finset (ConcretePlaquette physicalClayDimension L),
    ∃ decodeExtra : PlaquetteWalk physicalClayDimension L n p →
        Finset (ConcretePlaquette physicalClayDimension L),
      ∀ X : ConnectingClusterBucket physicalClayDimension L p q n,
        ∃ w : PlaquetteWalk physicalClayDimension L n p,
          baseline ∪ decodeExtra w = X.1

/-- The corrected baseline-plus-extra decoder target implies the abstract
extra-walk decoder target used by the F3-count bridge. -/
theorem physicalConnectingClusterExtraWalkDecoderBound_of_baselineExtraDecoderCovers
    (hcover : PhysicalConnectingClusterBaselineExtraDecoderCovers) :
    PhysicalConnectingClusterExtraWalkDecoderBound := by
  intro L _ p q n
  obtain ⟨baseline, decodeExtra, hsurj⟩ := hcover p q n
  exact ⟨fun w => baseline ∪ decodeExtra w, hsurj⟩

/-- Baseline-plus-extra decoder terminal F3-count bridge. -/
theorem physicalShiftedConnectingClusterCountBoundExp_of_baselineExtraDecoderCovers
    (hcover : PhysicalConnectingClusterBaselineExtraDecoderCovers) :
    PhysicalShiftedConnectingClusterCountBoundExp 1 1296 :=
  physicalShiftedConnectingClusterCountBoundExp_of_extraWalkDecoder
    (physicalConnectingClusterExtraWalkDecoderBound_of_baselineExtraDecoderCovers hcover)

/-! ### Word-decoder target for the BFS/Klarner proof -/

/-- General word-decoder version of the F3-count target.  This is the natural
shape of a BFS/Klarner proof: clusters are decoded from length-`n` words over a
fixed alphabet of size `K`, rather than from literal graph walks. -/
def PhysicalConnectingClusterExtraWordDecoderBound (K : ℕ) : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ),
    ∃ decode : (Fin n → Fin K) → Finset (ConcretePlaquette physicalClayDimension L),
      ∀ X : ConnectingClusterBucket physicalClayDimension L p q n,
        ∃ word : Fin n → Fin K, decode word = X.1

/-- Choose, for each bucket element, one word decoding to it. -/
noncomputable def physicalConnectingClusterExtraWordCodeOfDecoder
    {K : ℕ} (hdecode : PhysicalConnectingClusterExtraWordDecoderBound K)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    ConnectingClusterBucket physicalClayDimension L p q n → (Fin n → Fin K) :=
  let hcover := Classical.choose_spec (hdecode p q n)
  fun X => Classical.choose (hcover X)

/-- The code chosen from a covering word-decoder is injective. -/
theorem physicalConnectingClusterExtraWordCodeOfDecoder_injective
    {K : ℕ} (hdecode : PhysicalConnectingClusterExtraWordDecoderBound K)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    Function.Injective
      (physicalConnectingClusterExtraWordCodeOfDecoder hdecode p q n) := by
  intro X Y h
  apply Subtype.ext
  let decode := Classical.choose (hdecode p q n)
  let hcover := Classical.choose_spec (hdecode p q n)
  have hX : decode (Classical.choose (hcover X)) = X.1 := by
    exact Classical.choose_spec (hcover X)
  have hY : decode (Classical.choose (hcover Y)) = Y.1 := by
    exact Classical.choose_spec (hcover Y)
  have hdec := congrArg decode h
  dsimp [physicalConnectingClusterExtraWordCodeOfDecoder] at hdec
  change decode (Classical.choose (hcover X)) =
    decode (Classical.choose (hcover Y)) at hdec
  rw [hX, hY] at hdec
  exact hdec

/-- A covering word-decoder gives the exact `K^n` natural-number bound for one
shifted bucket. -/
theorem connectingClusterBucket_card_le_extra_word_of_decoder
    {K : ℕ} (hdecode : PhysicalConnectingClusterExtraWordDecoderBound K)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    Fintype.card (ConnectingClusterBucket physicalClayDimension L p q n) ≤
      K ^ n := by
  have hcard :
      Fintype.card (ConnectingClusterBucket physicalClayDimension L p q n) ≤
        Fintype.card (Fin n → Fin K) :=
    Fintype.card_le_of_injective
      (physicalConnectingClusterExtraWordCodeOfDecoder hdecode p q n)
      (physicalConnectingClusterExtraWordCodeOfDecoder_injective hdecode p q n)
  simpa [Fintype.card_fun] using hcard

/-- Word-decoder terminal F3-count bridge. -/
theorem physicalShiftedConnectingClusterCountBoundExp_of_extraWordDecoder
    {K : ℕ} (hdecode : PhysicalConnectingClusterExtraWordDecoderBound K) :
    PhysicalShiftedConnectingClusterCountBoundExp 1 K := by
  intro L _ p q n _hn _hdist
  rw [← connectingClusterBucket_card_eq_filter p q n]
  have hnat := connectingClusterBucket_card_le_extra_word_of_decoder hdecode p q n
  have hreal :
      (Fintype.card (ConnectingClusterBucket physicalClayDimension L p q n) : ℝ) ≤
        ((K ^ n : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simpa using hreal

/-- Final corrected BFS/Klarner decoder target: a deterministic baseline plus
a length-`n` word over an alphabet of size `K`.  This combines the distance
baseline correction with the finite-word counting bridge. -/
def PhysicalConnectingClusterBaselineExtraWordDecoderCovers (K : ℕ) : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ),
    ∃ baseline : Finset (ConcretePlaquette physicalClayDimension L),
    ∃ decodeExtra : (Fin n → Fin K) →
        Finset (ConcretePlaquette physicalClayDimension L),
      ∀ X : ConnectingClusterBucket physicalClayDimension L p q n,
        ∃ word : Fin n → Fin K, baseline ∪ decodeExtra word = X.1

/-- A baseline-plus-word decoder gives the plain word-decoder target by
unioning the deterministic baseline into the decoded output. -/
theorem physicalConnectingClusterExtraWordDecoderBound_of_baselineExtraWordDecoderCovers
    {K : ℕ} (hcover : PhysicalConnectingClusterBaselineExtraWordDecoderCovers K) :
    PhysicalConnectingClusterExtraWordDecoderBound K := by
  intro L _ p q n
  obtain ⟨baseline, decodeExtra, hsurj⟩ := hcover p q n
  exact ⟨fun word => baseline ∪ decodeExtra word, hsurj⟩

/-- Baseline-plus-word decoder terminal F3-count bridge. -/
theorem physicalShiftedConnectingClusterCountBoundExp_of_baselineExtraWordDecoderCovers
    {K : ℕ} (hcover : PhysicalConnectingClusterBaselineExtraWordDecoderCovers K) :
    PhysicalShiftedConnectingClusterCountBoundExp 1 K :=
  physicalShiftedConnectingClusterCountBoundExp_of_extraWordDecoder
    (physicalConnectingClusterExtraWordDecoderBound_of_baselineExtraWordDecoderCovers hcover)

/-- Physical four-dimensional baseline-plus-word decoder target with the
existing `1296` local alphabet. -/
abbrev PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296 : Prop :=
  PhysicalConnectingClusterBaselineExtraWordDecoderCovers 1296

/-- Physical-specialized terminal bridge from the baseline-plus-word decoder to
the exact exponential F3-count frontier used downstream. -/
theorem physicalShiftedConnectingClusterCountBoundExp_of_baselineExtraWordDecoderCovers1296
    (hcover : PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296) :
    PhysicalShiftedConnectingClusterCountBoundExp 1 1296 :=
  physicalShiftedConnectingClusterCountBoundExp_of_baselineExtraWordDecoderCovers hcover

/-- Package the physical `1296` baseline-plus-word decoder target as the
physical exponential F3-count package consumed by downstream F3 routes. -/
def physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296
    (hcover : PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296) :
    PhysicalShiftedF3CountPackageExp :=
  PhysicalShiftedF3CountPackageExp.ofBound 1 1296 one_pos (by norm_num)
    (physicalShiftedConnectingClusterCountBoundExp_of_baselineExtraWordDecoderCovers1296
      hcover)

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

/-! ### Bucket-to-graph-animal reduction -/

/-- Graph-theoretic anchored bucket: finite plaquette subsets of fixed
cardinality containing the root whose induced plaquette graph is
preconnected.  This is the consumer shape for a Klarner/BFS lattice-animal
count. -/
noncomputable def plaquetteGraphPreconnectedSubsetsAnchoredCard
    (d L : ℕ) [NeZero d] [NeZero L]
    (root : ConcretePlaquette d L) (k : ℕ) :
    Finset (Finset (ConcretePlaquette d L)) :=
  (Finset.univ.filter fun X =>
    root ∈ X ∧ X.card = k ∧
      ((plaquetteGraph d L).induce {x | x ∈ X}).Preconnected)

/-- Membership in an anchored bucket records that the root belongs to the
chosen plaquette set. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k) :
    root ∈ X := by
  unfold plaquetteGraphPreconnectedSubsetsAnchoredCard at hX
  rw [Finset.mem_filter] at hX
  exact hX.2.1

/-- Membership in an anchored bucket records the exact cardinality. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_card_eq
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k) :
    X.card = k := by
  unfold plaquetteGraphPreconnectedSubsetsAnchoredCard at hX
  rw [Finset.mem_filter] at hX
  exact hX.2.2.1

/-- Membership in an anchored bucket records induced preconnectedness. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k) :
    ((plaquetteGraph d L).induce {x | x ∈ X}).Preconnected := by
  unfold plaquetteGraphPreconnectedSubsetsAnchoredCard at hX
  rw [Finset.mem_filter] at hX
  exact hX.2.2.2

/-- An anchored bucket element has positive target cardinality. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_card_pos
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k) :
    0 < k := by
  have hroot : root ∈ X :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hX
  have hcard : X.card = k :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_card_eq hX
  have hpos : 0 < X.card := Finset.card_pos.mpr ⟨root, hroot⟩
  simpa [hcard] using hpos

/-- A non-singleton anchored bucket contains some plaquette different from the
root. This is the first branching witness needed by constructive
BFS/Klarner decoders. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_ne_root
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hk : 1 < k) :
    ∃ y, y ∈ X ∧ y ≠ root := by
  by_contra hnone
  have hforall : ∀ y, y ∈ X → y = root := by
    intro y hy
    by_contra hyne
    exact hnone ⟨y, hy, hyne⟩
  have hsubset : X ⊆ ({root} : Finset (ConcretePlaquette d L)) := by
    intro y hy
    rw [Finset.mem_singleton]
    exact hforall y hy
  have hcard_le : X.card ≤ 1 := by
    simpa using Finset.card_le_card hsubset
  have hcard : X.card = k :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_card_eq hX
  omega

/-- A non-singleton anchored bucket contains another plaquette different from
any chosen member. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_ne_member
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root p : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (_hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hp : p ∈ X) (hcard : X.card ≠ 1) :
    ∃ y, y ∈ X ∧ y ≠ p := by
  by_contra hnone
  have hforall : ∀ y, y ∈ X → y = p := by
    intro y hy
    by_contra hyne
    exact hnone ⟨y, hy, hyne⟩
  have hsubset : X ⊆ ({p} : Finset (ConcretePlaquette d L)) := by
    intro y hy
    rw [Finset.mem_singleton]
    exact hforall y hy
  have hcard_le : X.card ≤ 1 := by
    simpa using Finset.card_le_card hsubset
  have hcard_pos : 0 < X.card := Finset.card_pos.mpr ⟨p, hp⟩
  have hcard_eq : X.card = 1 := by omega
  exact hcard hcard_eq

/-- A nontrivial walk has a first adjacent vertex. -/
theorem simpleGraph_walk_exists_adj_start_of_ne
    {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (huv : u ≠ v) :
    ∃ w, G.Adj u w := by
  cases p with
  | nil =>
      exact False.elim (huv rfl)
  | cons hAdj _ =>
      exact ⟨_, hAdj⟩

/-- A nontrivial walk has a first adjacent vertex together with the remaining
tail walk.  This is the local walk-splitting primitive needed by constructive
BFS/Klarner decoders. -/
theorem simpleGraph_walk_exists_adj_start_and_tail_of_ne
    {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (huv : u ≠ v) :
    ∃ w, ∃ _hAdj : G.Adj u w, ∃ _tail : G.Walk w v, True := by
  cases p with
  | nil =>
      exact False.elim (huv rfl)
  | cons hAdj tail =>
      exact ⟨_, hAdj, tail, trivial⟩

/-- A non-singleton anchored bucket contains a residual neighbor of any chosen
member.  This is the member-local analogue of
`plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset`. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_nonSingleton_member_has_neighbor
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root p : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hp : p ∈ X) (hcard : X.card ≠ 1) :
    ∃ q, q ∈ X ∧ p ∈ (plaquetteGraph d L).neighborFinset q := by
  have hpre :
      ((plaquetteGraph d L).induce {x | x ∈ X}).Preconnected :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected hX
  obtain ⟨y, hy, hyne⟩ :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_ne_member hX hp hcard
  obtain ⟨walk⟩ := hpre ⟨p, hp⟩ ⟨y, hy⟩
  have hne :
      (⟨p, hp⟩ : {x : ConcretePlaquette d L // x ∈ X}) ≠
        ⟨y, hy⟩ := by
    intro h
    exact hyne (congrArg Subtype.val h).symm
  obtain ⟨q, hqAdj⟩ := simpleGraph_walk_exists_adj_start_of_ne walk hne
  have hAdj : (plaquetteGraph d L).Adj p q.1 :=
    SimpleGraph.induce_adj.mp hqAdj
  exact ⟨q.1, q.2,
    (SimpleGraph.mem_neighborFinset (plaquetteGraph d L) q.1 p).mpr hAdj.symm⟩

/-- A non-singleton anchored bucket contains a plaquette adjacent to the root,
still inside the same bucket. This is the first local expansion step needed by
BFS/Klarner decoders. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighbor
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hk : 1 < k) :
    ∃ z, z ∈ X ∧ (plaquetteGraph d L).Adj root z := by
  have hroot : root ∈ X :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hX
  have hpre :
      ((plaquetteGraph d L).induce {x | x ∈ X}).Preconnected :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected hX
  obtain ⟨y, hy, hyne⟩ :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_ne_root hX hk
  obtain ⟨p⟩ := hpre ⟨root, hroot⟩ ⟨y, hy⟩
  have hne :
      (⟨root, hroot⟩ : {x : ConcretePlaquette d L // x ∈ X}) ≠
        ⟨y, hy⟩ := by
    intro h
    exact hyne (congrArg Subtype.val h).symm
  obtain ⟨z, hz⟩ := simpleGraph_walk_exists_adj_start_of_ne p hne
  exact ⟨z.1, z.2, SimpleGraph.induce_adj.mp hz⟩

/-- Finset form of the root-neighbor witness.  This is the exact shape consumed
by the local neighbor-choice alphabets. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hk : 1 < k) :
    ∃ z, z ∈ X ∧ z ∈ (plaquetteGraph d L).neighborFinset root := by
  obtain ⟨z, hzX, hzAdj⟩ :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighbor hX hk
  exact ⟨z, hzX,
    (SimpleGraph.mem_neighborFinset (plaquetteGraph d L) root z).mpr hzAdj⟩

/-- The first BFS layer of a nontrivial anchored bucket is nonempty: the bucket
meets the root-neighbor finset. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_nonempty
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hk : 1 < k) :
    (X ∩ (plaquetteGraph d L).neighborFinset root).Nonempty := by
  obtain ⟨z, hzX, hzN⟩ :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset hX hk
  exact ⟨z, by simp [hzX, hzN]⟩

/-- Cardinal form of the nonempty first BFS layer. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_pos
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hk : 1 < k) :
    0 < (X ∩ (plaquetteGraph d L).neighborFinset root).card :=
  Finset.card_pos.mpr
    (plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_nonempty hX hk)

/-- The first BFS shell is bounded by the local neighbor finset. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_neighborFinset
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (_hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k) :
    (X ∩ (plaquetteGraph d L).neighborFinset root).card ≤
      ((plaquetteGraph d L).neighborFinset root).card :=
  Finset.card_le_card (Finset.inter_subset_right)

/-- A branching bound controls the first BFS shell of every anchored bucket. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_branching
    {d D L k : ℕ} [NeZero d] [NeZero L]
    (hD : PlaquetteGraphBranchingBoundDim d D)
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k) :
    (X ∩ (plaquetteGraph d L).neighborFinset root).card ≤ D :=
  (plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_neighborFinset
      hX).trans
    (hD root)

/-- Physical four-dimensional first-shell bound in the current `1296` alphabet. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_1296
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k) :
    (X ∩ (plaquetteGraph physicalClayDimension L).neighborFinset root).card ≤ 1296 :=
  plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_branching
    plaquetteGraph_branchingBoundDim_physical_ternary hX

/-- Canonical code for the first BFS shell, obtained from any local branching
bound. -/
noncomputable def plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCodeOfBranching
    {d D L k : ℕ} [NeZero d] [NeZero L]
    (hD : PlaquetteGraphBranchingBoundDim d D)
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k) :
    {z : ConcretePlaquette d L //
      z ∈ X ∩ (plaquetteGraph d L).neighborFinset root} → Fin D :=
  finsetCodeOfCardLe (X ∩ (plaquetteGraph d L).neighborFinset root)
    (plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_branching hD hX)

/-- The first-shell code induced by a branching bound is injective. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCodeOfBranching_injective
    {d D L k : ℕ} [NeZero d] [NeZero L]
    (hD : PlaquetteGraphBranchingBoundDim d D)
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k) :
    Function.Injective
      (plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCodeOfBranching
        hD hX) :=
  finsetCodeOfCardLe_injective (X ∩ (plaquetteGraph d L).neighborFinset root)
    (plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_branching hD hX)

/-- Physical four-dimensional first-shell code in the current `1296` alphabet. -/
noncomputable def physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k) :
    {z : ConcretePlaquette physicalClayDimension L //
      z ∈ X ∩ (plaquetteGraph physicalClayDimension L).neighborFinset root} →
      Fin 1296 :=
  plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCodeOfBranching
    plaquetteGraph_branchingBoundDim_physical_ternary hX

/-- The physical `1296` first-shell code is injective. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296_injective
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k) :
    Function.Injective
      (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296 hX) :=
  plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCodeOfBranching_injective
    plaquetteGraph_branchingBoundDim_physical_ternary hX

/-- Nontrivial physical anchored buckets have an inhabited coded first shell. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hk : 1 < k) :
    ∃ c : Fin 1296,
      ∃ z : {z : ConcretePlaquette physicalClayDimension L //
        z ∈ X ∩ (plaquetteGraph physicalClayDimension L).neighborFinset root},
        physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296 hX z = c := by
  obtain ⟨z, hz⟩ :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_nonempty hX hk
  exact ⟨physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296 hX
      ⟨z, hz⟩,
    ⟨⟨z, hz⟩, rfl⟩⟩

/-- Canonical first-deletion code for a nontrivial physical anchored bucket.
This chooses the first root-shell symbol that a recursive BFS/Klarner deletion
decoder can peel from a bucket with `1 < k`. -/
noncomputable def physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteCode1296
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hk : 1 < k) :
    Fin 1296 :=
  Classical.choose
    (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296
      hX hk)

/-- Canonical first-deletion plaquette for a nontrivial physical anchored
bucket.  The chosen plaquette lies in the root shell
`X ∩ neighborFinset root`. -/
noncomputable def physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hk : 1 < k) :
    {z : ConcretePlaquette physicalClayDimension L //
      z ∈ X ∩ (plaquetteGraph physicalClayDimension L).neighborFinset root} :=
  Classical.choose
    (Classical.choose_spec
      (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296
        hX hk))

/-- The canonical first-deletion plaquette carries exactly the canonical
first-deletion code. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteCode1296_spec
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hk : 1 < k) :
    physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296 hX
      (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296
        hX hk) =
      physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteCode1296
        hX hk := by
  let h :=
    physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296
      hX hk
  exact Classical.choose_spec (Classical.choose_spec h)

/-- The canonical first-deletion plaquette is outside the root and therefore
belongs to the root-erased residual bucket.  This is the deletion-side API
needed before the first-shell selector can be iterated into full words. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296_mem_erase_root
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hk : 1 < k) :
    (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296
      hX hk).1 ∈ X.erase root := by
  let z :=
    physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296 hX hk
  have hzX : z.1 ∈ X := (Finset.mem_inter.mp z.2).1
  have hzN : z.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset root :=
    (Finset.mem_inter.mp z.2).2
  have hzAdj : (plaquetteGraph physicalClayDimension L).Adj root z.1 :=
    (SimpleGraph.mem_neighborFinset
      (plaquetteGraph physicalClayDimension L) root z.1).mp hzN
  exact Finset.mem_erase.mpr ⟨hzAdj.1.symm, hzX⟩

/-- Residual finset after peeling the canonical first-deletion plaquette from a
nontrivial physical anchored bucket.  This records the raw deletion operation;
preconnectedness of this residual is a separate, nontrivial leaf-selection
problem. -/
noncomputable def physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hk : 1 < k) :
    Finset (ConcretePlaquette physicalClayDimension L) :=
  X.erase
    (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296 hX hk).1

/-- Peeling the canonical first-deletion plaquette lowers the raw cardinal by
one.  The remaining recursive challenge is to choose deletions that also
preserve the relevant preconnected anchored invariant. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296_card
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hk : 1 < k) :
    (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296
      hX hk).card = k - 1 := by
  let z :=
    physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296 hX hk
  have hzX : z.1 ∈ X := (Finset.mem_inter.mp z.2).1
  have hcard : X.card = k :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_card_eq hX
  simp [physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296,
    z, Finset.card_erase_of_mem hzX, hcard]

/-- The root remains in the raw residual after peeling the canonical
first-deletion plaquette. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem_firstDeleteResidual1296
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hk : 1 < k) :
    root ∈ physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296
      hX hk := by
  have hroot : root ∈ X :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hX
  have hdel :
      (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296
        hX hk).1 ∈ X.erase root :=
    physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296_mem_erase_root
      hX hk
  have hne :
      root ≠
        (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296
          hX hk).1 :=
    (Finset.mem_erase.mp hdel).1.symm
  exact Finset.mem_erase.mpr ⟨hne, hroot⟩

/-- Generic recursive-deletion bridge for anchored graph-animal buckets.
If deleting a non-root plaquette preserves induced preconnectedness, then the
erased set is again an anchored bucket, now at cardinality `k - 1`.

This isolates the exact remaining hard combinatorial input: finding such a
deleteable non-root plaquette for every nontrivial anchored bucket. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_preconnected
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root z : ConcretePlaquette d L}
    {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hzX : z ∈ X) (hz_ne_root : z ≠ root)
    (hpre :
      ((plaquetteGraph d L).induce {x | x ∈ X.erase z}).Preconnected) :
    X.erase z ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root (k - 1) := by
  have hroot : root ∈ X :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hX
  have hcard : X.card = k :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_card_eq hX
  unfold plaquetteGraphPreconnectedSubsetsAnchoredCard
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _,
    Finset.mem_erase.mpr ⟨hz_ne_root.symm, hroot⟩,
    by simp [Finset.card_erase_of_mem hzX, hcard],
    hpre⟩

/-- Physical `1296` first-deletion residual re-enters the anchored bucket if
the selected deletion is known to preserve induced preconnectedness.  This is
the formal recursive handoff point between the current first-deletion API and
the still-open leaf/deletion-order theorem. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296_mem_of_preconnected
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hk : 1 < k)
    (hpre :
      ((plaquetteGraph physicalClayDimension L).induce
        {x | x ∈
          physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296
            hX hk}).Preconnected) :
    physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296
      hX hk ∈
        plaquetteGraphPreconnectedSubsetsAnchoredCard physicalClayDimension L root
          (k - 1) := by
  let z :=
    (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296 hX hk).1
  have hzErase :
      z ∈ X.erase root := by
    simpa [z] using
      physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296_mem_erase_root
        hX hk
  have hzX : z ∈ X := (Finset.mem_erase.mp hzErase).2
  have hz_ne_root : z ≠ root := (Finset.mem_erase.mp hzErase).1
  simpa [physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296,
    z] using
    plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_preconnected
      (d := physicalClayDimension) (L := L) (k := k) (root := root)
      (z := z) (X := X) hX hzX hz_ne_root hpre

/-- Local leaf-deletion criterion for anchored buckets.  If a non-root member
has degree one in the induced bucket graph, then deleting it preserves
preconnectedness of the residual bucket.

This is the degree-one leaf subcase of the still-open root-avoiding deletion
order theorem. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_preconnected_of_induced_degree_one
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root z : ConcretePlaquette d L}
    {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hzX : z ∈ X) (_hz_ne_root : z ≠ root)
    (hdeg :
      ((plaquetteGraph d L).induce {x | x ∈ X}).degree ⟨z, hzX⟩ = 1) :
    ((plaquetteGraph d L).induce {x | x ∈ X.erase z}).Preconnected := by
  classical
  let GX : SimpleGraph {x : ConcretePlaquette d L // x ∈ X} :=
    (plaquetteGraph d L).induce {x | x ∈ X}
  let vz : {x : ConcretePlaquette d L // x ∈ X} := ⟨z, hzX⟩
  have hroot : root ∈ X :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hX
  have hpreX : GX.Preconnected := by
    simpa [GX] using
      plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected hX
  have hconnX : GX.Connected := by
    exact { preconnected := hpreX, nonempty := ⟨⟨root, hroot⟩⟩ }
  let Gsrc : SimpleGraph
      {x : {x : ConcretePlaquette d L // x ∈ X} // x ∈ ({vz}ᶜ :
          Set {x : ConcretePlaquette d L // x ∈ X})} :=
    GX.induce ({vz}ᶜ : Set {x : ConcretePlaquette d L // x ∈ X})
  let Gtgt : SimpleGraph {x : ConcretePlaquette d L // x ∈ X.erase z} :=
    (plaquetteGraph d L).induce {x | x ∈ X.erase z}
  have hsrc :
      Gsrc.Preconnected := by
    have hconnected :
        (GX.induce ({vz}ᶜ : Set {x : ConcretePlaquette d L // x ∈ X})).Connected := by
      simpa [GX, vz] using
        hconnX.induce_compl_singleton_of_degree_eq_one
          (v := vz) (by simpa [GX, vz] using hdeg)
    simpa [Gsrc] using hconnected.preconnected
  let f : Gsrc →g Gtgt :=
    { toFun := fun a =>
        ⟨a.1.1, Finset.mem_erase.mpr ⟨by
          intro h
          exact a.2 (Subtype.ext h), a.1.2⟩⟩
      map_rel' := by
        intro a b hab
        exact SimpleGraph.induce_adj.mpr
          (SimpleGraph.induce_adj.mp (SimpleGraph.induce_adj.mp hab)) }
  have hf_surj : Function.Surjective f := by
    intro y
    rcases Finset.mem_erase.mp y.2 with ⟨hy_ne, hyX⟩
    refine ⟨⟨⟨y.1, hyX⟩, ?_⟩, ?_⟩
    · intro hy
      exact hy_ne (Subtype.ext_iff.mp hy)
    · ext
      rfl
  simpa [Gtgt] using hsrc.map f hf_surj

/-- A non-root degree-one member supplies the recursive-deletion hypothesis
needed by `plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_preconnected`.
This packages the leaf subcase as an actual one-step recursive bucket
transition. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_induced_degree_one
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root z : ConcretePlaquette d L}
    {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hzX : z ∈ X) (hz_ne_root : z ≠ root)
    (hdeg :
      ((plaquetteGraph d L).induce {x | x ∈ X}).degree ⟨z, hzX⟩ = 1) :
    X.erase z ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root (k - 1) :=
  plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_preconnected
    hX hzX hz_ne_root
    (plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_preconnected_of_induced_degree_one
      hX hzX hz_ne_root hdeg)

/-- The exact global graph-combinatorics hypothesis still missing from the
F3/Klarner decoder after v2.52.

For every nontrivial anchored preconnected bucket, it asks for a non-root member
whose deletion leaves another anchored preconnected bucket of size `k - 1`.
This is the one-step recursive deletion property needed by the anchored
BFS/Klarner decoder. -/
def PlaquetteGraphAnchoredSafeDeletionExists (d L : ℕ) [NeZero d] [NeZero L] :
    Prop :=
  ∀ {root : ConcretePlaquette d L} {k : ℕ}
    {X : Finset (ConcretePlaquette d L)},
    2 ≤ k →
    X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k →
    ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
      X.erase z ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root (k - 1)

/-- A stronger sufficient global hypothesis: every nontrivial anchored bucket
has a non-root member of degree one in the induced bucket graph.

This is separated from `PlaquetteGraphAnchoredSafeDeletionExists` because the
degree-one condition is useful and already locally proved safe, but the exact
recursive decoder only needs safe deletion, not necessarily an induced leaf. -/
def PlaquetteGraphAnchoredDegreeOneDeletionExists
    (d L : ℕ) [NeZero d] [NeZero L] : Prop :=
  ∀ {root : ConcretePlaquette d L} {k : ℕ}
    {X : Finset (ConcretePlaquette d L)},
    2 ≤ k →
    X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k →
    ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
      ((plaquetteGraph d L).induce {x | x ∈ X}).degree ⟨z, hzX⟩ = 1

/-- Exact graph-theoretic non-cut formulation of the anchored deletion gap.

This is the minimum raw combinatorial content needed by
`PlaquetteGraphAnchoredSafeDeletionExists`: for every nontrivial anchored
bucket, find a non-root member whose deletion preserves induced
preconnectedness.  The safe-deletion proposition additionally packages the
erased set back into the anchored bucket family. -/
def PlaquetteGraphAnchoredNonRootNonCutExists
    (d L : ℕ) [NeZero d] [NeZero L] : Prop :=
  ∀ {root : ConcretePlaquette d L} {k : ℕ}
    {X : Finset (ConcretePlaquette d L)},
    2 ≤ k →
    X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k →
    ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
      ((plaquetteGraph d L).induce {x | x ∈ X.erase z}).Preconnected

/-- Two-non-cut formulation of the anchored deletion gap.

This is the standard graph-theoretic shape one expects from finite connected
graphs: every nontrivial anchored bucket has two distinct deletion candidates
whose removal preserves induced preconnectedness.  If this is proved globally,
one candidate must be different from the anchored root, so it implies the exact
non-root non-cut formulation below. -/
def PlaquetteGraphAnchoredTwoNonCutExists
    (d L : ℕ) [NeZero d] [NeZero L] : Prop :=
  ∀ {root : ConcretePlaquette d L} {k : ℕ}
    {X : Finset (ConcretePlaquette d L)},
    2 ≤ k →
    X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k →
    ∃ z₁, ∃ hz₁X : z₁ ∈ X, ∃ z₂, ∃ hz₂X : z₂ ∈ X,
      z₁ ≠ z₂ ∧
        ((plaquetteGraph d L).induce {x | x ∈ X.erase z₁}).Preconnected ∧
        ((plaquetteGraph d L).induce {x | x ∈ X.erase z₂}).Preconnected

/-- High-cardinality two-non-cut formulation after the small base zone has
been split off.

The v2.55/v2.58/v2.59 base drivers cover `2 ≤ k ≤ 3`.  The remaining
nontrivial graph-theoretic theorem can therefore be stated just for `4 ≤ k`,
which prevents the F3 route from accumulating more isolated base cases. -/
def PlaquetteGraphAnchoredHighCardTwoNonCutExists
    (d L : ℕ) [NeZero d] [NeZero L] : Prop :=
  ∀ {root : ConcretePlaquette d L} {k : ℕ}
    {X : Finset (ConcretePlaquette d L)},
    4 ≤ k →
    X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k →
    ∃ z₁, ∃ hz₁X : z₁ ∈ X, ∃ z₂, ∃ hz₂X : z₂ ∈ X,
      z₁ ≠ z₂ ∧
        ((plaquetteGraph d L).induce {x | x ∈ X.erase z₁}).Preconnected ∧
        ((plaquetteGraph d L).induce {x | x ∈ X.erase z₂}).Preconnected

/-- Generic finite-graph theorem that remains to be supplied for the
high-cardinality F3 deletion route.

It is intentionally phrased without plaquette geometry: every finite connected
graph with at least four vertices has two distinct vertices whose deletion
leaves a preconnected induced graph.  The bridge below transports this pure
graph statement to the plaquette bucket target
`PlaquetteGraphAnchoredHighCardTwoNonCutExists`. -/
def SimpleGraphHighCardTwoNonCutExists : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α),
    G.Connected →
    4 ≤ Fintype.card α →
    ∃ z₁, ∃ z₂,
      z₁ ≠ z₂ ∧
        (G.induce ({z₁}ᶜ : Set α)).Preconnected ∧
        (G.induce ({z₂}ᶜ : Set α)).Preconnected

/-- A finite tree with at least two vertices has two distinct leaves.

This is the focused graph-theoretic helper needed by the spanning-tree route
to `SimpleGraphHighCardTwoNonCutExists`: two leaves of the same spanning tree
give two deletion candidates in the original connected graph. -/
theorem simpleGraph_isTree_exists_two_distinct_degree_one_of_card_ge_two
    {V : Type} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V) :
    ∃ z₁ z₂ : V, z₁ ≠ z₂ ∧ T.degree z₁ = 1 ∧ T.degree z₂ = 1 := by
  classical
  haveI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp
      (Nat.lt_of_lt_of_le Nat.one_lt_two hcard)
  obtain ⟨z₁, hz₁⟩ := hT.exists_vert_degree_one_of_nontrivial
  by_contra hnot
  push_neg at hnot
  have huniq : ∀ v : V, T.degree v = 1 → v = z₁ := by
    intro v hv
    by_contra hvne
    exact hnot z₁ v (fun h => hvne h.symm) hz₁ hv
  have hdeg_ge : ∀ v : V, v ≠ z₁ → 2 ≤ T.degree v := by
    intro v hvne
    have hpos : 0 < T.degree v :=
      hT.isConnected.preconnected.degree_pos_of_nontrivial v
    have hne_one : T.degree v ≠ 1 := by
      intro hv
      exact hvne (huniq v hv)
    omega
  have hsum_lower : 2 * Fintype.card V - 1 ≤ ∑ v : V, T.degree v := by
    calc
      2 * Fintype.card V - 1 = 1 + 2 * (Fintype.card V - 1) := by
        omega
      _ ≤ T.degree z₁ + (∑ v ∈ Finset.univ.erase z₁, T.degree v) := by
        rw [hz₁]
        exact Nat.add_le_add_left (by
          calc
            2 * (Fintype.card V - 1)
                = ∑ v ∈ Finset.univ.erase z₁, 2 := by
                  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ z₁),
                    Finset.card_univ, smul_eq_mul]
                  omega
            _ ≤ ∑ v ∈ Finset.univ.erase z₁, T.degree v := by
              exact Finset.sum_le_sum fun v hv => hdeg_ge v
                (Finset.mem_erase.mp hv).1) 1
      _ = ∑ v : V, T.degree v := by
        rw [add_comm]
        exact Finset.sum_erase_add _ _ (Finset.mem_univ z₁)
  have hsum := T.sum_degrees_eq_twice_card_edges
  have hedge := hT.card_edgeFinset
  omega

/-- Finite connected graphs with at least four vertices have two distinct
vertices whose deletion leaves a preconnected induced graph.

The proof takes a spanning tree, uses the two-leaves helper above, deletes
each leaf in the tree, and then transports preconnectedness to the original
graph by monotonicity. -/
theorem simpleGraphHighCardTwoNonCutExists :
    SimpleGraphHighCardTwoNonCutExists := by
  classical
  intro α _ _ G hconn hcard
  obtain ⟨T, hTG, hT⟩ := hconn.exists_isTree_le
  have h2 : 2 ≤ Fintype.card α := le_trans (by norm_num) hcard
  obtain ⟨z₁, z₂, hne, hdeg₁, hdeg₂⟩ :=
    simpleGraph_isTree_exists_two_distinct_degree_one_of_card_ge_two hT h2
  refine ⟨z₁, z₂, hne, ?_, ?_⟩
  · exact
      ((hT.isConnected.induce_compl_singleton_of_degree_eq_one hdeg₁).mono
        (by
          intro a b hab
          exact hTG hab)).preconnected
  · exact
      ((hT.isConnected.induce_compl_singleton_of_degree_eq_one hdeg₂).mono
        (by
          intro a b hab
          exact hTG hab)).preconnected

/-- The degree-one global hypothesis is sufficient for the exact safe-deletion
hypothesis, by the local v2.52 leaf-deletion theorem. -/
theorem plaquetteGraphAnchoredSafeDeletionExists_of_degreeOneDeletionExists
    {d L : ℕ} [NeZero d] [NeZero L]
    (hdegone : PlaquetteGraphAnchoredDegreeOneDeletionExists d L) :
    PlaquetteGraphAnchoredSafeDeletionExists d L := by
  intro root k X hk hX
  obtain ⟨z, hzX, hz_ne_root, hdeg⟩ := hdegone hk hX
  exact ⟨z, hzX, hz_ne_root,
    plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_induced_degree_one
      hX hzX hz_ne_root hdeg⟩

/-- The non-root non-cut formulation is sufficient for the exact safe-deletion
hypothesis, via the generic erased-bucket bridge. -/
theorem plaquetteGraphAnchoredSafeDeletionExists_of_nonRootNonCutExists
    {d L : ℕ} [NeZero d] [NeZero L]
    (hnoncut : PlaquetteGraphAnchoredNonRootNonCutExists d L) :
    PlaquetteGraphAnchoredSafeDeletionExists d L := by
  intro root k X hk hX
  obtain ⟨z, hzX, hz_ne_root, hpre⟩ := hnoncut hk hX
  exact ⟨z, hzX, hz_ne_root,
    plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_preconnected
      hX hzX hz_ne_root hpre⟩

/-- A global two-non-cut theorem is sufficient for the exact non-root non-cut
formulation: among two distinct deletion candidates, at least one is not the
anchored root. -/
theorem plaquetteGraphAnchoredNonRootNonCutExists_of_twoNonCutExists
    {d L : ℕ} [NeZero d] [NeZero L]
    (htwo : PlaquetteGraphAnchoredTwoNonCutExists d L) :
    PlaquetteGraphAnchoredNonRootNonCutExists d L := by
  intro root k X hk hX
  obtain ⟨z₁, hz₁X, z₂, hz₂X, hne, hpre₁, hpre₂⟩ := htwo hk hX
  by_cases hz₁root : z₁ = root
  · refine ⟨z₂, hz₂X, ?_, hpre₂⟩
    intro hz₂root
    exact hne (hz₁root.trans hz₂root.symm)
  · exact ⟨z₁, hz₁X, hz₁root, hpre₁⟩

/-- A global two-non-cut theorem is sufficient for exact anchored safe
deletion.  This factors through the non-root non-cut bridge to keep the
remaining F3/Klarner obstruction visibly graph-theoretic. -/
theorem plaquetteGraphAnchoredSafeDeletionExists_of_twoNonCutExists
    {d L : ℕ} [NeZero d] [NeZero L]
    (htwo : PlaquetteGraphAnchoredTwoNonCutExists d L) :
    PlaquetteGraphAnchoredSafeDeletionExists d L :=
  plaquetteGraphAnchoredSafeDeletionExists_of_nonRootNonCutExists
    (plaquetteGraphAnchoredNonRootNonCutExists_of_twoNonCutExists htwo)

/-- Conversely, the exact safe-deletion hypothesis exposes a non-root non-cut
witness by projecting preconnectedness from the erased anchored bucket. -/
theorem plaquetteGraphAnchoredNonRootNonCutExists_of_safeDeletionExists
    {d L : ℕ} [NeZero d] [NeZero L]
    (hsafe : PlaquetteGraphAnchoredSafeDeletionExists d L) :
    PlaquetteGraphAnchoredNonRootNonCutExists d L := by
  intro root k X hk hX
  obtain ⟨z, hzX, hz_ne_root, hmem⟩ := hsafe hk hX
  exact ⟨z, hzX, hz_ne_root,
    plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected hmem⟩

/-- Safe deletion and the non-root non-cut formulation are equivalent.  This
pins the remaining F3/Klarner B.1 obstruction to the standard rooted non-cut
graph lemma. -/
theorem plaquetteGraphAnchoredSafeDeletionExists_iff_nonRootNonCutExists
    {d L : ℕ} [NeZero d] [NeZero L] :
    PlaquetteGraphAnchoredSafeDeletionExists d L ↔
      PlaquetteGraphAnchoredNonRootNonCutExists d L :=
  ⟨plaquetteGraphAnchoredNonRootNonCutExists_of_safeDeletionExists,
    plaquetteGraphAnchoredSafeDeletionExists_of_nonRootNonCutExists⟩

/-- Safe-deletion existence, once proved globally, is exactly the one-step
recursive transition needed by the anchored BFS/Klarner decoder.

This is deliberately conditional: it does not close `F3-COUNT`; it packages the
remaining graph-theoretic gap as the hypothesis
`PlaquetteGraphAnchoredSafeDeletionExists d L`. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L}
    {X : Finset (ConcretePlaquette d L)}
    (hsafe : PlaquetteGraphAnchoredSafeDeletionExists d L)
    (hk : 2 ≤ k)
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k) :
    ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
      X.erase z ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root (k - 1) := by
  exact hsafe hk hX

/-- Physical four-dimensional version of the global safe-deletion hypothesis
for the `1296`-alphabet F3 route. -/
abbrev PhysicalPlaquetteGraphAnchoredSafeDeletionExists (L : ℕ) [NeZero L] :
    Prop :=
  PlaquetteGraphAnchoredSafeDeletionExists physicalClayDimension L

/-- Physical four-dimensional version of the stronger degree-one deletion
hypothesis. -/
abbrev PhysicalPlaquetteGraphAnchoredDegreeOneDeletionExists
    (L : ℕ) [NeZero L] : Prop :=
  PlaquetteGraphAnchoredDegreeOneDeletionExists physicalClayDimension L

/-- Physical four-dimensional version of the exact non-root non-cut deletion
hypothesis. -/
abbrev PhysicalPlaquetteGraphAnchoredNonRootNonCutExists
    (L : ℕ) [NeZero L] : Prop :=
  PlaquetteGraphAnchoredNonRootNonCutExists physicalClayDimension L

/-- Physical four-dimensional version of the two-non-cut deletion hypothesis. -/
abbrev PhysicalPlaquetteGraphAnchoredTwoNonCutExists
    (L : ℕ) [NeZero L] : Prop :=
  PlaquetteGraphAnchoredTwoNonCutExists physicalClayDimension L

/-- Physical four-dimensional version of the high-cardinality two-non-cut
deletion hypothesis. -/
abbrev PhysicalPlaquetteGraphAnchoredHighCardTwoNonCutExists
    (L : ℕ) [NeZero L] : Prop :=
  PlaquetteGraphAnchoredHighCardTwoNonCutExists physicalClayDimension L

/-- Physical specialization: degree-one deletion existence is sufficient for
safe deletion existence. -/
theorem physicalPlaquetteGraphAnchoredSafeDeletionExists_of_degreeOneDeletionExists
    {L : ℕ} [NeZero L]
    (hdegone : PhysicalPlaquetteGraphAnchoredDegreeOneDeletionExists L) :
    PhysicalPlaquetteGraphAnchoredSafeDeletionExists L :=
  plaquetteGraphAnchoredSafeDeletionExists_of_degreeOneDeletionExists
    (d := physicalClayDimension) (L := L) hdegone

/-- Physical specialization: non-root non-cut deletion existence is sufficient
for safe deletion existence. -/
theorem physicalPlaquetteGraphAnchoredSafeDeletionExists_of_nonRootNonCutExists
    {L : ℕ} [NeZero L]
    (hnoncut : PhysicalPlaquetteGraphAnchoredNonRootNonCutExists L) :
    PhysicalPlaquetteGraphAnchoredSafeDeletionExists L :=
  plaquetteGraphAnchoredSafeDeletionExists_of_nonRootNonCutExists
    (d := physicalClayDimension) (L := L) hnoncut

/-- Physical specialization: two non-cut deletion candidates are sufficient for
the exact non-root non-cut formulation. -/
theorem physicalPlaquetteGraphAnchoredNonRootNonCutExists_of_twoNonCutExists
    {L : ℕ} [NeZero L]
    (htwo : PhysicalPlaquetteGraphAnchoredTwoNonCutExists L) :
    PhysicalPlaquetteGraphAnchoredNonRootNonCutExists L :=
  plaquetteGraphAnchoredNonRootNonCutExists_of_twoNonCutExists
    (d := physicalClayDimension) (L := L) htwo

/-- Physical specialization: two non-cut deletion candidates are sufficient for
exact anchored safe deletion. -/
theorem physicalPlaquetteGraphAnchoredSafeDeletionExists_of_twoNonCutExists
    {L : ℕ} [NeZero L]
    (htwo : PhysicalPlaquetteGraphAnchoredTwoNonCutExists L) :
    PhysicalPlaquetteGraphAnchoredSafeDeletionExists L :=
  plaquetteGraphAnchoredSafeDeletionExists_of_twoNonCutExists
    (d := physicalClayDimension) (L := L) htwo

/-- Physical specialization: safe deletion exposes the non-root non-cut
formulation. -/
theorem physicalPlaquetteGraphAnchoredNonRootNonCutExists_of_safeDeletionExists
    {L : ℕ} [NeZero L]
    (hsafe : PhysicalPlaquetteGraphAnchoredSafeDeletionExists L) :
    PhysicalPlaquetteGraphAnchoredNonRootNonCutExists L :=
  plaquetteGraphAnchoredNonRootNonCutExists_of_safeDeletionExists
    (d := physicalClayDimension) (L := L) hsafe

/-- Physical specialization of the equivalence between safe deletion and
non-root non-cut deletion. -/
theorem physicalPlaquetteGraphAnchoredSafeDeletionExists_iff_nonRootNonCutExists
    {L : ℕ} [NeZero L] :
    PhysicalPlaquetteGraphAnchoredSafeDeletionExists L ↔
      PhysicalPlaquetteGraphAnchoredNonRootNonCutExists L :=
  plaquetteGraphAnchoredSafeDeletionExists_iff_nonRootNonCutExists
    (d := physicalClayDimension) (L := L)

/-- Physical specialization of the conditional one-step recursive deletion
driver.  This is the immediate handoff from the still-open global safe-deletion
existence theorem to the already-proved v2.52 local deletion theorem. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hsafe : PhysicalPlaquetteGraphAnchoredSafeDeletionExists L)
    (hk : 2 ≤ k)
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k) :
    ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
      X.erase z ∈
        plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root (k - 1) :=
  plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion
    (d := physicalClayDimension) (L := L) (k := k) (root := root) (X := X)
    hsafe hk hX

/-- Transport preconnectedness from the induced subtype graph with one vertex
removed back to the concrete erased plaquette bucket.

This factors out the subtype-to-`Finset.erase` graph-homomorphism used by the
unrooted non-cut theorem, so later two-non-cut bridges can reuse it for both
deletion candidates. -/
theorem plaquetteGraph_erase_preconnected_of_subtype_compl_preconnected
    {d L : ℕ} [NeZero d] [NeZero L]
    {X : Finset (ConcretePlaquette d L)}
    (z : {x : ConcretePlaquette d L // x ∈ X})
    (hpre :
      (((plaquetteGraph d L).induce {x | x ∈ X}).induce
        ({z}ᶜ : Set {x : ConcretePlaquette d L // x ∈ X})).Preconnected) :
    ((plaquetteGraph d L).induce {x | x ∈ X.erase z.1}).Preconnected := by
  classical
  let GX : SimpleGraph {x : ConcretePlaquette d L // x ∈ X} :=
    (plaquetteGraph d L).induce {x | x ∈ X}
  let Gsrc : SimpleGraph
      {x : {x : ConcretePlaquette d L // x ∈ X} // x ∈ ({z}ᶜ :
          Set {x : ConcretePlaquette d L // x ∈ X})} :=
    GX.induce ({z}ᶜ : Set {x : ConcretePlaquette d L // x ∈ X})
  let Gtgt : SimpleGraph {x : ConcretePlaquette d L // x ∈ X.erase z.1} :=
    (plaquetteGraph d L).induce {x | x ∈ X.erase z.1}
  have hsrc : Gsrc.Preconnected := by
    simpa [GX, Gsrc] using hpre
  let f : Gsrc →g Gtgt :=
    { toFun := fun a =>
        ⟨a.1.1, Finset.mem_erase.mpr ⟨by
          intro h
          exact a.2 (Subtype.ext h), a.1.2⟩⟩
      map_rel' := by
        intro a b hab
        exact SimpleGraph.induce_adj.mpr
          (SimpleGraph.induce_adj.mp (SimpleGraph.induce_adj.mp hab)) }
  have hf_surj : Function.Surjective f := by
    intro y
    rcases Finset.mem_erase.mp y.2 with ⟨hy_ne, hyX⟩
    refine ⟨⟨⟨y.1, hyX⟩, ?_⟩, ?_⟩
    · intro hy
      exact hy_ne (Subtype.ext_iff.mp hy)
    · ext
      rfl
  simpa [Gtgt] using hsrc.map f hf_surj

/-- Unrooted non-cut deletion for anchored buckets.

Mathlib already proves that a finite connected graph has some vertex whose
removal leaves a preconnected induced graph.  Applied to the induced graph on
an anchored plaquette bucket, this gives a deletion preserving
preconnectedness of `X.erase z`.

This theorem is deliberately *unrooted*: it does not assert `z ≠ root`, so it
does not yet discharge `PlaquetteGraphAnchoredSafeDeletionExists`.  It isolates
the remaining F3/Klarner gap to the root-avoiding refinement needed by the
recursive decoder. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_preconnected_unrooted
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L}
    {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k) :
    ∃ z, ∃ hzX : z ∈ X,
      ((plaquetteGraph d L).induce {x | x ∈ X.erase z}).Preconnected := by
  classical
  let GX : SimpleGraph {x : ConcretePlaquette d L // x ∈ X} :=
    (plaquetteGraph d L).induce {x | x ∈ X}
  have hroot : root ∈ X :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hX
  have hpreX : GX.Preconnected := by
    simpa [GX] using
      plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected hX
  have hconnX : GX.Connected := by
    exact { preconnected := hpreX, nonempty := ⟨⟨root, hroot⟩⟩ }
  obtain ⟨vz, hvz⟩ :=
    hconnX.exists_preconnected_induce_compl_singleton_of_finite
  exact ⟨vz.1, vz.2, by
    exact plaquetteGraph_erase_preconnected_of_subtype_compl_preconnected
      (d := d) (L := L) (X := X) vz (by simpa [GX] using hvz)⟩

/-- A pure finite-graph two-non-cut theorem supplies the high-cardinality
plaquette deletion target.

This is a v2.61 bridge: it does not prove the graph theorem itself, but it
removes all plaquette-specific bookkeeping from the remaining high-cardinality
obstruction. -/
theorem plaquetteGraphAnchoredHighCardTwoNonCutExists_of_simpleGraph
    {d L : ℕ} [NeZero d] [NeZero L]
    (hgraph : SimpleGraphHighCardTwoNonCutExists) :
    PlaquetteGraphAnchoredHighCardTwoNonCutExists d L := by
  classical
  intro root k X hk hX
  let GX : SimpleGraph {x : ConcretePlaquette d L // x ∈ X} :=
    (plaquetteGraph d L).induce {x | x ∈ X}
  have hroot : root ∈ X :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hX
  have hpreX : GX.Preconnected := by
    simpa [GX] using
      plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected hX
  have hconnX : GX.Connected := by
    exact { preconnected := hpreX, nonempty := ⟨⟨root, hroot⟩⟩ }
  have hcardX : X.card = k :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_card_eq hX
  have hcardSubtype :
      4 ≤ Fintype.card {x : ConcretePlaquette d L // x ∈ X} := by
    rw [Fintype.card_subtype]
    simpa [hcardX] using hk
  obtain ⟨z₁, z₂, hne, hpre₁, hpre₂⟩ :=
    hgraph GX hconnX hcardSubtype
  refine ⟨z₁.1, z₁.2, z₂.1, z₂.2, ?_, ?_, ?_⟩
  · intro h
    exact hne (Subtype.ext h)
  · exact
      plaquetteGraph_erase_preconnected_of_subtype_compl_preconnected
        (d := d) (L := L) (X := X) z₁ (by simpa [GX] using hpre₁)
  · exact
      plaquetteGraph_erase_preconnected_of_subtype_compl_preconnected
        (d := d) (L := L) (X := X) z₂ (by simpa [GX] using hpre₂)

/-- Physical four-dimensional specialization of unrooted non-cut deletion.

This is the Mathlib-backed part of the F3 recursive-deletion route.  The
root-avoiding strengthening remains open. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_preconnected_unrooted
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k) :
    ∃ z, ∃ hzX : z ∈ X,
      ((plaquetteGraph physicalClayDimension L).induce
        {x | x ∈ X.erase z}).Preconnected :=
  plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_preconnected_unrooted
    (d := physicalClayDimension) (L := L) (k := k) (root := root) (X := X) hX

/-- Physical specialization of the pure finite-graph bridge to the
high-cardinality plaquette two-non-cut target. -/
theorem physicalPlaquetteGraphAnchoredHighCardTwoNonCutExists_of_simpleGraph
    {L : ℕ} [NeZero L]
    (hgraph : SimpleGraphHighCardTwoNonCutExists) :
    PhysicalPlaquetteGraphAnchoredHighCardTwoNonCutExists L :=
  plaquetteGraphAnchoredHighCardTwoNonCutExists_of_simpleGraph
    (d := physicalClayDimension) (L := L) hgraph

/-- High-cardinality two-non-cut deletion for anchored plaquette buckets.

This composes the oracle-clean pure finite-graph theorem with the v2.61
plaquette bookkeeping bridge. -/
theorem plaquetteGraphAnchoredHighCardTwoNonCutExists
    {d L : ℕ} [NeZero d] [NeZero L] :
    PlaquetteGraphAnchoredHighCardTwoNonCutExists d L :=
  plaquetteGraphAnchoredHighCardTwoNonCutExists_of_simpleGraph
    (d := d) (L := L) simpleGraphHighCardTwoNonCutExists

/-- Physical specialization of high-cardinality two-non-cut deletion. -/
theorem physicalPlaquetteGraphAnchoredHighCardTwoNonCutExists
    {L : ℕ} [NeZero L] :
    PhysicalPlaquetteGraphAnchoredHighCardTwoNonCutExists L :=
  physicalPlaquetteGraphAnchoredHighCardTwoNonCutExists_of_simpleGraph
    (L := L) simpleGraphHighCardTwoNonCutExists

/-- Root-avoiding safe deletion in the first nontrivial bucket size.

For `k = 2`, an anchored bucket contains the root and exactly one other
plaquette.  Deleting that non-root plaquette leaves the singleton `{root}`,
which is preconnected.  This closes the base nontrivial case of the
root-avoiding safe-deletion problem without invoking the still-open global
non-cut theorem. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_two
    {d L : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L}
    {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root 2) :
    ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
      X.erase z ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root 1 := by
  classical
  obtain ⟨z, hzX, hz_ne_root⟩ :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_ne_root hX
      (show 1 < 2 from Nat.lt_succ_self 1)
  refine ⟨z, hzX, hz_ne_root, ?_⟩
  unfold plaquetteGraphPreconnectedSubsetsAnchoredCard
  rw [Finset.mem_filter]
  have hroot : root ∈ X :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hX
  have hcardX : X.card = 2 :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_card_eq hX
  have hcardErase : (X.erase z).card = 1 := by
    rw [Finset.card_erase_of_mem hzX, hcardX]
  have hpre :
      ((plaquetteGraph d L).induce {x | x ∈ X.erase z}).Preconnected := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcardErase
    have hsub :
        Subsingleton
          ↑({x : ConcretePlaquette d L | x ∈ X.erase z} :
            Set (ConcretePlaquette d L)) := by
      refine ⟨?_⟩
      intro u v
      apply Subtype.ext
      have hu : u.1 ∈ ({a} : Finset (ConcretePlaquette d L)) := by
        simpa [ha] using u.2
      have hv : v.1 ∈ ({a} : Finset (ConcretePlaquette d L)) := by
        simpa [ha] using v.2
      rw [Finset.mem_singleton] at hu hv
      exact hu.trans hv.symm
    haveI := hsub
    exact SimpleGraph.Preconnected.of_subsingleton
  exact ⟨Finset.mem_univ _, Finset.mem_erase.mpr ⟨hz_ne_root.symm, hroot⟩,
    by simpa using hcardErase, hpre⟩

/-- Physical specialization of the `k = 2` root-avoiding safe-deletion base
case. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_two
    {L : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root 2) :
    ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
      X.erase z ∈
        plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root 1 :=
  plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_two
    (d := physicalClayDimension) (L := L) (root := root) (X := X) hX

/-- Root-avoiding safe deletion for anchored buckets of cardinality three.

Choose a root-neighbor `z` inside the bucket and delete the other non-root
plaquette.  The residual bucket has exactly the two adjacent vertices
`{root, z}`, hence remains preconnected and anchored. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_three
    {d L : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L}
    {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root 3) :
    ∃ y, ∃ hyX : y ∈ X, y ≠ root ∧
      X.erase y ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root 2 := by
  classical
  obtain ⟨z, hzX, hzAdj⟩ :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighbor hX
      (show 1 < 3 from by norm_num)
  have hroot : root ∈ X :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hX
  have hz_ne_root : z ≠ root := hzAdj.ne'
  have hcardX : X.card = 3 :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_card_eq hX
  have hzEraseRoot : z ∈ X.erase root := by
    exact Finset.mem_erase.mpr ⟨hz_ne_root, hzX⟩
  have hcardEraseRoot : (X.erase root).card = 2 := by
    rw [Finset.card_erase_of_mem hroot, hcardX]
  have hcardEraseRootZ : ((X.erase root).erase z).card = 1 := by
    rw [Finset.card_erase_of_mem hzEraseRoot, hcardEraseRoot]
  obtain ⟨y, hySingleton⟩ := Finset.card_eq_one.mp hcardEraseRootZ
  have hyEraseRootZ : y ∈ (X.erase root).erase z := by
    rw [hySingleton]
    simp
  have hyEraseRoot : y ∈ X.erase root := (Finset.mem_erase.mp hyEraseRootZ).2
  have hyX : y ∈ X := (Finset.mem_erase.mp hyEraseRoot).2
  have hy_ne_root : y ≠ root := by
    exact (Finset.mem_erase.mp hyEraseRoot).1
  have hy_ne_z : y ≠ z := by
    exact (Finset.mem_erase.mp hyEraseRootZ).1
  refine ⟨y, hyX, hy_ne_root, ?_⟩
  unfold plaquetteGraphPreconnectedSubsetsAnchoredCard
  rw [Finset.mem_filter]
  have hrootEraseY : root ∈ X.erase y := by
    exact Finset.mem_erase.mpr ⟨hy_ne_root.symm, hroot⟩
  have hzEraseY : z ∈ X.erase y := by
    exact Finset.mem_erase.mpr ⟨hy_ne_z.symm, hzX⟩
  have hcardEraseY : (X.erase y).card = 2 := by
    rw [Finset.card_erase_of_mem hyX, hcardX]
  have hpair_eq :
      ({root, z} : Finset (ConcretePlaquette d L)) = X.erase y := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      rw [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha
      · simpa [ha] using hrootEraseY
      · simpa [ha] using hzEraseY
    · rw [hcardEraseY, Finset.card_pair hzAdj.ne]
  let rV : {x : ConcretePlaquette d L // x ∈ X.erase y} :=
    ⟨root, hrootEraseY⟩
  let zV : {x : ConcretePlaquette d L // x ∈ X.erase y} :=
    ⟨z, hzEraseY⟩
  have hadjInd :
      ((plaquetteGraph d L).induce {x | x ∈ X.erase y}).Adj rV zV := by
    exact SimpleGraph.induce_adj.mpr hzAdj
  have hpre :
      ((plaquetteGraph d L).induce {x | x ∈ X.erase y}).Preconnected := by
    intro u v
    have huPair : u.1 ∈ ({root, z} : Finset (ConcretePlaquette d L)) := by
      rw [hpair_eq]
      exact u.2
    have hvPair : v.1 ∈ ({root, z} : Finset (ConcretePlaquette d L)) := by
      rw [hpair_eq]
      exact v.2
    have huCases : u.1 = root ∨ u.1 = z := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using huPair
    have hvCases : v.1 = root ∨ v.1 = z := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hvPair
    rcases huCases with hu | hu <;> rcases hvCases with hv | hv
    · have hu' : u = rV := Subtype.ext hu
      have hv' : v = rV := Subtype.ext hv
      subst u
      subst v
      exact ⟨SimpleGraph.Walk.nil⟩
    · have hu' : u = rV := Subtype.ext hu
      have hv' : v = zV := Subtype.ext hv
      subst u
      subst v
      exact ⟨SimpleGraph.Walk.cons hadjInd SimpleGraph.Walk.nil⟩
    · have hu' : u = zV := Subtype.ext hu
      have hv' : v = rV := Subtype.ext hv
      subst u
      subst v
      exact ⟨SimpleGraph.Walk.cons hadjInd.symm SimpleGraph.Walk.nil⟩
    · have hu' : u = zV := Subtype.ext hu
      have hv' : v = zV := Subtype.ext hv
      subst u
      subst v
      exact ⟨SimpleGraph.Walk.nil⟩
  exact ⟨Finset.mem_univ _, hrootEraseY, by simpa using hcardEraseY, hpre⟩

/-- Physical specialization of the `k = 3` root-avoiding safe-deletion base
case. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_three
    {L : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root 3) :
    ∃ y, ∃ hyX : y ∈ X, y ≠ root ∧
      X.erase y ∈
        plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root 2 :=
  plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_three
    (d := physicalClayDimension) (L := L) (root := root) (X := X) hX

/-- Combined root-avoiding safe-deletion driver for the proved base zone
`2 ≤ k ≤ 3`.

This packages the v2.55 `k = 2` base case and the v2.58 `k = 3` base case
behind the same interface as the future global safe-deletion theorem. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_le_three
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root : ConcretePlaquette d L}
    {X : Finset (ConcretePlaquette d L)}
    (hk_lower : 2 ≤ k) (hk_upper : k ≤ 3)
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k) :
    ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
      X.erase z ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root (k - 1) := by
  interval_cases k
  · exact plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_two hX
  · exact plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_three hX

/-- Physical specialization of the combined `2 ≤ k ≤ 3` root-avoiding
safe-deletion driver. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_le_three
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hk_lower : 2 ≤ k) (hk_upper : k ≤ 3)
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k) :
    ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
      X.erase z ∈
        plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root (k - 1) :=
  plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_le_three
    (d := physicalClayDimension) (L := L) (k := k) (root := root) (X := X)
    hk_lower hk_upper hX

/-- A high-cardinality two-non-cut theorem plus the already-proved small base
zone is sufficient for exact anchored safe deletion.

This is the v2.60 split of the remaining F3/Klarner obstruction: the local
`2 ≤ k ≤ 3` cases are discharged by v2.59, so future work only needs to prove
the standard two-non-cut graph statement for `4 ≤ k`. -/
theorem plaquetteGraphAnchoredSafeDeletionExists_of_highCardTwoNonCutExists
    {d L : ℕ} [NeZero d] [NeZero L]
    (hhigh : PlaquetteGraphAnchoredHighCardTwoNonCutExists d L) :
    PlaquetteGraphAnchoredSafeDeletionExists d L := by
  intro root k X hk hX
  by_cases hk_small : k ≤ 3
  · exact
      plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_le_three
        (d := d) (L := L) (k := k) (root := root) (X := X)
        hk hk_small hX
  · have hk_high : 4 ≤ k := by omega
    obtain ⟨z₁, hz₁X, z₂, hz₂X, hne, hpre₁, hpre₂⟩ := hhigh hk_high hX
    by_cases hz₁root : z₁ = root
    · refine ⟨z₂, hz₂X, ?_, ?_⟩
      · intro hz₂root
        exact hne (hz₁root.trans hz₂root.symm)
      · exact
          plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_preconnected
            hX hz₂X (by
              intro hz₂root
              exact hne (hz₁root.trans hz₂root.symm)) hpre₂
    · exact ⟨z₁, hz₁X, hz₁root,
        plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_preconnected
          hX hz₁X hz₁root hpre₁⟩

/-- Physical specialization of the high-cardinality two-non-cut plus small
base-zone bridge to exact anchored safe deletion. -/
theorem physicalPlaquetteGraphAnchoredSafeDeletionExists_of_highCardTwoNonCutExists
    {L : ℕ} [NeZero L]
    (hhigh : PhysicalPlaquetteGraphAnchoredHighCardTwoNonCutExists L) :
    PhysicalPlaquetteGraphAnchoredSafeDeletionExists L :=
  plaquetteGraphAnchoredSafeDeletionExists_of_highCardTwoNonCutExists
    (d := physicalClayDimension) (L := L) hhigh

/-- Exact anchored safe deletion for all nontrivial anchored plaquette buckets.

The small base zone `2 ≤ k ≤ 3` is supplied by the existing v2.59 base-case
driver, and the high-cardinality zone is supplied by the v2.63
`SimpleGraphHighCardTwoNonCutExists` closure above. -/
theorem plaquetteGraphAnchoredSafeDeletionExists
    {d L : ℕ} [NeZero d] [NeZero L] :
    PlaquetteGraphAnchoredSafeDeletionExists d L :=
  plaquetteGraphAnchoredSafeDeletionExists_of_highCardTwoNonCutExists
    (d := d) (L := L) plaquetteGraphAnchoredHighCardTwoNonCutExists

/-- Physical specialization of exact anchored safe deletion. -/
theorem physicalPlaquetteGraphAnchoredSafeDeletionExists
    {L : ℕ} [NeZero L] :
    PhysicalPlaquetteGraphAnchoredSafeDeletionExists L :=
  physicalPlaquetteGraphAnchoredSafeDeletionExists_of_highCardTwoNonCutExists
    (L := L) physicalPlaquetteGraphAnchoredHighCardTwoNonCutExists

/-- Exact physical one-step residual handoff for the recursive anchored decoder.

The v2.63 graph-theoretic closure supplies `physicalPlaquetteGraphAnchoredSafeDeletionExists`,
so the older conditional one-step deletion driver can now be used without an
external safe-deletion hypothesis.  This does not yet construct the full
Klarner/BFS decoder: the remaining work is to package the iterated residuals
into a reconstructive finite-alphabet word map. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hk : 2 ≤ k)
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k) :
    ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
      X.erase z ∈
        plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root (k - 1) :=
  physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion
    (L := L) (k := k) (root := root) (X := X)
    physicalPlaquetteGraphAnchoredSafeDeletionExists hk hX

/-- Exact one-step reconstruction contract for the B.2 anchored word decoder.

For each physical root and cardinality `k`, a single decoder
`reconstruct residual symbol` must recover the deleted plaquette from the
residual bucket and one `Fin 1296` symbol for every nontrivial anchored bucket.
This is deliberately a `Prop` target: v2.64 proves that a safe deleted plaquette
exists, while this contract records the still-open injective reconstruction
content needed to iterate those deletions into a full word decoder. -/
def PhysicalPlaquetteGraphDeletedVertexDecoderStep1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ reconstruct :
      Finset (ConcretePlaquette physicalClayDimension L) → Fin 1296 →
        Option (ConcretePlaquette physicalClayDimension L),
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
          X.erase z ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          ∃ symbol : Fin 1296, reconstruct (X.erase z) symbol = some z

/-- A reconstruction-step contract supplies the exact recoverable safe deletion
needed by the B.2 iteration.  This theorem is only a projector from the contract;
it does not prove the contract itself. -/
theorem physicalPlaquetteGraphDeletedVertexDecoderStep1296_exists_recoverable_deletion
    (hstep : PhysicalPlaquetteGraphDeletedVertexDecoderStep1296)
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hk : 2 ≤ k)
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k) :
    ∃ reconstruct :
      Finset (ConcretePlaquette physicalClayDimension L) → Fin 1296 →
        Option (ConcretePlaquette physicalClayDimension L),
    ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
      X.erase z ∈
        plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root (k - 1) ∧
      ∃ symbol : Fin 1296, reconstruct (X.erase z) symbol = some z := by
  obtain ⟨reconstruct, hcover⟩ := hstep root k
  obtain ⟨z, hzX, hz_ne_root, hresidual, symbol, hsymbol⟩ := hcover hk hX
  exact ⟨reconstruct, z, hzX, hz_ne_root, hresidual, symbol, hsymbol⟩

/-- Invert a local plaquette-neighbor step code at a fixed parent.  This is a
finite inverse for an injective code on the actual neighbor finset, not an
existential decoder for deleted vertices. -/
noncomputable def physicalNeighborDecodeOfStepCode
    {L : ℕ} [NeZero L]
    (code : ConcretePlaquette physicalClayDimension L →
      ConcretePlaquette physicalClayDimension L → Fin 1296)
    (p : ConcretePlaquette physicalClayDimension L) (symbol : Fin 1296) :
    Option (ConcretePlaquette physicalClayDimension L) :=
  if h : ∃ q : ConcretePlaquette physicalClayDimension L,
      q ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p ∧
        code p q = symbol then
    some (Classical.choose h)
  else
    none

/-- The local inverse recovers any actual neighbor from its injective step code. -/
theorem physicalNeighborDecodeOfStepCode_spec
    {L : ℕ} [NeZero L]
    {code : ConcretePlaquette physicalClayDimension L →
      ConcretePlaquette physicalClayDimension L → Fin 1296}
    (hinj : ∀ p, Set.InjOn (code p)
      {q | q ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p})
    {p q : ConcretePlaquette physicalClayDimension L}
    (hq : q ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p) :
    physicalNeighborDecodeOfStepCode code p (code p q) = some q := by
  classical
  unfold physicalNeighborDecodeOfStepCode
  have hex : ∃ r : ConcretePlaquette physicalClayDimension L,
      r ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p ∧
        code p r = code p q := ⟨q, hq, rfl⟩
  rw [dif_pos hex]
  apply congrArg some
  have hchosen := Classical.choose_spec hex
  exact hinj p hchosen.1 hq hchosen.2

/-- Residual parent/frontier invariant sufficient to make the B.2 deleted
vertex symbol local.

For each residual bucket produced by a safe deletion, the invariant supplies a
canonical parent selected from the residual and a globally injective local
neighbor code.  At least one admissible deleted plaquette is adjacent to the
selected parent, so a single `Fin 1296` neighbor symbol reconstructs it. -/
def PhysicalPlaquetteGraphResidualParentInvariant1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ parent :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Option (ConcretePlaquette physicalClayDimension L),
    ∃ code : ConcretePlaquette physicalClayDimension L →
      ConcretePlaquette physicalClayDimension L → Fin 1296,
      (∀ p, Set.InjOn (code p)
        {q | q ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p}) ∧
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
          X.erase z ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          ∃ p, parent (X.erase z) = some p ∧
            p ∈ X.erase z ∧
            z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p

/-- Canonical residual-only parent selector for the B.2 deleted-vertex decoder.

This is the exact selector part of `PhysicalPlaquetteGraphResidualParentInvariant1296`,
with the already-proved `Fin 1296` local-neighbor code fact factored out. -/
def PhysicalPlaquetteGraphCanonicalResidualParentSelector1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ parent :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Option (ConcretePlaquette physicalClayDimension L),
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
          X.erase z ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          ∃ p, parent (X.erase z) = some p ∧
            p ∈ X.erase z ∧
            z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p

/-- A fixed residual-only parent selector is compatible with all current
anchored buckets at a fixed root/cardinality.

This isolates the v2.70 blocker: the parent is a function of the residual
bucket alone, while the existential deleted vertex is chosen only after that
residual-only selector has been fixed. -/
def PhysicalPlaquetteGraphResidualExtensionCompatible1296
    {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (parent :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Option (ConcretePlaquette physicalClayDimension L)) : Prop :=
  ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hk : 2 ≤ k)
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k),
    ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
      X.erase z ∈
        plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root (k - 1) ∧
      ∃ p, parent (X.erase z) = some p ∧
        p ∈ X.erase z ∧
        z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p

/-- Residual-extension compatibility is the exact remaining mathematical
content of the canonical residual parent selector. -/
def PhysicalPlaquetteGraphResidualExtensionCompatibility1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ parent :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Option (ConcretePlaquette physicalClayDimension L),
      PhysicalPlaquetteGraphResidualExtensionCompatible1296 root k parent

/-- Once residual-extension compatibility is proved, the canonical residual
parent selector follows immediately.  This is a bridge only: it does not prove
the compatibility theorem. -/
theorem physicalPlaquetteGraphCanonicalResidualParentSelector1296_of_residualExtensionCompatibility1296
    (hcompat : PhysicalPlaquetteGraphResidualExtensionCompatibility1296) :
    PhysicalPlaquetteGraphCanonicalResidualParentSelector1296 := by
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨parent, hparent⟩ := hcompat root k
  exact ⟨parent, hparent⟩

/-- Conversely, the canonical residual parent selector is exactly residual-extension
compatibility with the selector body named separately.  This records that v2.71
did not make the mathematical target easier; it only gave the blocker a sharper
name. -/
theorem physicalPlaquetteGraphResidualExtensionCompatibility1296_of_canonicalResidualParentSelector1296
    (hselector : PhysicalPlaquetteGraphCanonicalResidualParentSelector1296) :
    PhysicalPlaquetteGraphResidualExtensionCompatibility1296 := by
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨parent, hparent⟩ := hselector root k
  exact ⟨parent, hparent⟩

/-- The residual-extension compatibility theorem is definitionally the same
remaining content as the canonical residual-only parent selector. -/
theorem physicalPlaquetteGraphResidualExtensionCompatibility1296_iff_canonicalResidualParentSelector1296 :
    PhysicalPlaquetteGraphResidualExtensionCompatibility1296 ↔
      PhysicalPlaquetteGraphCanonicalResidualParentSelector1296 :=
  ⟨physicalPlaquetteGraphCanonicalResidualParentSelector1296_of_residualExtensionCompatibility1296,
    physicalPlaquetteGraphResidualExtensionCompatibility1296_of_canonicalResidualParentSelector1296⟩

/-- The canonical residual-only selector is exactly the missing mathematical
part of the residual-parent invariant; the `Fin 1296` code is supplied by the
physical neighbor step-code bound. -/
theorem physicalPlaquetteGraphResidualParentInvariant1296_of_canonicalResidualParentSelector1296
    (hselector : PhysicalPlaquetteGraphCanonicalResidualParentSelector1296) :
    PhysicalPlaquetteGraphResidualParentInvariant1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨parent, hparent⟩ := hselector root k
  obtain ⟨code, hinj⟩ :=
    (plaquetteNeighborStepCodeBoundDim_physical_ternary (L := L))
  exact ⟨parent, code, hinj, hparent⟩

/-- A proved residual parent/frontier invariant closes the one-step deleted
vertex decoder contract by composing the parent selector with the local
neighbor-code inverse. -/
theorem physicalPlaquetteGraphDeletedVertexDecoderStep1296_of_residualParentInvariant1296
    (hinv : PhysicalPlaquetteGraphResidualParentInvariant1296) :
    PhysicalPlaquetteGraphDeletedVertexDecoderStep1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨parent, code, hinj, hcover⟩ := hinv root k
  refine ⟨fun residual symbol =>
    match parent residual with
    | some p => physicalNeighborDecodeOfStepCode code p symbol
    | none => none, ?_⟩
  intro X hk hX
  obtain ⟨z, hzX, hz_ne_root, hresidual, p, hparent, _hp_residual, hzp⟩ :=
    hcover hk hX
  refine ⟨z, hzX, hz_ne_root, hresidual, code p z, ?_⟩
  dsimp
  rw [hparent]
  exact physicalNeighborDecodeOfStepCode_spec hinj hzp

/-- A canonical residual-only selector closes the one-step deleted-vertex
decoder contract through the residual-parent invariant bridge. -/
theorem physicalPlaquetteGraphDeletedVertexDecoderStep1296_of_canonicalResidualParentSelector1296
    (hselector : PhysicalPlaquetteGraphCanonicalResidualParentSelector1296) :
    PhysicalPlaquetteGraphDeletedVertexDecoderStep1296 :=
  physicalPlaquetteGraphDeletedVertexDecoderStep1296_of_residualParentInvariant1296
    (physicalPlaquetteGraphResidualParentInvariant1296_of_canonicalResidualParentSelector1296
      hselector)

/-- Strengthened one-step reconstruction contract for the B.2 decoder.

This is a parallel interface to `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296`.
The product symbol records a residual parent/frontier branch together with the
existing local neighbor code.  It deliberately does not claim the original
`Fin 1296` contract or preserve the old alphabet constant. -/
def PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ reconstruct :
      Finset (ConcretePlaquette physicalClayDimension L) →
        (Fin 1296 × Fin 1296) →
        Option (ConcretePlaquette physicalClayDimension L),
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
          X.erase z ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          ∃ symbol : Fin 1296 × Fin 1296,
            reconstruct (X.erase z) symbol = some z

/-- Triple-symbol one-step reconstruction contract for the multi-portal B.2
decoder route.

The three components separately encode a residual portal, a parent inside the
portal-local shell, and the deleted plaquette inside the parent-local shell.
This is intentionally not a compression back to the old `Fin 1296` or
two-component `Fin 1296 × Fin 1296` contracts. -/
def PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ reconstruct :
      Finset (ConcretePlaquette physicalClayDimension L) →
        (Fin 1296 × (Fin 1296 × Fin 1296)) →
        Option (ConcretePlaquette physicalClayDimension L),
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
          X.erase z ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          ∃ symbol : Fin 1296 × (Fin 1296 × Fin 1296),
            reconstruct (X.erase z) symbol = some z

/-- Essential safe-deletion parent-frontier bound for the strengthened symbolic
B.2 decoder.

This is a structured sufficient target for the residual parent-menu bound.  For
fixed `root` and `k`, it chooses a canonical deleted plaquette and a canonical
residual parent for every current anchored bucket.  The finite menu attached to
a residual is required to be exactly the image of those chosen parents over the
fiber of current buckets whose canonical deletion has that residual.  The bound
is therefore on the essential safe-deletion parent image, not on the whole raw
one-step residual frontier. -/
def PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
      (∀ residual,
        essential residual =
          ((plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root k).filter
              (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
      (∀ residual,
        essential residual ⊆ residual ∧ (essential residual).card ≤ 1296) ∧
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X ∈ X ∧
          deleted X ≠ root ∧
          X.erase (deleted X) ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          parentOf X ∈ X.erase (deleted X) ∧
          parentOf X ∈ essential (X.erase (deleted X)) ∧
          deleted X ∈
            (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)

/-- A sharpened interface for the safe-deletion orientation obstruction.  It
does not postulate the `card ≤ 1296` menu bound directly.  Instead, for each
residual bucket it provides an explicit code of the essential chosen-parent menu
into `Fin 1296`, plus injectivity of that code. -/
def PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
    ∃ orientCode :
      ∀ residual,
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
          Fin 1296,
      (∀ residual,
        essential residual =
          ((plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root k).filter
              (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
      (∀ residual, Function.Injective (orientCode residual)) ∧
      (∀ residual, essential residual ⊆ residual) ∧
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X ∈ X ∧
          deleted X ≠ root ∧
          X.erase (deleted X) ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          parentOf X ∈ X.erase (deleted X) ∧
          parentOf X ∈ essential (X.erase (deleted X)) ∧
          deleted X ∈
            (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)

/-- Root-shell safe-deletion intersection for the portal-supported F3 route.

This is stronger than plain safe deletion and stronger than plain first-shell
nonemptiness: it asks for the same deleted plaquette to be safe and adjacent
to the anchored root.  If proved, it supports the cheap portal policy
`portal residual = some root` and `parentOf X = root` in
`PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296`. -/
def PhysicalPlaquetteGraphRootShellSafeDeletionExists1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L} {k : ℕ}
    {X : Finset (ConcretePlaquette physicalClayDimension L)},
    2 ≤ k →
    X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k →
    ∃ z, z ∈ X ∧
      z ≠ root ∧
      z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset root ∧
      X.erase z ∈
        plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root (k - 1)

/-- Multi-portal safe-deletion orientation for the flexible product-symbol F3 route.

This is residual-only but not root-only.  Each residual bucket carries a bounded
menu of portal points, and each essential chosen parent is supported by one
portal-local neighbor shell.  The first two `Fin 1296`-sized choices can encode
the portal and then the parent inside that portal shell; a separate compression
or an additional local deleted-vertex symbol is still required before this can
close the existing two-component deleted-vertex decoder contract. -/
def PhysicalPlaquetteGraphMultiPortalSupportedSafeDeletionOrientation1296x1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
    ∃ portalMenu :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
    ∃ portalOfParent :
      ∀ residual,
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
          ConcretePlaquette physicalClayDimension L,
      (∀ residual,
        essential residual =
          ((plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root k).filter
              (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
      (∀ residual,
        portalMenu residual ⊆ residual ∧ (portalMenu residual).card ≤ 1296) ∧
      (∀ residual
        (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
        portalOfParent residual p ∈ portalMenu residual ∧
          p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
            (portalOfParent residual p)) ∧
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X ∈ X ∧
          deleted X ≠ root ∧
          X.erase (deleted X) ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          parentOf X ∈ X.erase (deleted X) ∧
          parentOf X ∈ essential (X.erase (deleted X)) ∧
          deleted X ∈
            (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)

/-- Base-aware multi-portal safe-deletion orientation for the triple-symbol F3
route.

This is the v2.94 successor interface to the strict multi-portal producer.  It
keeps the residual-only portal menu for non-singleton residuals, but handles the
first nontrivial residual explicitly: when the residual bucket has cardinality
one, the deleted plaquette is decoded directly from the root shell.  Thus the
interface never asks a singleton portal to support itself as a graph neighbor,
and it remains a triple-symbol route rather than a compression back to the old
`Fin 1296` or `Fin 1296 × Fin 1296` contracts. -/
def PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
    ∃ portalMenu :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
    ∃ portalOfParent :
      ∀ residual,
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
          ConcretePlaquette physicalClayDimension L,
      (∀ residual,
        essential residual =
          ((plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root k).filter
              (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
      (∀ residual,
        portalMenu residual ⊆ residual ∧ (portalMenu residual).card ≤ 1296) ∧
      (∀ residual
        (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
        residual.card ≠ 1 →
          portalOfParent residual p ∈ portalMenu residual ∧
            p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
              (portalOfParent residual p)) ∧
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X ∈ X ∧
          deleted X ≠ root ∧
          X.erase (deleted X) ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          parentOf X ∈ X.erase (deleted X) ∧
          parentOf X ∈ essential (X.erase (deleted X)) ∧
          (((X.erase (deleted X)).card = 1 ∧
              parentOf X = root ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
            ((X.erase (deleted X)).card ≠ 1 ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))

/-- Last-step portal-image bound for the base-aware v2.98 route.

This interface factors the residual portal-menu burden one step further.  It
does not postulate a raw residual frontier bound and does not use root-shell
reachability as adjacency.  Instead it asks for a residual-local
`lastStepPortalOfParent` selector whose value is adjacent to each essential
parent, and asks only that the image of this selector over each essential
parent fiber has cardinality at most `1296`. -/
def PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
      (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X ∈ X ∧
          deleted X ≠ root ∧
          X.erase (deleted X) ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          parentOf X ∈ X.erase (deleted X) ∧
          parentOf X ∈ essential (X.erase (deleted X)) ∧
          (((X.erase (deleted X)).card = 1 ∧
              parentOf X = root ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
            ((X.erase (deleted X)).card ≠ 1 ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) ∧
      ∃ lastStepPortalOfParent :
        ∀ residual,
          {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
            ConcretePlaquette physicalClayDimension L,
        (∀ residual,
          essential residual =
            ((plaquetteGraphPreconnectedSubsetsAnchoredCard
                physicalClayDimension L root k).filter
                (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
        (∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
          lastStepPortalOfParent residual p ∈ residual ∧
            (residual.card ≠ 1 →
              p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
                (lastStepPortalOfParent residual p))) ∧
        ∀ residual,
          ((essential residual).attach.image
            (fun p => lastStepPortalOfParent residual p)).card ≤ 1296

/-- Canonical-predecessor-code interface for the base-aware v2.101 last-step
portal-image route.

This is deliberately sharper than `PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296`.
Instead of directly naming only a last-step portal selector, it asks for canonical
residual-local predecessor data carrying both the selected predecessor and a
`Fin 1296` code.  The code-separation clause is the future load-bearing route
for proving the selected-image bound; this interface still records the image
bound explicitly so the bridge to v2.101 is a no-sorry repacking bridge, not a
new cardinality proof. -/
def PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
      (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X ∈ X ∧
          deleted X ≠ root ∧
          X.erase (deleted X) ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          parentOf X ∈ X.erase (deleted X) ∧
          parentOf X ∈ essential (X.erase (deleted X)) ∧
          (((X.erase (deleted X)).card = 1 ∧
              parentOf X = root ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
            ((X.erase (deleted X)).card ≠ 1 ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) ∧
      ∃ canonicalLastStepPredecessor :
        ∀ residual,
          {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} × Fin 1296,
        (∀ residual,
          essential residual =
            ((plaquetteGraphPreconnectedSubsetsAnchoredCard
                physicalClayDimension L root k).filter
                (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
        (∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
          residual.card ≠ 1 →
            p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
              ((canonicalLastStepPredecessor residual p).1.1)) ∧
        (∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
          (canonicalLastStepPredecessor residual p).2 =
              (canonicalLastStepPredecessor residual q).2 →
            (canonicalLastStepPredecessor residual p).1.1 =
              (canonicalLastStepPredecessor residual q).1.1) ∧
        ∀ residual,
          ((essential residual).attach.image
            (fun p => (canonicalLastStepPredecessor residual p).1.1)).card ≤ 1296

/-- Residual-local last-edge data for the canonical predecessor route.

For a residual bucket and target parent `p`, this data packages:

* a proof that `p` itself lies in the residual,
* a selected residual predecessor `q`,
* an induced residual walk from `q` to `p`,
* a `Fin 1296` code attached to the selected predecessor.

The future mathematical burden is to build such data canonically and prove that
the selected predecessor image is `1296`-bounded.  The data is residual-local:
it mentions only the residual bucket and target parent, not a current
deleted-vertex witness `(X, deleted X)`. -/
structure PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData
    {L : ℕ} [NeZero L]
    (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (p : ConcretePlaquette physicalClayDimension L) where
  target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual}
  target_eq : target.1 = p
  predecessor : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}
  path :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      predecessor target
  code : Fin 1296

/-- Residual-local terminal-edge selector data for the v2.135 route.

This is slightly more structured than
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData`: it separates the
canonical residual path endpoint/source data from the terminal predecessor
selected on the final edge.  The load-bearing future theorem is the selected
terminal-predecessor image bound; this data object itself does not prove that
bound and does not mention a current deleted-vertex witness. -/
structure PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeData
    {L : ℕ} [NeZero L]
    (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (p : ConcretePlaquette physicalClayDimension L) where
  target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual}
  target_eq : target.1 = p
  pathSource : {s : ConcretePlaquette physicalClayDimension L // s ∈ residual}
  canonicalPath :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      pathSource target
  terminalPred : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}
  terminalPath :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      terminalPred target
  terminalCode : Fin 1296

/-- Residual-local walk terminal-edge data for the v2.138 route.

This refines the v2.136 terminal-edge data by naming the full residual
`canonicalWalk` and the extracted `terminalSuffix` separately.  The intended
future proof must construct this data from residual-local walk/path information
and prove the selected terminal-predecessor image bound.  This structure does
not use deleted-vertex adjacency outside the residual and does not by itself
bound the selected image. -/
structure PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeData
    {L : ℕ} [NeZero L]
    (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (p : ConcretePlaquette physicalClayDimension L) where
  target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual}
  target_eq : target.1 = p
  walkSource : {s : ConcretePlaquette physicalClayDimension L // s ∈ residual}
  canonicalWalk :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      walkSource target
  terminalPred : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}
  terminalSuffix :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      terminalPred target
  terminalCode : Fin 1296

/-- Residual-local canonical terminal-suffix data for the v2.141 route.

This refines the v2.139 walk terminal-edge data by exposing a residual-local
prefix to the selected terminal predecessor and a final-edge adjacency clause
inside the residual.  The prefix/suffix fields make the selected predecessor a
terminal-suffix datum from residual-local walk/path information, not a
post-hoc deleted-vertex witness.  The structure still does not prove the
selected image bound; that remains a field of the corresponding proposition. -/
structure PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixData
    {L : ℕ} [NeZero L]
    (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (p : ConcretePlaquette physicalClayDimension L) where
  target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual}
  target_eq : target.1 = p
  source : {s : ConcretePlaquette physicalClayDimension L // s ∈ residual}
  canonicalWalk :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      source target
  terminalPred : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}
  prefixToTerminalPred :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      source terminalPred
  terminalSuffix :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      terminalPred target
  terminalSuffix_is_last_edge :
    residual.card ≠ 1 →
      p ∈ (plaquetteGraph physicalClayDimension L).neighborFinset terminalPred.1
  terminalCode : Fin 1296

/-- Residual-local selector evidence for the v2.147 terminal-neighbor image route.

The selected terminal neighbor is an explicit parameter, supplied by the
corresponding selector theorem.  This structure only records the residual-local
canonical walk/prefix/suffix evidence and the final-edge adjacency for that
already selected neighbor.  It is therefore sharper than merely repacking
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborData`: the
selector map and its selected-image cardinality bound remain separate fields of
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296`.

This evidence is not derived from root/root-shell reachability, local degree,
residual size, raw frontier growth, deleted-vertex adjacency outside the
residual, or packing of an already bounded menu. -/
structure PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
    {L : ℕ} [NeZero L]
    (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (p : ConcretePlaquette physicalClayDimension L)
    (terminalNeighbor :
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) where
  target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual}
  target_eq : target.1 = p
  source : {s : ConcretePlaquette physicalClayDimension L // s ∈ residual}
  canonicalWalk :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      source target
  prefixToTerminalNeighbor :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      source terminalNeighbor
  terminalNeighborSuffix :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      terminalNeighbor target
  terminalNeighbor_is_last_edge :
    residual.card ≠ 1 →
      p ∈ (plaquetteGraph physicalClayDimension L).neighborFinset terminalNeighbor.1
  terminalNeighborCode : Fin 1296

/-- Residual-local canonical terminal-neighbor data for the v2.144 route.

This is a predecessor to `PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixData`
that names the selected terminal neighbor directly.  The image bound belongs to
the corresponding proposition below; this structure only records residual-local
canonical walk/prefix/suffix evidence and the final adjacency inside the
residual.  It does not choose a terminal predecessor from a current deleted
vertex witness and does not use deleted-vertex adjacency outside the residual. -/
structure PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborData
    {L : ℕ} [NeZero L]
    (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (p : ConcretePlaquette physicalClayDimension L) where
  target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual}
  target_eq : target.1 = p
  source : {s : ConcretePlaquette physicalClayDimension L // s ∈ residual}
  canonicalWalk :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      source target
  terminalNeighbor : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}
  prefixToTerminalNeighbor :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      source terminalNeighbor
  terminalNeighborSuffix :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      terminalNeighbor target
  terminalNeighbor_is_last_edge :
    residual.card ≠ 1 →
      p ∈ (plaquetteGraph physicalClayDimension L).neighborFinset terminalNeighbor.1
  terminalNeighborCode : Fin 1296

/-- Canonical residual last-edge predecessor selector for the base-aware v2.104
route.

This is deliberately sharper than
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296`:
it does not merely name a selected predecessor and code.  It also exposes
residual-local last-edge path data from which the predecessor is projected.  The
bridge to v2.104 below is only a repacking bridge; this interface still leaves
the actual selector construction as the next mathematical target. -/
def PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
      (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X ∈ X ∧
          deleted X ≠ root ∧
          X.erase (deleted X) ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          parentOf X ∈ X.erase (deleted X) ∧
          parentOf X ∈ essential (X.erase (deleted X)) ∧
          (((X.erase (deleted X)).card = 1 ∧
              parentOf X = root ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
            ((X.erase (deleted X)).card ≠ 1 ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) ∧
      ∃ canonicalLastEdgeData :
        ∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
            PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData
              residual p.1,
        (∀ residual,
          essential residual =
            ((plaquetteGraphPreconnectedSubsetsAnchoredCard
                physicalClayDimension L root k).filter
                (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
        (∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
          residual.card ≠ 1 →
            p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
              ((canonicalLastEdgeData residual p).predecessor.1)) ∧
        (∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
          (canonicalLastEdgeData residual p).code =
              (canonicalLastEdgeData residual q).code →
            (canonicalLastEdgeData residual p).predecessor.1 =
              (canonicalLastEdgeData residual q).predecessor.1) ∧
        ∀ residual,
          ((essential residual).attach.image
            (fun p => (canonicalLastEdgeData residual p).predecessor.1)).card ≤ 1296

/-- Residual-only terminal-predecessor domination target.

This factors the selected last-edge predecessor image bound away from the
base-aware deletion bookkeeping.  It takes only a residual bucket and an
essential parent set inside it, then asks for a residual-local selected
terminal-predecessor menu with an injective `Fin 1296` code.  It is not a raw
frontier bound, not a residual-cardinality bound, not the local degree bound of
one fixed plaquette, and not first-shell/root reachability. -/
def PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (residual essential : Finset (ConcretePlaquette physicalClayDimension L)),
    essential ⊆ residual →
      ∃ terminalPredMenu : Finset (ConcretePlaquette physicalClayDimension L),
      ∃ terminalPredOfParent :
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential} →
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalPredCode :
        {q : ConcretePlaquette physicalClayDimension L //
          q ∈ terminalPredMenu} → Fin 1296,
        terminalPredMenu ⊆ residual ∧
        Function.Injective terminalPredCode ∧
        terminalPredMenu =
          essential.attach.image (fun p => (terminalPredOfParent p).1) ∧
        (∀ p, (terminalPredOfParent p).1 ∈ terminalPredMenu) ∧
        (residual.card ≠ 1 →
          ∀ p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential},
            p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
              (terminalPredOfParent p).1) ∧
        ∀ p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential},
          ∃ target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual},
            target.1 = p.1 ∧
              Nonempty
                (((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
                  (terminalPredOfParent p) target)

/-- Packing interface for a residual-local selected terminal-predecessor menu.

Unlike `PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296`, this
does not claim that arbitrary `essential ⊆ residual` data is last-edge
dominated.  The selected predecessor menu, last-edge domination, residual path
evidence, and cardinality bound are explicit inputs; the interface only asks
for the resulting `Fin 1296` code. -/
def PhysicalPlaquetteGraphResidualDominatedTerminalPredecessorPacking1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (residual essential terminalPredMenu :
      Finset (ConcretePlaquette physicalClayDimension L))
    (terminalPredOfParent :
      {p : ConcretePlaquette physicalClayDimension L // p ∈ essential} →
        {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
    essential ⊆ residual →
    terminalPredMenu ⊆ residual →
    terminalPredMenu =
      essential.attach.image (fun p => (terminalPredOfParent p).1) →
    (∀ p, (terminalPredOfParent p).1 ∈ terminalPredMenu) →
    (residual.card ≠ 1 →
      ∀ p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential},
        p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
          (terminalPredOfParent p).1) →
    (∀ p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential},
      ∃ target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual},
        target.1 = p.1 ∧
          Nonempty
            (((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
              (terminalPredOfParent p) target)) →
    terminalPredMenu.card ≤ 1296 →
      ∃ terminalPredCode :
        {q : ConcretePlaquette physicalClayDimension L // q ∈ terminalPredMenu} →
          Fin 1296,
        Function.Injective terminalPredCode

/-- Residual-fiber canonical last-edge selected-image bound.

This is the canonical-data strengthening of
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`.  It is
indexed by the same v2.121 base-aware bookkeeping data, but it asks first for
canonical residual last-edge data for each essential parent.  The selected
terminal predecessor is then the `predecessor` field of that canonical datum.
The cardinality bound is still an image bound over those selected
predecessors; it is not root reachability, local degree, raw frontier growth,
or deleted-vertex adjacency outside the residual. -/
def PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ canonicalLastEdgeData :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData
              residual p.1,
        (∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual}),
          residual.card ≠ 1 →
            p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
              ((canonicalLastEdgeData residual p).predecessor.1)) ∧
        ∀ residual,
          ((essential residual).attach.image
            (fun p =>
              (canonicalLastEdgeData residual p).predecessor.1)).card ≤ 1296

/-- Residual-fiber canonical terminal-edge selector interface.

This is the v2.135 structural predecessor to
`PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296`.  It asks
for residual-local terminal-edge data, including a canonical residual path
record and a separately selected terminal predecessor.  The selected-image
bound is still explicit and applies to the terminal predecessor image over each
residual fiber.  It is not a root-shell reachability bound, local degree bound,
residual-cardinality bound, raw frontier bound, or deleted-vertex adjacency
outside the residual. -/
def PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalEdgeData :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeData
              residual p.1,
        (∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual}),
          residual.card ≠ 1 →
            p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
              ((terminalEdgeData residual p).terminalPred.1)) ∧
        ∀ residual,
          ((essential residual).attach.image
            (fun p =>
              (terminalEdgeData residual p).terminalPred.1)).card ≤ 1296

/-- Residual-fiber canonical walk terminal-edge selected-image interface.

This is the v2.138 structural predecessor to
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296`.  It asks
for residual-local canonical walk/path data, extraction of an immediate terminal
predecessor, residual suffix evidence to the essential parent, and the selected
terminal-predecessor image bound `<= 1296` over each residual fiber.

It is not a proof from path existence alone, not a root/root-shell reachability
statement, not a local-degree or residual-cardinality bound, not a raw frontier
bound, and not merely packing an already bounded menu.  It also does not use
deleted-vertex adjacency outside the residual as terminal-predecessor data. -/
def PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ walkTerminalEdgeData :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeData
              residual p.1,
        (∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual}),
          residual.card ≠ 1 →
            p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
              ((walkTerminalEdgeData residual p).terminalPred.1)) ∧
        ∀ residual,
          ((essential residual).attach.image
            (fun p =>
              (walkTerminalEdgeData residual p).terminalPred.1)).card ≤ 1296

/-- Residual-fiber canonical terminal-suffix selected-image interface.

This is the v2.141 structural predecessor to
`PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296`.
It separates residual-local canonical walk/path source data, a prefix to the
selected terminal predecessor, terminal-suffix evidence, final-edge adjacency
inside the residual, and the selected terminal-predecessor image bound.

It is not a proof from path existence alone, not root/root-shell reachability,
not a local-degree or residual-size bound, not a raw frontier bound, and not
packing an already bounded menu.  It does not use deleted-vertex adjacency
outside the residual as terminal-predecessor data. -/
def PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalSuffixData :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixData
              residual p.1,
        ∀ residual,
          ((essential residual).attach.image
            (fun p =>
              (terminalSuffixData residual p).terminalPred.1)).card ≤ 1296

/-- Residual-fiber terminal-neighbor selector selected-image interface.

This is the v2.147 structural predecessor to
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296`.
It exposes the residual-indexed selector `terminalNeighborOfParent` as the
load-bearing object, then separately supplies residual-local evidence for that
chosen neighbor and the selected terminal-neighbor image-cardinality bound
`<= 1296` over each v2.121 bookkeeping residual fiber.

The interface deliberately does not treat residual path existence/splitting,
root/root-shell reachability, local degree of one fixed plaquette, residual
size, raw frontier growth, deleted-vertex adjacency outside the residual, or
packing of an already bounded menu as a proof of the selected-image bound. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborOfParent :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalNeighborSelectorEvidence :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
              residual p.1 (terminalNeighborOfParent residual p),
        ∀ residual,
          ((essential residual).attach.image
            (fun p =>
              (terminalNeighborOfParent residual p).1)).card ≤ 1296

/-- Source tags for an ambient residual-value code.

These constructors name the allowed upstream origins for the `Fin 1296` code
used in `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296`.
They are bookkeeping metadata for the interface: the code is meant to come from
base-zone enumeration, v2.121 bookkeeping tags, or canonical-last-edge/frontier
coordinates, never from a selected-image cardinality bound. -/
inductive PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientCodeOrigin where
  | baseZoneEnumeration
  | bookkeepingTag
  | canonicalLastEdgeFrontier
  deriving DecidableEq

/-- Ambient code data for a single residual fiber.

The value code is defined on the whole residual subtype, not on the already
selected terminal-neighbor image.  The `ambientOrigin` field records which
upstream structural source is intended to justify the code in a later proof:
base-zone enumeration, bookkeeping tags, or canonical-last-edge/frontier
coordinates. -/
structure PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCodeData
    {L : ℕ}
    (residual : Finset (ConcretePlaquette physicalClayDimension L)) where
  ambientOrigin :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientCodeOrigin
  ambientValueCode :
    {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296

/-- Bookkeeping-tag code data for a single residual fiber.

This is narrower than
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCodeData`: the
origin is fixed to the v2.121 bookkeeping-tag route.  The code still lives on
the whole residual subtype, not on the selected terminal-neighbor image, so it
cannot be manufactured from a selected-image cardinality bound. -/
structure PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
    {L : ℕ}
    (residual : Finset (ConcretePlaquette physicalClayDimension L)) where
  bookkeepingTagCode :
    {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296

/-- Selector-independent base-zone coordinate data for bookkeeping residual fibers.

The coordinate lives on the whole residual subtype before any fixed selector,
selected terminal-neighbor image, or bounded menu is supplied.  The separation
law is only required on residual values that carry
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from
essential parents. -/
structure PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData
    {L : ℕ} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)) where
  baseZoneTagSpace :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L), Type
  baseZoneTagOfResidualValue :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
        baseZoneTagSpace residual
  baseZoneTagIntoFin1296 :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      baseZoneTagSpace residual → Fin 1296
  selectedAdmissible_injective :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (a b : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 a)) →
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 b)) →
      baseZoneTagIntoFin1296 residual (baseZoneTagOfResidualValue residual a) =
        baseZoneTagIntoFin1296 residual (baseZoneTagOfResidualValue residual b) →
      a.1 = b.1

/-- Selector-admissible base-zone coordinate injection data.

This is a source-facing carrier for the v2.220 recovery interface.  It exposes
a selector-independent base-zone coordinate space, a residual-value coordinate
extractor on the whole residual subtype, an encoding into `Fin 1296`, and the
selected-admissible injectivity law needed to populate the downstream
bookkeeping/base-zone tag coordinate data.

The coordinate data is present before any selected image, bounded menu, or
fixed selector is supplied.  The admissibility hypotheses only restrict the
injectivity law to residual values carrying
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence from
essential parents. -/
structure PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjectionData
    {L : ℕ} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)) where
  baseZoneCoordinateSpace :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L), Type
  baseZoneCoordinateOfResidualValue :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
        baseZoneCoordinateSpace residual
  baseZoneCoordinateIntoFin1296 :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      baseZoneCoordinateSpace residual → Fin 1296
  selectorAdmissible_injective :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (a b : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 a)) →
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 b)) →
      baseZoneCoordinateIntoFin1296 residual
          (baseZoneCoordinateOfResidualValue residual a) =
        baseZoneCoordinateIntoFin1296 residual
          (baseZoneCoordinateOfResidualValue residual b) →
      a.1 = b.1

/-- Proof-relevant selector-admissible base-zone coordinate source data.

This is strictly upstream of
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjectionData`.
It carries a realization relation connecting each residual value to its
base-zone coordinate certificate.  The downstream injection interface is
obtained by erasing those certificates and retaining only the coordinate,
`Fin 1296` encoding, and selected-admissible separation law.

The realization layer is the intended place for a future structural proof that
v2.121 bookkeeping/base-zone data produces selector-independent residual-value
coordinates.  It is not a selected-image cardinality theorem, does not
manufacture codes by `finsetCodeOfCardLe`, and does not use root-shell,
local-neighbor, local-displacement, parent-relative `terminalNeighborCode`,
deleted-X, empirical, or v2.161 cycle routes. -/
structure PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData
    {L : ℕ} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)) where
  baseZoneCoordinateSpace :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L), Type
  baseZoneCoordinateRealizes :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
        baseZoneCoordinateSpace residual → Prop
  baseZoneCoordinateOfResidualValue :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
        {c : baseZoneCoordinateSpace residual //
          baseZoneCoordinateRealizes residual q c}
  baseZoneCoordinateIntoFin1296 :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      baseZoneCoordinateSpace residual → Fin 1296
  selectorAdmissible_realized_injective :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (a b : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual})
      (ca cb : baseZoneCoordinateSpace residual),
      baseZoneCoordinateRealizes residual a ca →
      baseZoneCoordinateRealizes residual b cb →
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 a)) →
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 b)) →
      baseZoneCoordinateIntoFin1296 residual ca =
        baseZoneCoordinateIntoFin1296 residual cb →
      a.1 = b.1

/-- Proof-relevant base-zone coordinate origin/separation data.

This carrier sits strictly upstream of
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData`.
It separates the origin/certificate producing a residual bookkeeping/base-zone
coordinate from the coordinate value later consumed by the source interface.
The bridge to the source interface erases the origin certificates into a
realization relation.

The origin layer is selector-independent and lives on the whole residual
subtype.  It is not a selected-image cardinality argument, bounded-menu
argument, empirical search, `finsetCodeOfCardLe` construction, root-shell,
local-neighbor, local-displacement, parent-relative `terminalNeighborCode`,
deleted-X shortcut, or v2.161 cycle route. -/
structure PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData
    {L : ℕ} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)) where
  baseZoneCoordinateSpace :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L), Type
  baseZoneCoordinateOrigin :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Type
  baseZoneCoordinateOfOrigin :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
        baseZoneCoordinateOrigin residual q →
          baseZoneCoordinateSpace residual
  baseZoneCoordinateOrigin_realizes :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
        baseZoneCoordinateOrigin residual q → Prop
  baseZoneCoordinateOriginOfResidualValue :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
        {origin : baseZoneCoordinateOrigin residual q //
          baseZoneCoordinateOrigin_realizes residual q origin}
  baseZoneCoordinateIntoFin1296 :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      baseZoneCoordinateSpace residual → Fin 1296
  selectorAdmissible_origin_injective :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (a b : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual})
      (oa : baseZoneCoordinateOrigin residual a)
      (ob : baseZoneCoordinateOrigin residual b),
      baseZoneCoordinateOrigin_realizes residual a oa →
      baseZoneCoordinateOrigin_realizes residual b ob →
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 a)) →
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 b)) →
      baseZoneCoordinateIntoFin1296 residual
          (baseZoneCoordinateOfOrigin residual a oa) =
        baseZoneCoordinateIntoFin1296 residual
          (baseZoneCoordinateOfOrigin residual b ob) →
      a.1 = b.1

/-- Concrete base-zone origin certificate source data.

This carrier sits strictly upstream of
`PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData`.
It separates the provenance source for an origin certificate from the erased
certificate consumed by the v2.224 realization/separation layer.  The source is
selector-independent and lives on the whole residual subtype; selected
admissibility appears only in the certificate-level separation law.

It is not a selected-image cardinality argument, bounded-menu argument,
empirical search, `finsetCodeOfCardLe` construction, root-shell, local-neighbor,
local-displacement, parent-relative `terminalNeighborCode`, deleted-X shortcut,
or v2.161 cycle route. -/
structure PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSourceData
    {L : ℕ} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)) where
  baseZoneCoordinateSpace :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L), Type
  baseZoneOriginCertificate :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Type
  baseZoneOriginCertificateSource :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Type
  baseZoneOriginCertificateOfSource :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
        baseZoneOriginCertificateSource residual q →
          baseZoneOriginCertificate residual q
  baseZoneOriginSourceOfResidualValue :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
        baseZoneOriginCertificateSource residual q
  baseZoneOriginSource_valid :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
        baseZoneOriginCertificateSource residual q → Prop
  baseZoneOriginSourceOfResidualValue_valid :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
        baseZoneOriginSource_valid residual q
          (baseZoneOriginSourceOfResidualValue residual q)
  baseZoneOriginCertificate_realizes :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
        baseZoneOriginCertificate residual q → Prop
  baseZoneOriginCertificateOfSource_realizes :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
        (source : baseZoneOriginCertificateSource residual q) →
          baseZoneOriginSource_valid residual q source →
            baseZoneOriginCertificate_realizes residual q
              (baseZoneOriginCertificateOfSource residual q source)
  baseZoneCoordinateOfCertificate :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
        baseZoneOriginCertificate residual q →
          baseZoneCoordinateSpace residual
  baseZoneCoordinateIntoFin1296 :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      baseZoneCoordinateSpace residual → Fin 1296
  selectorAdmissible_certificate_injective :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (a b : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual})
      (ca : baseZoneOriginCertificate residual a)
      (cb : baseZoneOriginCertificate residual b),
      baseZoneOriginCertificate_realizes residual a ca →
      baseZoneOriginCertificate_realizes residual b cb →
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 a)) →
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 b)) →
      baseZoneCoordinateIntoFin1296 residual
          (baseZoneCoordinateOfCertificate residual a ca) =
      baseZoneCoordinateIntoFin1296 residual
          (baseZoneCoordinateOfCertificate residual b cb) →
      a.1 = b.1

/-- Selector-independent residual-value code separation data.

This carrier is strictly upstream of
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealizationData`.
It exposes only the residual-value code into `Fin 1296` on the whole residual
subtype and the selected-admissible equality-reflection law needed to populate a
trivial realization layer.

It is not a selected-image cardinality argument, bounded-menu argument,
empirical search, `finsetCodeOfCardLe` construction, root-shell, local-neighbor,
local-displacement, parent-relative `terminalNeighborCode`, deleted-X shortcut,
or v2.161 cycle route. -/
structure
  PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData
    {L : ℕ} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)) where
  residualValueCode :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
        Fin 1296
  selectorAdmissible_code_injective :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (a b : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 a)) →
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 b)) →
      residualValueCode residual a =
        residualValueCode residual b →
      a.1 = b.1

/-- Proof-relevant residual-value code realization data.

This carrier is strictly upstream of
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSourceData`.  It
exposes a selector-independent realization/certificate type for every value of
the whole residual subtype, a distinguished valid realization, code extraction
from realizations into `Fin 1296`, realization-choice stability, and
selected-admissible equality-reflection for values carrying terminal-neighbor
selector data from essential parents.

It is not a selected-image cardinality argument, bounded-menu argument,
empirical search, `finsetCodeOfCardLe` construction, root-shell, local-neighbor,
local-displacement, parent-relative `terminalNeighborCode`, deleted-X shortcut,
or v2.161 cycle route. -/
structure
  PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealizationData
    {L : ℕ} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)) where
  residualValueCodeRealization :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Type
  residualValueCodeRealizationOfValue :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      residualValueCodeRealization residual q
  residualValueCodeRealization_valid :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      residualValueCodeRealization residual q → Prop
  residualValueCodeRealizationOfValue_valid :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      residualValueCodeRealization_valid residual q
        (residualValueCodeRealizationOfValue residual q)
  residualValueCodeOfRealization :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      residualValueCodeRealization residual q → Fin 1296
  residualValueCode_realization_ext :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual})
      (s t : residualValueCodeRealization residual q),
      residualValueCodeRealization_valid residual q s →
      residualValueCodeRealization_valid residual q t →
      residualValueCodeOfRealization residual q s =
        residualValueCodeOfRealization residual q t
  selectorAdmissible_realizedCode_injective :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (a b : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 a)) →
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 b)) →
      residualValueCodeOfRealization residual a
          (residualValueCodeRealizationOfValue residual a) =
        residualValueCodeOfRealization residual b
          (residualValueCodeRealizationOfValue residual b) →
      a.1 = b.1

/-- Proof-relevant residual-value code source data.

This carrier is strictly upstream of
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData`.
It exposes a source/certificate type for every value of the whole residual
subtype, a distinguished valid source witness, a code extracted from valid
sources into `Fin 1296`, and selected-admissible equality-reflection for values
carrying terminal-neighbor selector data from essential parents.

It is not a selected-image cardinality argument, bounded-menu argument,
empirical search, `finsetCodeOfCardLe` construction, root-shell, local-neighbor,
local-displacement, parent-relative `terminalNeighborCode`, deleted-X shortcut,
or v2.161 cycle route. -/
structure
  PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSourceData
    {L : ℕ} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)) where
  residualValueCodeSource :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Type
  residualValueCodeSourceOfValue :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      residualValueCodeSource residual q
  residualValueSource_valid :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      residualValueCodeSource residual q → Prop
  residualValueCodeSourceOfValue_valid :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      residualValueSource_valid residual q
        (residualValueCodeSourceOfValue residual q)
  residualValueCodeOfSource :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      residualValueCodeSource residual q → Fin 1296
  residualValueCode_source_ext :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual})
      (s t : residualValueCodeSource residual q),
      residualValueSource_valid residual q s →
      residualValueSource_valid residual q t →
      residualValueCodeOfSource residual q s =
        residualValueCodeOfSource residual q t
  selectorAdmissible_sourceCode_injective :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (a b : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 a)) →
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 b)) →
      residualValueCodeOfSource residual a
          (residualValueCodeSourceOfValue residual a) =
        residualValueCodeOfSource residual b
          (residualValueCodeSourceOfValue residual b) →
      a.1 = b.1

/-- Selector-independent residual-value certificate-code injection data.

This carrier is strictly upstream of
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSourceData`.
It exposes only a code into `Fin 1296` on the whole residual subtype and the
selected-admissible equality-reflection principle needed by the richer source
carrier.

It is not a selected-image cardinality argument, bounded-menu argument,
empirical search, `finsetCodeOfCardLe` construction, root-shell, local-neighbor,
local-displacement, parent-relative `terminalNeighborCode`, deleted-X shortcut,
or v2.161 cycle route. -/
structure
  PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData
    {L : ℕ} [NeZero L]
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)) where
  baseZoneOriginCertificateCode :
    ∀ residual : Finset (ConcretePlaquette physicalClayDimension L),
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
        Fin 1296
  selectorAdmissible_code_injective :
    ∀ (residual : Finset (ConcretePlaquette physicalClayDimension L))
      (a b : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 a)) →
      (∃ p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual},
        Nonempty
          (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 b)) →
      baseZoneOriginCertificateCode residual a =
        baseZoneOriginCertificateCode residual b →
      a.1 = b.1

/-- Residual-fiber terminal-neighbor selector source interface.

This is the upstream v2.181 source contract for the selector part of
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296`.  It exposes only
the residual-local `terminalNeighborOfParent` selector and the corresponding
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`.

It deliberately does not carry a residual-value tag map, selected-value
separation, selected-image cardinality, or a code manufactured by
`finsetCodeOfCardLe`.  It is also not justified here by residual paths alone,
root-shell reachability alone, local degree, residual size, raw frontier,
deleted-vertex adjacency, local displacement codes, parent-relative
`terminalNeighborCode` equality, empirical search, or post-hoc choices from a
current deletion witness. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborOfParent :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalNeighborSelectorEvidence :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
              residual p.1 (terminalNeighborOfParent residual p),
        True

/-- Bookkeeping tag-code interface relative to a fixed terminal-neighbor selector.

This is separated from
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296` so the
selector-source interface remains selector-only.  Given the same v2.121
bookkeeping hypotheses, a fixed residual-local `terminalNeighborOfParent`, and
its selector evidence, this contract supplies the residual-subtype
bookkeeping-tag map and selected-value separation needed by
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296`.

The code lives on the whole residual subtype; it is not derived from
selected-image cardinality, `finsetCodeOfCardLe`, local displacement codes,
parent-relative `terminalNeighborCode` equality, empirical search, or the
v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
    (terminalNeighborOfParent :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
    (∀ residual,
      (p : {p : ConcretePlaquette physicalClayDimension L //
        p ∈ essential residual}) →
        PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
          residual p.1 (terminalNeighborOfParent residual p)) →
      ∃ bookkeepingTagCode :
        ∀ residual,
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
            Fin 1296,
        ∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          bookkeepingTagCode residual (terminalNeighborOfParent residual p) =
            bookkeepingTagCode residual (terminalNeighborOfParent residual q) →
            (terminalNeighborOfParent residual p).1 =
              (terminalNeighborOfParent residual q).1

/-- Residual bookkeeping/base-zone coordinate source for the tag-space injection
route.  The source returns named base-zone coordinate data on the whole
residual subtype before any selected image, bounded menu, or fixed selector code
is supplied; admissibility only restricts the separation statement to residual
values carrying terminal-neighbor selector evidence from essential parents.

This interface does not obtain its code from selected-image cardinality, bounded
menu cardinality, empirical search, `finsetCodeOfCardLe`, root-shell codes,
local neighbor or displacement codes, parent-relative `terminalNeighborCode`
equality, deleted-vertex adjacency outside the residual, or the v2.161
selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      Nonempty
        (PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData
          (L := L) essential)

/-- Selector-admissible residual bookkeeping/base-zone coordinate injection
source.

This upstream interface isolates the source of the v2.218 base-zone coordinate
data.  For each v2.121 bookkeeping residual fiber it supplies coordinate data
on the whole residual subtype before any selected image, bounded menu, or fixed
selector is supplied, together with selected-admissible injectivity for values
carrying terminal-neighbor selector evidence from essential parents.

It does not obtain its code from selected-image cardinality, bounded menu
cardinality, empirical search, `finsetCodeOfCardLe`, root-shell codes, local
neighbor or displacement codes, parent-relative `terminalNeighborCode`
equality, deleted-vertex adjacency outside the residual, or the v2.161
selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      Nonempty
        (PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjectionData
          (L := L) essential)

/-- Selector-admissible residual bookkeeping/base-zone coordinate source.

This interface is stricter than the v2.220 injection interface: it exposes a
proof-relevant realization relation tying each residual value to a base-zone
coordinate certificate before the certificate is erased into coordinate
injection data.  It is therefore an origin/source contract, not merely a
renaming of
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`.

It does not obtain its code from selected-image cardinality, bounded menu
cardinality, empirical search, `finsetCodeOfCardLe`, root-shell codes, local
neighbor or displacement codes, parent-relative `terminalNeighborCode`
equality, deleted-vertex adjacency outside the residual, or the v2.161
selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      Nonempty
        (PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData
          (L := L) essential)

/-- Proof-relevant base-zone coordinate realization/separation interface.

This is an upstream source contract for
`PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296`.
It provides a selector-independent origin/certificate layer for residual
bookkeeping/base-zone coordinates on the whole residual subtype.  The
downstream source interface should be obtained only by erasing these origin
certificates into coordinate realizations.

It does not obtain its code or separation law from selected-image cardinality,
bounded menu cardinality, empirical search, `finsetCodeOfCardLe`, root-shell
codes, local neighbor or displacement codes, parent-relative
`terminalNeighborCode` equality, deleted-vertex adjacency outside the residual,
or the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      Nonempty
        (PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData
          (L := L) essential)

/-- Concrete base-zone origin certificate source interface.

This is upstream of
`PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296`.
It exposes provenance/certificate-source data that can be erased into the
v2.224 origin layer, rather than assuming the origin layer directly.

It does not obtain its code or separation law from selected-image cardinality,
bounded menu cardinality, empirical search, `finsetCodeOfCardLe`, root-shell
codes, local neighbor or displacement codes, parent-relative
`terminalNeighborCode` equality, deleted-vertex adjacency outside the residual,
or the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      Nonempty
        (PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSourceData
          (L := L) essential)

/-- Selector-independent residual-value code separation interface.

This is strictly upstream of
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296`.
It supplies the actual code into `Fin 1296` on the whole residual subtype and
the selected-admissible equality-reflection law for values carrying
terminal-neighbor selector data from essential parents.  The downstream
realization interface is obtained by adding a trivial `Unit` realization layer.

The interface does not obtain its code from selected-image cardinality, bounded
menu cardinality, empirical search, `finsetCodeOfCardLe`, root-shell codes,
local neighbor or displacement codes, parent-relative `terminalNeighborCode`
equality, deleted-X shortcuts, or the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      Nonempty
        (PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData
          (L := L) essential)

/-- Realization-level source for residual-value codes.

This is strictly upstream of
`PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296`.  It
supplies proof-relevant realization/certificate data for residual-value codes
into `Fin 1296` on the whole residual subtype, together with selected-admissible
equality-reflection for values carrying terminal-neighbor selector data from
essential parents.

The interface does not obtain its code from selected-image cardinality, bounded
menu cardinality, empirical search, `finsetCodeOfCardLe`, root-shell codes,
local neighbor or displacement codes, parent-relative `terminalNeighborCode`
equality, deleted-X shortcuts, or the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      Nonempty
        (PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealizationData
          (L := L) essential)

/-- Proof-relevant residual-value code source interface.

This is strictly upstream of
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296`.
It supplies a selector-independent source layer for residual-value codes into
`Fin 1296` on the whole residual subtype, together with selected-admissible
equality-reflection for values carrying terminal-neighbor selector data from
essential parents.

The interface does not obtain its code from selected-image cardinality, bounded
menu cardinality, empirical search, `finsetCodeOfCardLe`, root-shell codes,
local neighbor or displacement codes, parent-relative `terminalNeighborCode`
equality, deleted-X shortcuts, or the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      Nonempty
        (PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSourceData
          (L := L) essential)

/-- Selector-independent base-zone origin certificate code-injection interface.

This is the focused upstream source for
`PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296`.  It
provides only a residual-value code into `Fin 1296` on the whole residual
subtype and selected-admissible equality-reflection for values carrying
terminal-neighbor selector data from essential parents. -/
def PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      Nonempty
        (PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData
          (L := L) essential)

/-- Residual bookkeeping/base-zone tag-space injection source for the
selector-admissible bookkeeping-tag route.  The tag space and extractor live on
the whole residual subtype before any selected image or bounded menu is
introduced; admissibility only restricts the separation statement to residual
values carrying terminal-neighbor selector evidence from essential parents.

This interface does not obtain its code from selected-image cardinality, bounded
menu cardinality, empirical search, `finsetCodeOfCardLe`, root-shell codes,
local neighbor or displacement codes, parent-relative `terminalNeighborCode`
equality, deleted-vertex adjacency outside the residual, or the v2.161
selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ bookkeepingTagSpace : ∀ residual, Type,
      ∃ bookkeepingTagOfResidualVertex :
        ∀ residual,
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
            bookkeepingTagSpace residual,
      ∃ bookkeepingTagIntoFin1296 :
        ∀ residual, bookkeepingTagSpace residual → Fin 1296,
        ∀ residual
          (a b : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
          (∃ p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual},
            Nonempty
              (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
                residual p.1 a)) →
          (∃ p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual},
            Nonempty
              (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
                residual p.1 b)) →
          bookkeepingTagIntoFin1296 residual
              (bookkeepingTagOfResidualVertex residual a) =
            bookkeepingTagIntoFin1296 residual
              (bookkeepingTagOfResidualVertex residual b) →
          a.1 = b.1

/-- Selector-admissible residual bookkeeping/base-zone tag injection source.

This is the v2.209 interface source for admissible-value separation.  For the
v2.121 bookkeeping residual fibers, it exposes bookkeeping/base-zone tag code
data on the whole residual subtype before any fixed
`terminalNeighborOfParent` selector, selected image, or bounded menu is
supplied.  Its separation clause only applies to residual values carrying
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
from essential parents.

This is deliberately not a selected-image cardinality theorem.  It does not
manufacture the code by `finsetCodeOfCardLe`, bounded menu cardinality,
empirical search, root-shell codes, local neighbor or displacement codes,
parent-relative `terminalNeighborCode` equality, deleted-vertex adjacency
outside the residual, or the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ bookkeepingTagCodeData :
        ∀ residual,
          PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
            residual,
        ∀ residual
          (a b : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
          (∃ p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual},
            Nonempty
              (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
                residual p.1 a)) →
          (∃ p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual},
            Nonempty
              (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
                residual p.1 b)) →
          (bookkeepingTagCodeData residual).bookkeepingTagCode a =
            (bookkeepingTagCodeData residual).bookkeepingTagCode b →
      a.1 = b.1

/-- A selector-admissible base-zone coordinate injection source supplies the
bookkeeping/base-zone tag coordinate interface by projecting its coordinate
space, residual-value extractor, `Fin 1296` encoding, and admissible
injectivity law into the downstream carrier. -/
theorem physicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
    (hinjection :
      PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296) :
    PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296 := by
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨coordinateInjectionData⟩ :=
    hinjection root k deleted parentOf essential hchoice himage hessential_subset
  exact ⟨
    { baseZoneTagSpace :=
        coordinateInjectionData.baseZoneCoordinateSpace
      baseZoneTagOfResidualValue :=
        coordinateInjectionData.baseZoneCoordinateOfResidualValue
      baseZoneTagIntoFin1296 :=
        coordinateInjectionData.baseZoneCoordinateIntoFin1296
      selectedAdmissible_injective :=
        coordinateInjectionData.selectorAdmissible_injective }⟩

/-- A proof-relevant base-zone coordinate source supplies the v2.220
selector-admissible coordinate injection interface by erasing realization
certificates. -/
theorem physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
    (hsource :
      PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296) :
    PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296 := by
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨sourceData⟩ :=
    hsource root k deleted parentOf essential hchoice himage hessential_subset
  refine ⟨
    { baseZoneCoordinateSpace :=
        sourceData.baseZoneCoordinateSpace
      baseZoneCoordinateOfResidualValue :=
        fun residual q => (sourceData.baseZoneCoordinateOfResidualValue residual q).1
      baseZoneCoordinateIntoFin1296 :=
        sourceData.baseZoneCoordinateIntoFin1296
      selectorAdmissible_injective := ?_ }⟩
  intro residual a b ha hb hcode
  exact
    sourceData.selectorAdmissible_realized_injective residual a b
      ((sourceData.baseZoneCoordinateOfResidualValue residual a).1)
      ((sourceData.baseZoneCoordinateOfResidualValue residual b).1)
      ((sourceData.baseZoneCoordinateOfResidualValue residual a).2)
      ((sourceData.baseZoneCoordinateOfResidualValue residual b).2)
      ha hb hcode

/-- A proof-relevant base-zone coordinate origin/separation source supplies the
v2.222 selector-admissible coordinate source interface by erasing origin
certificates into coordinate realizations. -/
theorem physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296_of_baseZoneCoordinateRealizationSeparation1296
    (hrealization :
      PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296) :
    PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296 := by
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨realizationData⟩ :=
    hrealization root k deleted parentOf essential hchoice himage hessential_subset
  refine ⟨
    { baseZoneCoordinateSpace :=
        realizationData.baseZoneCoordinateSpace
      baseZoneCoordinateRealizes := ?_
      baseZoneCoordinateOfResidualValue := ?_
      baseZoneCoordinateIntoFin1296 :=
        realizationData.baseZoneCoordinateIntoFin1296
      selectorAdmissible_realized_injective := ?_ }⟩
  · intro residual q c
    exact
      ∃ origin : realizationData.baseZoneCoordinateOrigin residual q,
        realizationData.baseZoneCoordinateOrigin_realizes residual q origin ∧
          realizationData.baseZoneCoordinateOfOrigin residual q origin = c
  · intro residual q
    let origin := realizationData.baseZoneCoordinateOriginOfResidualValue residual q
    exact
      ⟨realizationData.baseZoneCoordinateOfOrigin residual q origin.1,
        ⟨origin.1, origin.2, rfl⟩⟩
  · intro residual a b ca cb ha_real hb_real ha hb hcode
    rcases ha_real with ⟨oa, hoa, hca⟩
    rcases hb_real with ⟨ob, hob, hcb⟩
    exact
      realizationData.selectorAdmissible_origin_injective residual a b oa ob
        hoa hob ha hb (by
          simpa [hca, hcb] using hcode)

/-- A concrete base-zone origin certificate source supplies the v2.224
realization/separation interface by erasing source provenance into origin
certificates. -/
theorem physicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296_of_baseZoneOriginCertificateSource1296
    (hsource :
      PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296) :
    PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296 := by
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨sourceData⟩ :=
    hsource root k deleted parentOf essential hchoice himage hessential_subset
  refine ⟨
    { baseZoneCoordinateSpace :=
        sourceData.baseZoneCoordinateSpace
      baseZoneCoordinateOrigin :=
        sourceData.baseZoneOriginCertificate
      baseZoneCoordinateOfOrigin :=
        sourceData.baseZoneCoordinateOfCertificate
      baseZoneCoordinateOrigin_realizes :=
        sourceData.baseZoneOriginCertificate_realizes
      baseZoneCoordinateOriginOfResidualValue := ?_
      baseZoneCoordinateIntoFin1296 :=
        sourceData.baseZoneCoordinateIntoFin1296
      selectorAdmissible_origin_injective := ?_ }⟩
  · intro residual q
    let source := sourceData.baseZoneOriginSourceOfResidualValue residual q
    exact
      ⟨sourceData.baseZoneOriginCertificateOfSource residual q source,
        sourceData.baseZoneOriginCertificateOfSource_realizes residual q source
          (sourceData.baseZoneOriginSourceOfResidualValue_valid residual q)⟩
  · intro residual a b oa ob hoa hob ha hb hcode
    exact
      sourceData.selectorAdmissible_certificate_injective residual a b oa ob
        hoa hob ha hb hcode

/-- A selector-independent residual-value code separation theorem supplies the
v2.232 realization layer by adding a trivial `Unit` realization certificate. -/
theorem physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296_of_baseZoneResidualValueCodeSeparation1296
    (hseparation :
      PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296) :
    PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296 := by
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨separationData⟩ :=
    hseparation root k deleted parentOf essential hchoice himage
      hessential_subset
  refine ⟨
    { residualValueCodeRealization := fun _ _ => Unit
      residualValueCodeRealizationOfValue := fun _ _ => ()
      residualValueCodeRealization_valid := fun _ _ _ => True
      residualValueCodeRealizationOfValue_valid := fun _ _ => trivial
      residualValueCodeOfRealization := fun residual q _ =>
        separationData.residualValueCode residual q
      residualValueCode_realization_ext := ?_
      selectorAdmissible_realizedCode_injective := ?_ }⟩
  · intro residual q s t hs ht
    rfl
  · intro residual a b ha hb hcode
    exact
      separationData.selectorAdmissible_code_injective residual a b ha hb
        hcode

/-- A residual-value code realization layer supplies the v2.230 source layer by
erasing realization certificates into source witnesses. -/
theorem physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296_of_baseZoneResidualValueCodeRealization1296
    (hrealization :
      PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296) :
    PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296 := by
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨realizationData⟩ :=
    hrealization root k deleted parentOf essential hchoice himage hessential_subset
  refine ⟨
    { residualValueCodeSource :=
        realizationData.residualValueCodeRealization
      residualValueCodeSourceOfValue :=
        realizationData.residualValueCodeRealizationOfValue
      residualValueSource_valid :=
        realizationData.residualValueCodeRealization_valid
      residualValueCodeSourceOfValue_valid :=
        realizationData.residualValueCodeRealizationOfValue_valid
      residualValueCodeOfSource :=
        realizationData.residualValueCodeOfRealization
      residualValueCode_source_ext :=
        realizationData.residualValueCode_realization_ext
      selectorAdmissible_sourceCode_injective := ?_ }⟩
  intro residual a b ha hb hcode
  exact
    realizationData.selectorAdmissible_realizedCode_injective
      residual a b ha hb hcode

/-- A proof-relevant residual-value code source supplies the focused
base-zone origin certificate code-injection interface by forgetting the source
layer and retaining only the distinguished residual-value code and its
selected-admissible equality-reflection law. -/
theorem physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_baseZoneResidualValueCodeSource1296
    (hsource :
      PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296) :
    PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296 := by
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨sourceData⟩ :=
    hsource root k deleted parentOf essential hchoice himage hessential_subset
  refine ⟨
    { baseZoneOriginCertificateCode := fun residual q =>
        sourceData.residualValueCodeOfSource residual q
          (sourceData.residualValueCodeSourceOfValue residual q)
      selectorAdmissible_code_injective := ?_ }⟩
  intro residual a b ha hb hcode
  exact
    sourceData.selectorAdmissible_sourceCode_injective residual a b ha hb hcode

/-- A selector-independent residual-value certificate code supplies the richer
base-zone origin certificate source interface by using `Fin 1296` as the
coordinate space and trivial origin certificates. -/
theorem physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296_of_baseZoneOriginCertificateCodeInjection1296
    (hcode :
      PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296) :
    PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296 := by
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨codeData⟩ :=
    hcode root k deleted parentOf essential hchoice himage hessential_subset
  refine ⟨
    { baseZoneCoordinateSpace := fun _ => Fin 1296
      baseZoneOriginCertificate := fun _ _ => Unit
      baseZoneOriginCertificateSource := fun _ _ => Unit
      baseZoneOriginCertificateOfSource := fun _ _ _ => ()
      baseZoneOriginSourceOfResidualValue := fun _ _ => ()
      baseZoneOriginSource_valid := fun _ _ _ => True
      baseZoneOriginSourceOfResidualValue_valid := fun _ _ => trivial
      baseZoneOriginCertificate_realizes := fun _ _ _ => True
      baseZoneOriginCertificateOfSource_realizes := fun _ _ _ _ => trivial
      baseZoneCoordinateOfCertificate := fun residual q _ =>
        codeData.baseZoneOriginCertificateCode residual q
      baseZoneCoordinateIntoFin1296 := fun _ code => code
      selectorAdmissible_certificate_injective := ?_ }⟩
  intro residual a b _ca _cb _hca _hcb ha hb hcode_eq
  exact
    codeData.selectorAdmissible_code_injective residual a b ha hb hcode_eq

/-- A selector-independent base-zone coordinate source supplies the residual
bookkeeping tag-space injection interface by projecting its tag space,
residual-value extractor, `Fin 1296` encoding, and selected-admissible
injectivity law. -/
theorem physicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296
    (hcoordinate :
      PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296) :
    PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296 := by
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨coordinateData⟩ :=
    hcoordinate root k deleted parentOf essential hchoice himage hessential_subset
  exact ⟨coordinateData.baseZoneTagSpace,
    coordinateData.baseZoneTagOfResidualValue,
    coordinateData.baseZoneTagIntoFin1296,
    coordinateData.selectedAdmissible_injective⟩

/-- A residual bookkeeping tag space injection supplies the selector-admissible
bookkeeping tag injection interface by composing its residual-value tag
extractor with the fixed `Fin 1296` encoding. -/
theorem physicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296_of_residualFiberBookkeepingTagSpaceInjection1296
    (htagSpace :
      PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296) :
    PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296 := by
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨bookkeepingTagSpace, bookkeepingTagOfResidualVertex,
      bookkeepingTagIntoFin1296, hseparates⟩ :=
    htagSpace root k deleted parentOf essential hchoice himage hessential_subset
  let bookkeepingTagCodeData :
      ∀ residual,
        PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
          residual :=
    fun residual =>
      { bookkeepingTagCode := fun q =>
          bookkeepingTagIntoFin1296 residual
            (bookkeepingTagOfResidualVertex residual q) }
  refine ⟨bookkeepingTagCodeData, ?_⟩
  intro residual a b ha hb hcode
  exact hseparates residual a b ha hb hcode

/-- Selector-admissible residual-value bookkeeping tag separation source.

This is the admissible-value separation interface isolated by v2.206.  For the
v2.121 bookkeeping residual fibers, it exposes bookkeeping/base-zone tag code
data on the whole residual subtype before any fixed `terminalNeighborOfParent`
selector is supplied.  Its separation clause applies to residual values that
are admissible through `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`
evidence from essential parents.

This is deliberately not a selected-image cardinality theorem.  It does not
manufacture the code by `finsetCodeOfCardLe`, bounded menu cardinality,
empirical search, root-shell codes, local neighbor or displacement codes,
parent-relative `terminalNeighborCode` equality, deleted-vertex adjacency
outside the residual, or the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ bookkeepingTagCodeData :
        ∀ residual,
          PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
            residual,
        ∀ residual
          (a b : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
          (∃ p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual},
            Nonempty
              (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
                residual p.1 a)) →
          (∃ p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual},
            Nonempty
              (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
                residual p.1 b)) →
          (bookkeepingTagCodeData residual).bookkeepingTagCode a =
            (bookkeepingTagCodeData residual).bookkeepingTagCode b →
          a.1 = b.1

/-- A selector-admissible bookkeeping-tag injection source supplies the
admissible-value separation interface by direct repackaging.

The source already carries a residual-subtype bookkeeping/base-zone tag code
before any fixed selector, selected image, or bounded menu is supplied, and its
separation law is exactly the selected-admissible residual-value separation
needed downstream. -/
theorem physicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296_of_residualFiberSelectorAdmissibleBookkeepingTagInjection1296
    (hinjection :
      PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296) :
    PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296 := by
  exact hinjection

/-- Structural residual bookkeeping/base-zone coordinate source.

This is the coordinate-first interface isolated by v2.203.  For the v2.121
bookkeeping residual fibers, it exposes bookkeeping/base-zone tag code data on
the whole residual subtype before any fixed `terminalNeighborOfParent` selector
or selector evidence is supplied.  The later separation clause may then be
restricted to selected terminal-neighbor values.

This interface is deliberately not a selected-image cardinality theorem.  It
does not manufacture the code by `finsetCodeOfCardLe`, bounded menu
cardinality, empirical search, root-shell codes, local neighbor or displacement
codes, parent-relative `terminalNeighborCode` equality, deleted-vertex
adjacency outside the residual, or the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ bookkeepingTagCodeData :
        ∀ residual,
          PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
            residual,
        ∀ (terminalNeighborOfParent :
            ∀ residual,
              (p : {p : ConcretePlaquette physicalClayDimension L //
                p ∈ essential residual}) →
                {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
          (∀ residual,
            (p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual}) →
              PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
                residual p.1 (terminalNeighborOfParent residual p)) →
          ∀ residual
            (p q : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual}),
            (bookkeepingTagCodeData residual).bookkeepingTagCode
                (terminalNeighborOfParent residual p) =
              (bookkeepingTagCodeData residual).bookkeepingTagCode
                (terminalNeighborOfParent residual q) →
              (terminalNeighborOfParent residual p).1 =
                (terminalNeighborOfParent residual q).1

/-- A selector-admissible residual-value separation source supplies the
coordinate-first interface by direct repackaging after the caller fixes a
selector.

The proof only shows that each selected terminal-neighbor value is admissible
using the supplied selector evidence.  It does not create a code from a
selected image, bounded menu, `finsetCodeOfCardLe`, empirical search,
root-shell/local-neighbor/local-displacement code, parent-relative
`terminalNeighborCode`, deleted-vertex adjacency outside the residual, or the
v2.161 selector-image cycle. -/
theorem physicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296_of_residualFiberBookkeepingTagAdmissibleValueSeparation1296
    (hadmissible :
      PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296) :
    PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨bookkeepingTagCodeData, hseparates_admissible⟩ :=
    hadmissible root k deleted parentOf essential hchoice himage
      hessential_subset
  refine ⟨bookkeepingTagCodeData, ?_⟩
  intro terminalNeighborOfParent terminalNeighborSelectorEvidence residual p q hcode
  exact hseparates_admissible residual
    (terminalNeighborOfParent residual p)
    (terminalNeighborOfParent residual q)
    ⟨p, ⟨terminalNeighborSelectorEvidence residual p⟩⟩
    ⟨q, ⟨terminalNeighborSelectorEvidence residual q⟩⟩
    hcode

/-- Structural residual-value bookkeeping tag separation source.

This is the upstream separation interface isolated by v2.200.  For the v2.121
bookkeeping residual fibers, and for a fixed residual-local
`terminalNeighborOfParent` selector with selector evidence, it exposes
bookkeeping/base-zone tag code data on the whole residual subtype and proves
that equality of those residual-value tags separates the selected
terminal-neighbor values.

This interface is deliberately not a selected-image cardinality theorem.  It
does not manufacture the code by `finsetCodeOfCardLe`, bounded menu
cardinality, empirical search, root-shell codes, local neighbor or displacement
codes, parent-relative `terminalNeighborCode` equality, deleted-vertex
adjacency outside the residual, or the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
    (terminalNeighborOfParent :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
    (∀ residual,
      (p : {p : ConcretePlaquette physicalClayDimension L //
        p ∈ essential residual}) →
        PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
          residual p.1 (terminalNeighborOfParent residual p)) →
      ∃ bookkeepingTagCodeData :
        ∀ residual,
          PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
            residual,
        ∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          (bookkeepingTagCodeData residual).bookkeepingTagCode
              (terminalNeighborOfParent residual p) =
            (bookkeepingTagCodeData residual).bookkeepingTagCode
              (terminalNeighborOfParent residual q) →
            (terminalNeighborOfParent residual p).1 =
              (terminalNeighborOfParent residual q).1

/-- A coordinate-first bookkeeping/base-zone source supplies the value-separation
interface by direct repackaging after the caller fixes a selector.

This bridge does not create a code from selected-image cardinality, bounded
menu cardinality, `finsetCodeOfCardLe`, empirical search, root-shell codes,
local neighbor or displacement codes, parent-relative `terminalNeighborCode`
equality, deleted-vertex adjacency outside the residual, or the v2.161
selector-image cycle. -/
theorem physicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296_of_residualFiberBookkeepingTagCoordinate1296
    (hcoord :
      PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296) :
    PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
    terminalNeighborOfParent terminalNeighborSelectorEvidence
  letI : NeZero L := hL
  obtain ⟨bookkeepingTagCodeData, hseparates⟩ :=
    hcoord root k deleted parentOf essential hchoice himage hessential_subset
  exact ⟨bookkeepingTagCodeData,
    hseparates terminalNeighborOfParent terminalNeighborSelectorEvidence⟩

/-- Structural residual-value bookkeeping tag code source.

This is upstream of
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296`.  For
the v2.121 bookkeeping residual fibers, and for a fixed residual-local
`terminalNeighborOfParent` selector with selector evidence, it supplies
bookkeeping-tag code data on the whole residual subtype before restricting to
the selected terminal-neighbor values.

This interface does not obtain a code from selected-image cardinality, bounded
menu cardinality, `finsetCodeOfCardLe`, empirical search, local displacement
codes, parent-relative `terminalNeighborCode` equality, deleted-vertex
adjacency outside the residual, or the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
    (terminalNeighborOfParent :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) →
    (∀ residual,
      (p : {p : ConcretePlaquette physicalClayDimension L //
        p ∈ essential residual}) →
        PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
          residual p.1 (terminalNeighborOfParent residual p)) →
      ∃ bookkeepingTagCodeData :
        ∀ residual,
          PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
            residual,
        ∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          (bookkeepingTagCodeData residual).bookkeepingTagCode
              (terminalNeighborOfParent residual p) =
            (bookkeepingTagCodeData residual).bookkeepingTagCode
              (terminalNeighborOfParent residual q) →
            (terminalNeighborOfParent residual p).1 =
              (terminalNeighborOfParent residual q).1

/-- A residual-value bookkeeping tag separation source supplies the value-code
source interface by direct repackaging.

This bridge does not create a code from selected-image cardinality, bounded
menu cardinality, `finsetCodeOfCardLe`, empirical search, root-shell codes,
local neighbor or displacement codes, parent-relative `terminalNeighborCode`
equality, deleted-vertex adjacency outside the residual, or the v2.161
selector-image cycle. -/
theorem physicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296_of_residualFiberBookkeepingTagValueSeparation1296
    (hseparation :
      PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296) :
    PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296 := by
  exact hseparation

/-- A structural residual-value bookkeeping tag source supplies the compatible
tag-code-for-selector premise by projecting the residual-subtype code data.

This bridge is only repackaging.  It does not manufacture a code from
selected-image cardinality, bounded menu cardinality, `finsetCodeOfCardLe`,
empirical search, local displacement codes, parent-relative
`terminalNeighborCode` equality, deleted-vertex adjacency outside the residual,
or the v2.161 selector-image cycle. -/
theorem physicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296_of_residualFiberBookkeepingTagValueCodeSource1296
    (htagSource :
      PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296) :
    PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
    terminalNeighborOfParent terminalNeighborSelectorEvidence
  letI : NeZero L := hL
  obtain ⟨bookkeepingTagCodeData, htag_separates⟩ :=
    htagSource root k deleted parentOf essential hchoice himage
      hessential_subset terminalNeighborOfParent terminalNeighborSelectorEvidence
  refine ⟨fun residual =>
    (bookkeepingTagCodeData residual).bookkeepingTagCode, ?_⟩
  intro residual p q hcode
  exact htag_separates residual p q hcode

/-- Residual-fiber bookkeeping tag map interface.

This is the upstream v2.178 source contract for
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296`.
It exposes the residual-value `Fin 1296` tag map directly on the whole residual
subtype, before the selected terminal-neighbor image is considered.  The
selected-value separation clause is only a restriction of that residual tag map
to the terminal-neighbor values chosen by `terminalNeighborOfParent`.

This interface is not a selected-image cardinality theorem, does not use
`finsetCodeOfCardLe` on an already bounded selected image, is not a local
displacement code or parent-relative `terminalNeighborCode` equality, and does
not route through empirical search or the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborOfParent :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalNeighborSelectorEvidence :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
              residual p.1 (terminalNeighborOfParent residual p),
      ∃ bookkeepingTagCode :
        ∀ residual,
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
            Fin 1296,
        ∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          bookkeepingTagCode residual (terminalNeighborOfParent residual p) =
            bookkeepingTagCode residual (terminalNeighborOfParent residual q) →
            (terminalNeighborOfParent residual p).1 =
              (terminalNeighborOfParent residual q).1

/-- A terminal-neighbor selector source plus a compatible bookkeeping tag-code
source supplies the residual-fiber bookkeeping tag map interface.

The proof is only a two-premise packaging bridge.  It obtains the selector and
selector evidence from
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296`, then
applies `PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296`
to that exact selector.  It does not use selected-image cardinality,
`finsetCodeOfCardLe`, local displacement codes, parent-relative
`terminalNeighborCode` equality, empirical search, or the v2.161
selector-image cycle. -/
theorem physicalPlaquetteGraphResidualFiberBookkeepingTagMap1296_of_residualFiberTerminalNeighborSelectorSource1296_of_residualFiberBookkeepingTagCodeForSelector1296
    (hselector :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296)
    (htagForSelector :
      PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296) :
    PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence, _⟩ :=
    hselector root k deleted parentOf essential hchoice himage hessential_subset
  obtain ⟨bookkeepingTagCode, htag_separates⟩ :=
    htagForSelector root k deleted parentOf essential hchoice himage
      hessential_subset terminalNeighborOfParent terminalNeighborSelectorEvidence
  exact ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
    bookkeepingTagCode, htag_separates⟩

/-- Residual-fiber ambient bookkeeping-tag terminal-neighbor value-code interface.

This is the v2.175 source contract for
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296`.  It
has the same residual-local selector shape as the ambient interface, but the
absolute residual-value code is explicitly a bookkeeping-tag code rather than
an arbitrary ambient source.  The bridge below repacks this code with
`ambientOrigin = bookkeepingTag`.

The code is defined on `{q // q ∈ residual}` before terminal neighbors are
selected.  It is not a local displacement code, not parent-relative
`terminalNeighborCode` equality, not `finsetCodeOfCardLe` on an already bounded
selected image, not empirical search, and not the v2.161 cycle through
selector-image bounds. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborOfParent :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalNeighborSelectorEvidence :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
              residual p.1 (terminalNeighborOfParent residual p),
      ∃ bookkeepingTagCodeData :
        ∀ residual,
          PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
            residual,
        ∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          (bookkeepingTagCodeData residual).bookkeepingTagCode
              (terminalNeighborOfParent residual p) =
            (bookkeepingTagCodeData residual).bookkeepingTagCode
              (terminalNeighborOfParent residual q) →
            (terminalNeighborOfParent residual p).1 =
              (terminalNeighborOfParent residual q).1

/-- A residual-fiber bookkeeping tag map supplies the terminal-neighbor
bookkeeping-tag code interface by packaging the residual-subtype map as
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData`.

The proof is only a repacking bridge.  It does not derive a code from
selected-image cardinality, does not use `finsetCodeOfCardLe`, does not inspect
local displacement or parent-relative terminal-neighbor codes, and does not
route through the v2.161 selector-image cycle. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296_of_residualFiberBookkeepingTagMap1296
    (htag : PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
      bookkeepingTagCode, htag_separates⟩ :=
    htag root k deleted parentOf essential hchoice himage hessential_subset
  let bookkeepingTagCodeData :
      ∀ residual,
        PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCodeData
          residual :=
    fun residual =>
      { bookkeepingTagCode := bookkeepingTagCode residual }
  refine ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
    bookkeepingTagCodeData, ?_⟩
  intro residual p q hcode
  exact htag_separates residual p q hcode

/-- Residual-fiber ambient terminal-neighbor value-code interface.

This is the upstream v2.172 source contract for
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296`.
It carries the residual-local terminal-neighbor selector and selector evidence,
then supplies an ambient `Fin 1296` code on residual values themselves.

The code lives on `{q // q ∈ residual}` and is tagged by an ambient source:
base-zone enumeration, v2.121 bookkeeping tags, or canonical-last-edge/frontier
coordinates.  Thus the bridge below is a direct projection into the v2.170
absolute selected-value interface.  It is not a local displacement code, not
parent-relative `terminalNeighborCode` equality, not `finsetCodeOfCardLe` on an
already bounded selected image, not selected-image packing/projection, and not
the v2.161 circular chain through selector-image bounds. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborOfParent :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalNeighborSelectorEvidence :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
              residual p.1 (terminalNeighborOfParent residual p),
      ∃ ambientValueCodeData :
        ∀ residual,
          PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCodeData
            residual,
        ∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          (ambientValueCodeData residual).ambientValueCode
              (terminalNeighborOfParent residual p) =
            (ambientValueCodeData residual).ambientValueCode
              (terminalNeighborOfParent residual q) →
            (terminalNeighborOfParent residual p).1 =
              (terminalNeighborOfParent residual q).1

/-- A bookkeeping-tag residual-value code supplies the ambient value-code
interface by fixing the ambient origin to `bookkeepingTag`.

The proof only repacks the residual-subtype code into
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCodeData`.  It
does not derive a code from selected-image cardinality, does not use
`finsetCodeOfCardLe`, and does not route through the v2.161 selector-image
cycle. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296_of_residualFiberTerminalNeighborAmbientBookkeepingTagCode1296
    (hbookkeeping :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
      bookkeepingTagCodeData, hbookkeeping_separates⟩ :=
    hbookkeeping root k deleted parentOf essential hchoice himage hessential_subset
  let ambientValueCodeData :
      ∀ residual,
        PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCodeData
          residual :=
    fun residual =>
      { ambientOrigin :=
          PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientCodeOrigin.bookkeepingTag
        ambientValueCode :=
          (bookkeepingTagCodeData residual).bookkeepingTagCode }
  refine ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
    ambientValueCodeData, ?_⟩
  intro residual p q hcode
  exact hbookkeeping_separates residual p q hcode

/-- Residual-fiber absolute selected terminal-neighbor value-code interface.

This is the v2.168 source contract for
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296`.
It carries the residual-local terminal-neighbor selector and selector evidence,
then codes absolute residual terminal-neighbor values directly:

`{q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296`.

The separation clause is stated on essential parents, but the codes being
compared are the absolute residual values selected by those parents.  This is
not a parent-relative displacement code, not equality of the per-witness
`terminalNeighborCode` field, and not a code obtained by first bounding the
selected-image finset. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborOfParent :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalNeighborSelectorEvidence :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
              residual p.1 (terminalNeighborOfParent residual p),
      ∃ terminalNeighborAbsoluteValueCode :
        ∀ residual,
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
            Fin 1296,
        ∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          terminalNeighborAbsoluteValueCode residual
              (terminalNeighborOfParent residual p) =
            terminalNeighborAbsoluteValueCode residual
              (terminalNeighborOfParent residual q) →
            (terminalNeighborOfParent residual p).1 =
              (terminalNeighborOfParent residual q).1

/-- An ambient residual-value code supplies the v2.170 absolute selected-value
code by direct projection.

The proof only forgets the ambient-origin tag and reuses the residual-subtype
code on each selected terminal neighbor.  It does not construct a code from the
cardinality of the selected image, does not use `finsetCodeOfCardLe`, and does
not route through the v2.161 selector-image cycle. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296_of_residualFiberTerminalNeighborAmbientValueCode1296
    (hambient :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
      ambientValueCodeData, hambient_separates⟩ :=
    hambient root k deleted parentOf essential hchoice himage hessential_subset
  refine ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
    (fun residual q => (ambientValueCodeData residual).ambientValueCode q), ?_⟩
  intro residual p q hcode
  exact hambient_separates residual p q hcode

/-- Residual-fiber basepoint-independent terminal-neighbor value-code interface.

This is the v2.165 source contract for
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296`.
It carries the same residual-local terminal-neighbor selector data as the
geometric selector-code interface, but the `Fin 1296` code is attached to the
selected terminal-neighbor value itself, as an element of the selected-image
finset, not to a parent-relative displacement or a per-parent local neighbor
code.

The selected-image cardinality bound is deliberately not assumed here and the
code is not obtained from `finsetCodeOfCardLe` on an already bounded selected
image.  The bridge below evaluates this absolute selected-value code at each
parent's selected neighbor and uses injectivity to prove pairwise selected-value
separation. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborOfParent :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalNeighborSelectorEvidence :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
              residual p.1 (terminalNeighborOfParent residual p),
      ∃ terminalNeighborValueCode :
        ∀ residual,
          {q : ConcretePlaquette physicalClayDimension L //
            q ∈ (essential residual).attach.image
              (fun p => (terminalNeighborOfParent residual p).1)} →
            Fin 1296,
        ∀ residual, Function.Injective (terminalNeighborValueCode residual)

/-- An absolute residual-value code restricts to the selected-image code used by
the basepoint-independent interface.

The selected-image code is defined by choosing an essential parent witnessing
membership in the image and evaluating the absolute residual-value code on that
parent's selected terminal neighbor.  Injectivity on the selected-image subtype
follows from the absolute selected-value separation clause plus the image
witness equalities. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296_of_residualFiberTerminalNeighborAbsoluteSelectedValueCode1296
    (habsolute :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
      terminalNeighborAbsoluteValueCode, habsolute_separates⟩ :=
    habsolute root k deleted parentOf essential hchoice himage hessential_subset
  let imageParent :
      ∀ residual,
        {q : ConcretePlaquette physicalClayDimension L //
          q ∈ (essential residual).attach.image
            (fun p => (terminalNeighborOfParent residual p).1)} →
          {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual} :=
    fun residual q =>
      Classical.choose (Finset.mem_image.mp q.2)
  let terminalNeighborValueCode :
      ∀ residual,
        {q : ConcretePlaquette physicalClayDimension L //
          q ∈ (essential residual).attach.image
            (fun p => (terminalNeighborOfParent residual p).1)} →
          Fin 1296 :=
    fun residual q =>
      terminalNeighborAbsoluteValueCode residual
        (terminalNeighborOfParent residual (imageParent residual q))
  refine ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
    terminalNeighborValueCode, ?_⟩
  intro residual q r hcode
  have hq_image :
      (terminalNeighborOfParent residual (imageParent residual q)).1 = q.1 := by
    simpa [imageParent] using
      (Classical.choose_spec (Finset.mem_image.mp q.2)).2
  have hr_image :
      (terminalNeighborOfParent residual (imageParent residual r)).1 = r.1 := by
    simpa [imageParent] using
      (Classical.choose_spec (Finset.mem_image.mp r.2)).2
  have hcode' :
      terminalNeighborAbsoluteValueCode residual
          (terminalNeighborOfParent residual (imageParent residual q)) =
        terminalNeighborAbsoluteValueCode residual
          (terminalNeighborOfParent residual (imageParent residual r)) := by
    simpa [terminalNeighborValueCode] using hcode
  have hneighbor_eq :
      (terminalNeighborOfParent residual (imageParent residual q)).1 =
        (terminalNeighborOfParent residual (imageParent residual r)).1 :=
    habsolute_separates residual (imageParent residual q)
      (imageParent residual r) hcode'
  apply Subtype.ext
  calc
    q.1 = (terminalNeighborOfParent residual (imageParent residual q)).1 :=
      hq_image.symm
    _ = (terminalNeighborOfParent residual (imageParent residual r)).1 :=
      hneighbor_eq
    _ = r.1 := hr_image

/-- Residual-fiber geometric selector-code interface for terminal neighbors.

This is the non-circular v2.162 source contract for
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296`.
It asks for the residual-local `terminalNeighborOfParent` selector and its
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`, then exposes
an independent `Fin 1296` geometric code on essential parents.  Equal codes
must force equality of the selected terminal-neighbor values inside each
residual fiber.

The selected-image cardinality bound is deliberately not an input field here:
the bridge below derives it by coding the selected image through parent
witnesses and the pairwise selected-value separation theorem.  Thus this
interface does not use `finsetCodeOfCardLe` on an already bounded selected
image and does not cycle through selector-code separation, code separation,
dominating menus, image compression, local degree, residual paths, root-shell
reachability, residual size, raw frontier growth, deleted-vertex adjacency,
empirical search, or post-hoc current deletion witnesses. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborOfParent :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalNeighborSelectorEvidence :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
              residual p.1 (terminalNeighborOfParent residual p),
      ∃ terminalNeighborGeometricCode :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) → Fin 1296,
        ∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          terminalNeighborGeometricCode residual p =
              terminalNeighborGeometricCode residual q →
            (terminalNeighborOfParent residual p).1 =
              (terminalNeighborOfParent residual q).1

/-- An absolute selected-value code gives the parent-indexed geometric selector
code.

The geometric code of an essential parent is the basepoint-independent code of
the selected terminal-neighbor value itself.  Pairwise selected-value separation
then follows from injectivity on the selected image. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296_of_residualFiberTerminalNeighborBasepointIndependentCode1296
    (hbase :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
      terminalNeighborValueCode, hvalueCode_injective⟩ :=
    hbase root k deleted parentOf essential hchoice himage hessential_subset
  let selectedValue :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}) →
          {q : ConcretePlaquette physicalClayDimension L //
            q ∈ (essential residual).attach.image
              (fun p => (terminalNeighborOfParent residual p).1)} :=
    fun residual p =>
      ⟨(terminalNeighborOfParent residual p).1, by
        exact Finset.mem_image.mpr ⟨p, by simp, rfl⟩⟩
  refine ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
    (fun residual p => terminalNeighborValueCode residual (selectedValue residual p)), ?_⟩
  intro residual p q hcode
  exact congrArg
    (fun x :
      {q : ConcretePlaquette physicalClayDimension L //
        q ∈ (essential residual).attach.image
          (fun p => (terminalNeighborOfParent residual p).1)} => x.1)
    (hvalueCode_injective residual hcode)

/-- A residual-local geometric selector code gives the selected terminal-neighbor
image bound.

The proof builds a code on each selected-image element by choosing an essential
parent witnessing membership in the image and then applying the geometric code
of that parent.  Injectivity follows from the pairwise selected-value separation
field of
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296`.
It does not use `finsetCodeOfCardLe` on the selected image and does not route
through selector-code separation, code separation, dominating menus, or image
compression. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296_of_residualFiberTerminalNeighborGeometricSelectorCode1296
    (hgeometric :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
      terminalNeighborGeometricCode, hcode_separates⟩ :=
    hgeometric root k deleted parentOf essential hchoice himage hessential_subset
  refine ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence, ?_⟩
  intro residual
  let selectedImage : Finset (ConcretePlaquette physicalClayDimension L) :=
    (essential residual).attach.image
      (fun p => (terminalNeighborOfParent residual p).1)
  let selectedImageCode :
      {q : ConcretePlaquette physicalClayDimension L // q ∈ selectedImage} →
        Fin 1296 :=
    fun q =>
      terminalNeighborGeometricCode residual
        (Classical.choose (Finset.mem_image.mp q.2))
  have hselectedImageCode_injective : Function.Injective selectedImageCode := by
    intro a b hcode
    let pa := Classical.choose (Finset.mem_image.mp a.2)
    let pb := Classical.choose (Finset.mem_image.mp b.2)
    have hpa :
        (terminalNeighborOfParent residual pa).1 = a.1 :=
      (Classical.choose_spec (Finset.mem_image.mp a.2)).2
    have hpb :
        (terminalNeighborOfParent residual pb).1 = b.1 :=
      (Classical.choose_spec (Finset.mem_image.mp b.2)).2
    have hsame :
        (terminalNeighborOfParent residual pa).1 =
          (terminalNeighborOfParent residual pb).1 := by
      exact hcode_separates residual pa pb hcode
    apply Subtype.ext
    exact hpa.symm.trans (hsame.trans hpb)
  have hcard :
      Fintype.card
        {q : ConcretePlaquette physicalClayDimension L // q ∈ selectedImage} ≤
          1296 := by
    simpa using
      Fintype.card_le_of_injective selectedImageCode hselectedImageCode_injective
  rw [← Fintype.card_of_subtype selectedImage (fun _ => Iff.rfl)]
  exact hcard

/-- Residual-fiber terminal-neighbor image-compression interface.

This is the v2.150 bounded-menu predecessor to
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296`.
It does not ask for the selected-image cardinality directly.  Instead, it
requires a residual-only `terminalNeighborMenu` with cardinality `<= 1296`, a
selector whose values lie in that menu, residual-local selector evidence, and
an image-cover clause showing that the selected terminal-neighbor image is
contained in the bounded menu.

This separates image compression from local neighbor existence, residual path
existence/splitting, root/root-shell reachability, local degree of one fixed
plaquette, residual size, raw frontier growth, deleted-vertex adjacency outside
the residual, empirical search, and packing of an already bounded menu. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborMenu :
        Finset (ConcretePlaquette physicalClayDimension L) →
          Finset (ConcretePlaquette physicalClayDimension L),
      (∀ residual, terminalNeighborMenu residual ⊆ residual) ∧
      (∀ residual, (terminalNeighborMenu residual).card ≤ 1296) ∧
      ∃ terminalNeighborOfParent :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalNeighborSelectorEvidence :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
              residual p.1 (terminalNeighborOfParent residual p),
        (∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            (terminalNeighborOfParent residual p).1 ∈
              terminalNeighborMenu residual) ∧
        ∀ residual,
          ((essential residual).attach.image
            (fun p =>
              (terminalNeighborOfParent residual p).1)) ⊆
                terminalNeighborMenu residual

/-- Residual-fiber terminal-neighbor dominating-menu interface.

This is the v2.153 menu-first predecessor to
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296`.
It asks for a residual-local bounded menu and a domination relation: every
essential parent is dominated by some terminal neighbor in that menu carrying
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`.

The selector used by the image-compression interface is derived only in the
bridge from this domination relation.  The bounded-menu construction is kept
separate from selector image compression, local degree, residual path
existence/splitting, root/root-shell reachability, residual size, raw frontier
growth, deleted-vertex adjacency outside the residual, empirical search, and
packing/projection of an already bounded menu. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborMenu :
        Finset (ConcretePlaquette physicalClayDimension L) →
          Finset (ConcretePlaquette physicalClayDimension L),
      ∃ hmenu_subset : ∀ residual, terminalNeighborMenu residual ⊆ residual,
      (∀ residual, (terminalNeighborMenu residual).card ≤ 1296) ∧
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          ∃ q : {q : ConcretePlaquette physicalClayDimension L //
            q ∈ terminalNeighborMenu residual},
            Nonempty
              (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
                residual p.1 ⟨q.1, hmenu_subset residual q.2⟩)

/-- Non-singleton residual-member neighbor source.

This interface isolates only the residual final-edge neighbor existence needed
upstream of the walk-split theorem
`PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296`.
For each v2.121 bookkeeping residual fiber and essential residual parent, it
asks that a non-singleton residual contain some residual vertex adjacent to the
parent.

It deliberately does not claim full
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`: there are no
source/target subtypes, induced residual walks, terminal-neighbor suffixes, menu
cardinality, selected-image cardinality, `finsetCodeOfCardLe`, empirical search,
or v2.161 selector-image cycle here.  In particular the deleted vertex of a
current witness is not used as a residual terminal neighbor for
`residual = X.erase (deleted X)`. -/
def PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset
                (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∀ residual,
        residual ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root (k - 1) →
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          residual.card ≠ 1 →
            ∃ q : {q : ConcretePlaquette physicalClayDimension L //
              q ∈ residual},
              p.1 ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset q.1

/-- The non-singleton residual-member neighbor interface follows from induced
preconnectedness of each anchored residual fiber.

The proof is strictly local to the residual: essential parents are first
included into the residual via the `essential ⊆ residual` hypothesis, and the
generic member-neighbor lemma extracts an adjacent residual vertex from a
nontrivial induced walk.  It does not construct selector-data source fields,
walk-split data, menus, selected-image bounds, or any code from bounded
cardinality. -/
theorem physicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296 :
    PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296 := by
  intro L hL root k deleted parentOf essential _hchoice _himage hessential_subset
    residual hresidual p hcard
  letI : NeZero L := hL
  have hp_residual : p.1 ∈ residual := hessential_subset residual p.2
  obtain ⟨q, hq_residual, hq_neighbor⟩ :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_nonSingleton_member_has_neighbor
      (d := physicalClayDimension) (L := L) (k := k - 1) (root := root)
      (p := p.1) (X := residual) hresidual hp_residual hcard
  exact ⟨⟨q, hq_residual⟩, hq_neighbor⟩

/-- Residual induced walk-split interface below the full terminal-neighbor
selector-data source.

This interface is deliberately stronger than residual-neighbor existence
alone.  It accepts
`PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296`
as the only permitted source for non-singleton final-edge adjacency, but it
still requires the full induced residual walk-split payload for each essential
parent: source and target residual subtypes, a residual terminal neighbor, a
terminal-neighbor code, induced walks `source -> target`,
`source -> terminalNeighbor`, and `terminalNeighbor -> target`, plus the
non-singleton final-edge adjacency.

Thus the bridge to
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296`
below is only structural repackaging.  This interface does not use deleted
vertices outside the residual, selected-image cardinality, bounded menus,
`finsetCodeOfCardLe`, empirical search, or the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296 :
    Prop :=
  PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296 →
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset
                (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          ∃ source : {s : ConcretePlaquette physicalClayDimension L //
            s ∈ residual},
          ∃ target : {r : ConcretePlaquette physicalClayDimension L //
            r ∈ residual},
          ∃ terminalNeighbor :
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
          ∃ terminalNeighborCode : Fin 1296,
            target.1 = p.1 ∧
            Nonempty
              (((plaquetteGraph physicalClayDimension L).induce
                {x | x ∈ residual}).Walk source target) ∧
            Nonempty
              (((plaquetteGraph physicalClayDimension L).induce
                {x | x ∈ residual}).Walk source terminalNeighbor) ∧
            Nonempty
              (((plaquetteGraph physicalClayDimension L).induce
                {x | x ∈ residual}).Walk terminalNeighbor target) ∧
            (residual.card ≠ 1 →
              p.1 ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset
                  terminalNeighbor.1)

/-- The non-singleton residual-member neighbor theorem supplies the final edge
of the induced residual walk split.

The construction keeps the source equal to the target essential parent.  In the
singleton case the final-edge clause is vacuous and all induced walks are nil.
In the non-singleton case the neighbor-only theorem supplies a residual
terminal neighbor `q`; the two one-edge induced walks are built from the
ambient adjacency `q -- p`, while the source-to-target walk remains nil.

No deleted vertex from a current witness is used as a residual terminal
neighbor, and no selected-image cardinality, bounded menu, empirical search,
`finsetCodeOfCardLe`, or v2.161 selector-image cycle appears in the proof. -/
theorem physicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296 :
    PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296 := by
  intro hneighbor L hL root k deleted parentOf essential hchoice himage
    hessential_subset residual p
  letI : NeZero L := hL
  have hp_residual : p.1 ∈ residual := hessential_subset residual p.2
  let source : {s : ConcretePlaquette physicalClayDimension L // s ∈ residual} :=
    ⟨p.1, hp_residual⟩
  let target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual} :=
    source
  by_cases hcard : residual.card = 1
  · refine ⟨source, target, target, 0, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.nil⟩
    · intro hnon
      exact False.elim (hnon hcard)
  · have hp_image :
        p.1 ∈
          ((plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root k).filter
              (fun X => X.erase (deleted X) = residual)).image parentOf := by
      simpa [himage residual] using p.2
    obtain ⟨X, hXfilter, hparent⟩ := Finset.mem_image.mp hp_image
    have hX :
        X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k :=
      (Finset.mem_filter.mp hXfilter).1
    have herase : X.erase (deleted X) = residual :=
      (Finset.mem_filter.mp hXfilter).2
    have hres_card_pos : 0 < residual.card :=
      Finset.card_pos.mpr ⟨p.1, hp_residual⟩
    have hres_card_ge_two : 2 ≤ residual.card := by
      omega
    have hres_le_X : residual.card ≤ X.card := by
      rw [← herase]
      exact Finset.card_le_card (Finset.erase_subset _ _)
    have hXcard : X.card = k :=
      plaquetteGraphPreconnectedSubsetsAnchoredCard_card_eq hX
    have hk : 2 ≤ k := by
      omega
    have hchoiceX := hchoice hk hX
    have hresidual_anchored :
        residual ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root (k - 1) := by
      simpa [herase] using hchoiceX.2.2.1
    obtain ⟨terminalNeighbor, hterminal_adj⟩ :=
      hneighbor root k deleted parentOf essential hchoice himage hessential_subset
        residual hresidual_anchored p hcard
    have hAdj_qp :
        (plaquetteGraph physicalClayDimension L).Adj terminalNeighbor.1 target.1 := by
      simpa [target, source] using
        (SimpleGraph.mem_neighborFinset
          (plaquetteGraph physicalClayDimension L) terminalNeighbor.1 p.1).mp
          hterminal_adj
    have hAdj_source_q :
        ((plaquetteGraph physicalClayDimension L).induce
          {x | x ∈ residual}).Adj source terminalNeighbor := by
      exact SimpleGraph.induce_adj.mpr hAdj_qp.symm
    have hAdj_q_target :
        ((plaquetteGraph physicalClayDimension L).induce
          {x | x ∈ residual}).Adj terminalNeighbor target := by
      exact SimpleGraph.induce_adj.mpr hAdj_qp
    refine ⟨source, target, terminalNeighbor, 0, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons hAdj_source_q SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons hAdj_q_target SimpleGraph.Walk.nil⟩
    · intro _hnon
      exact hterminal_adj

/-- Structural source data for residual terminal-neighbor selector evidence.

This is the full selector-data source isolated by the v2.185 proof attempt.  It
is deliberately stronger than residual-neighbor existence alone: for every
essential parent it exposes the residual source, target, selected terminal
neighbor, the three induced residual walks used by
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`, the
non-singleton final-edge adjacency, and the terminal-neighbor code.

It is still cardinality-free: there is no menu, selected-image bound,
`finsetCodeOfCardLe`, empirical search, or v2.161 selector-image cycle here. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          ∃ source : {s : ConcretePlaquette physicalClayDimension L //
            s ∈ residual},
          ∃ target : {r : ConcretePlaquette physicalClayDimension L //
            r ∈ residual},
          ∃ terminalNeighbor :
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
          ∃ terminalNeighborCode : Fin 1296,
            target.1 = p.1 ∧
            Nonempty
              (((plaquetteGraph physicalClayDimension L).induce
                {x | x ∈ residual}).Walk source target) ∧
            Nonempty
              (((plaquetteGraph physicalClayDimension L).induce
                {x | x ∈ residual}).Walk source terminalNeighbor) ∧
            Nonempty
              (((plaquetteGraph physicalClayDimension L).induce
                {x | x ∈ residual}).Walk terminalNeighbor target) ∧
            (residual.card ≠ 1 →
              p.1 ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset
                  terminalNeighbor.1)

/-- The walk-split interface supplies the full selector-data source by passing
the already proved residual-member neighbor theorem as its non-singleton
final-edge source and then forgetting that source label.

This bridge does not construct selector data from residual-neighbor existence
alone: all source/target subtypes, induced walks, terminal neighbor, and code
come from
`PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296`. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296_of_residualFiberNonSingletonMemberNeighborWalkSplit1296
    (hsplit :
      PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296 := by
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
    residual p
  letI : NeZero L := hL
  exact hsplit
    physicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296
    root k deleted parentOf essential hchoice himage hessential_subset
    residual p

/-- The v2.192 walk-split proof closes the residual terminal-neighbor
selector-data source by direct bridge application.

This proof deliberately does not reconstruct selector data from residual-neighbor
existence alone.  The full source/target subtype payload, induced residual
walks, residual terminal neighbor, and code come through
`physicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296`
and the bridge above. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296 :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296 :=
  physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296_of_residualFiberNonSingletonMemberNeighborWalkSplit1296
    physicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296

/-- Residual-fiber terminal-neighbor domination relation without a bounded menu.

This is the v2.184 selector-source predecessor isolated from the v2.154
dominating-menu interface.  It asks only for the residual-local domination
relation needed to choose a terminal neighbor for every essential parent:
for each bookkeeping residual fiber and essential parent, there exists a
residual terminal-neighbor candidate carrying
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`.

It deliberately does not ask for a `terminalNeighborMenu`, a menu-cardinality
bound, selected-image cardinality, `finsetCodeOfCardLe`, local displacement
codes, parent-relative `terminalNeighborCode` equality, empirical search, or
the v2.161 selector-image cycle. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          ∃ q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
            Nonempty
              (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
                residual p.1 q)

/-- A full residual terminal-neighbor selector-data source supplies the
menu-free domination relation by packaging the exposed source/target/walk data
as `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`.

The proof is a structural repackaging bridge only.  It does not derive
selector data from residual-neighbor existence alone and does not use bounded
menus, selected-image cardinality, `finsetCodeOfCardLe`, empirical search, or
the v2.161 selector-image cycle. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296_of_residualFiberTerminalNeighborSelectorDataSource1296
    (hsource :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  intro residual p
  obtain ⟨source, target, terminalNeighbor, terminalNeighborCode,
    htarget, hcanonicalWalk, hprefix, hsuffix, hlast⟩ :=
    hsource root k deleted parentOf essential hchoice himage
      hessential_subset residual p
  refine ⟨terminalNeighbor, ?_⟩
  exact
    ⟨{
      target := target
      target_eq := htarget
      source := source
      canonicalWalk := Classical.choice hcanonicalWalk
      prefixToTerminalNeighbor := Classical.choice hprefix
      terminalNeighborSuffix := Classical.choice hsuffix
      terminalNeighbor_is_last_edge := hlast
      terminalNeighborCode := terminalNeighborCode
    }⟩

/-- The proved selector-data source closes the residual terminal-neighbor
domination relation by direct bridge application.

This proof deliberately keeps the domination construction behind the existing
selector-data-source bridge.  It does not rebuild domination witnesses from
residual-neighbor existence alone, bounded menus, selected-image cardinality,
`finsetCodeOfCardLe`, empirical search, or the v2.161 selector-image cycle. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296 :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296 :=
  physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296_of_residualFiberTerminalNeighborSelectorDataSource1296
    physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296

/-- A residual terminal-neighbor domination relation supplies the selector-source
interface by choosing the dominated terminal neighbor for each essential parent.

This bridge is the menu-free version of the v2.183 reduction.  It does not use
menu cardinality, selected-image cardinality, `finsetCodeOfCardLe`, residual
paths alone, root-shell reachability, local degree, deleted-vertex adjacency,
local displacement codes, parent-relative `terminalNeighborCode` equality,
empirical search, or the v2.161 selector-image cycle. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominationRelation1296
    (hdomination :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  let terminalNeighborOfParent :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} :=
    fun residual p =>
      Classical.choose
        (hdomination root k deleted parentOf essential hchoice himage
          hessential_subset residual p)
  let terminalNeighborSelectorEvidence :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 (terminalNeighborOfParent residual p) :=
    fun residual p => by
      simpa [terminalNeighborOfParent] using
        (Classical.choice
          (Classical.choose_spec
            (hdomination root k deleted parentOf essential hchoice himage
              hessential_subset residual p)))
  exact ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence, trivial⟩

/-- The proved residual terminal-neighbor domination relation closes the
selector-source interface by direct bridge application.

This proof deliberately keeps all selector-source construction inside the
existing domination-relation bridge.  It does not use bounded menus,
selected-image cardinality, `finsetCodeOfCardLe`, empirical search, deleted
vertices outside the residual, or the v2.161 selector-image cycle. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296 :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296 :=
  physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominationRelation1296
    physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296

/-- A residual terminal-neighbor dominating menu supplies the selector-source
interface by choosing the dominated terminal neighbor for each essential parent.

The proof only projects the domination relation to a residual-local
`terminalNeighborOfParent` and its
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`.  It ignores
the menu cardinality field and does not derive anything from selected-image
cardinality, `finsetCodeOfCardLe`, local displacement codes, parent-relative
`terminalNeighborCode` equality, empirical search, or the v2.161
selector-image cycle. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominatingMenu1296
    (hdominating :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborMenu, hmenu_subset, _hmenu_card, hdominating_menu⟩ :=
    hdominating root k deleted parentOf essential hchoice himage hessential_subset
  let terminalNeighborOfParent :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} :=
    fun residual p =>
      ⟨(Classical.choose (hdominating_menu residual p)).1,
        hmenu_subset residual (Classical.choose (hdominating_menu residual p)).2⟩
  let terminalNeighborSelectorEvidence :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 (terminalNeighborOfParent residual p) :=
    fun residual p => by
      simpa [terminalNeighborOfParent] using
        (Classical.choice (Classical.choose_spec (hdominating_menu residual p)))
  exact ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence, trivial⟩

/-- Residual-fiber terminal-neighbor selected-image code-separation interface.

This is the v2.159 selector-code predecessor to
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296`.  It
does not merely record a per-witness `terminalNeighborCode`.  Instead, it
constructs a residual-local selector and proves that equal selector codes force
equal selected terminal-neighbor values across essential parents in the same
residual fiber.  The selected-image cardinality bound is kept explicit so the
projection bridge is Lean-stable and does not smuggle in a separate cardinality
argument.

This is not a local-degree, residual-path, root-shell, residual-size,
raw-frontier, deleted-vertex adjacency, empirical-search, or packing/projection
statement. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborOfParent :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalNeighborSelectorEvidence :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
              residual p.1 (terminalNeighborOfParent residual p),
        (∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          (terminalNeighborSelectorEvidence residual p).terminalNeighborCode =
              (terminalNeighborSelectorEvidence residual q).terminalNeighborCode →
            (terminalNeighborOfParent residual p).1 =
              (terminalNeighborOfParent residual q).1) ∧
        ∀ residual,
          ((essential residual).attach.image
            (fun p =>
              (terminalNeighborOfParent residual p).1)).card ≤ 1296

/-- Residual-fiber terminal-neighbor selected-image code-separation interface.

This is the v2.156 selected-image predecessor to
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296`.  It
constructs a residual-local terminal-neighbor selector and residual-local
selector evidence, then exposes a genuine injective `Fin 1296` code on the
selected terminal-neighbor image.  The dominating menu can therefore be the
selected image itself.

This is deliberately not a local-degree, residual-path, root-shell, residual
size, raw-frontier, deleted-vertex adjacency, empirical-search, or
packing/projection statement: those ingredients do not separate the selected
terminal-neighbor image across all essential parents in a residual fiber. -/
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborOfParent :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalNeighborSelectorEvidence :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
              residual p.1 (terminalNeighborOfParent residual p),
      ∃ terminalNeighborImageCode :
        ∀ residual,
          {q : ConcretePlaquette physicalClayDimension L //
            q ∈
              ((essential residual).attach.image
                (fun p => (terminalNeighborOfParent residual p).1))} →
            Fin 1296,
        (∀ residual, Function.Injective (terminalNeighborImageCode residual)) ∧
        ∀ residual,
          ((essential residual).attach.image
            (fun p =>
              (terminalNeighborOfParent residual p).1)).card ≤ 1296

/-- Residual-fiber canonical terminal-neighbor selected-image interface.

This is the v2.144 structural predecessor to
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296`.  It
names the selected terminal neighbor before terminal-suffix repacking and keeps
the selected terminal-neighbor image-cardinality bound `<= 1296` explicit over
each residual fiber.

It is not a proof from residual path existence or path splitting alone, not
root/root-shell reachability, not a local-degree or residual-size bound, not a
raw frontier bound, and not packing an already bounded menu.  It does not use
deleted-vertex adjacency outside the residual as terminal-predecessor data. -/
def PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalNeighborData :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborData
              residual p.1,
        ∀ residual,
          ((essential residual).attach.image
            (fun p =>
              (terminalNeighborData residual p).terminalNeighbor.1)).card ≤ 1296

/-- Selector terminal-neighbor data projects into the v2.145 canonical
terminal-neighbor interface.

The proof is projection-only: it copies the explicit
`terminalNeighborOfParent` selector into
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborData` and carries
the selected-image bound unchanged.  It does not construct the selector, does
not use deleted-vertex adjacency outside the residual, and does not replace the
selected-image bound with path existence, root/root-shell reachability, local
degree, residual size, raw frontier growth, or packing of an already bounded
menu. -/
theorem physicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296_of_residualFiberTerminalNeighborSelectorImageBound1296
    (hselector :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296) :
    PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence, hcard⟩ :=
    hselector root k deleted parentOf essential hchoice himage hessential_subset
  let terminalNeighborData :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborData
            residual p.1 :=
    fun residual p =>
      { target := (terminalNeighborSelectorEvidence residual p).target
        target_eq := (terminalNeighborSelectorEvidence residual p).target_eq
        source := (terminalNeighborSelectorEvidence residual p).source
        canonicalWalk :=
          (terminalNeighborSelectorEvidence residual p).canonicalWalk
        terminalNeighbor := terminalNeighborOfParent residual p
        prefixToTerminalNeighbor :=
          (terminalNeighborSelectorEvidence residual p).prefixToTerminalNeighbor
        terminalNeighborSuffix :=
          (terminalNeighborSelectorEvidence residual p).terminalNeighborSuffix
        terminalNeighbor_is_last_edge :=
          (terminalNeighborSelectorEvidence residual p).terminalNeighbor_is_last_edge
        terminalNeighborCode :=
          (terminalNeighborSelectorEvidence residual p).terminalNeighborCode }
  refine ⟨terminalNeighborData, ?_⟩
  intro residual
  simpa [terminalNeighborData] using hcard residual

/-- Selected terminal-neighbor code separation supplies the dominating menu.

The menu is the selected terminal-neighbor image itself.  The cardinality bound
comes from the code-separation interface, while domination is obtained from the
residual-local selector evidence.  This does not choose terminal neighbors
post-hoc from a current `(X, deleted X)` witness and does not replace selected
image separation by local degree, paths, root-shell reachability, residual
size, raw frontier, deleted-vertex adjacency, empirical search, or packing. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296_of_residualFiberTerminalNeighborCodeSeparation1296
    (hseparation :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
      _terminalNeighborImageCode, _hcode_injective, hcard⟩ :=
    hseparation root k deleted parentOf essential hchoice himage hessential_subset
  let terminalNeighborMenu :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L) :=
    fun residual =>
      (essential residual).attach.image
        (fun p => (terminalNeighborOfParent residual p).1)
  have hmenu_subset : ∀ residual, terminalNeighborMenu residual ⊆ residual := by
    intro residual q hq
    rcases Finset.mem_image.mp hq with ⟨p, _hp, rfl⟩
    exact (terminalNeighborOfParent residual p).2
  refine ⟨terminalNeighborMenu, hmenu_subset, ?_, ?_⟩
  · intro residual
    simpa [terminalNeighborMenu] using hcard residual
  · intro residual p
    have hq_mem : (terminalNeighborOfParent residual p).1 ∈
        terminalNeighborMenu residual := by
      refine Finset.mem_image.mpr ?_
      exact ⟨p, by simp, rfl⟩
    let qMenu : {q : ConcretePlaquette physicalClayDimension L //
        q ∈ terminalNeighborMenu residual} :=
      ⟨(terminalNeighborOfParent residual p).1, hq_mem⟩
    refine ⟨qMenu, ?_⟩
    exact ⟨by
      simpa [qMenu, terminalNeighborMenu, hmenu_subset] using
        terminalNeighborSelectorEvidence residual p⟩

/-- Selector-code separation projects to a selected-image code.

The image code is defined by choosing a parent witness for each selected image
element and reading the witness's `terminalNeighborCode`.  Injectivity follows
from the pairwise selector-code separation clause; the selected-image
cardinality bound is carried by the selector-code interface.  This bridge does
not use local degree, residual paths, root-shell reachability, residual size,
raw frontier growth, deleted-vertex adjacency, empirical search, or post-hoc
current deletion witnesses. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296_of_residualFiberTerminalNeighborSelectorCodeSeparation1296
    (hselectorCode :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
      hselector_code_separates, hcard⟩ :=
    hselectorCode root k deleted parentOf essential hchoice himage hessential_subset
  let selectedImage :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L) :=
    fun residual =>
      (essential residual).attach.image
        (fun p => (terminalNeighborOfParent residual p).1)
  let imageParent :
      ∀ residual,
        {q : ConcretePlaquette physicalClayDimension L //
          q ∈ selectedImage residual} →
          {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual} :=
    fun residual q =>
      Classical.choose (Finset.mem_image.mp q.2)
  let terminalNeighborImageCode :
      ∀ residual,
        {q : ConcretePlaquette physicalClayDimension L //
          q ∈ selectedImage residual} →
          Fin 1296 :=
    fun residual q =>
      (terminalNeighborSelectorEvidence residual
        (imageParent residual q)).terminalNeighborCode
  refine ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence,
    terminalNeighborImageCode, ?_, ?_⟩
  · intro residual q r hcode
    have hq_image :
        (terminalNeighborOfParent residual (imageParent residual q)).1 = q.1 := by
      simpa [selectedImage, imageParent] using
        (Classical.choose_spec (Finset.mem_image.mp q.2)).2
    have hr_image :
        (terminalNeighborOfParent residual (imageParent residual r)).1 = r.1 := by
      simpa [selectedImage, imageParent] using
        (Classical.choose_spec (Finset.mem_image.mp r.2)).2
    have hcode' :
        (terminalNeighborSelectorEvidence residual
            (imageParent residual q)).terminalNeighborCode =
          (terminalNeighborSelectorEvidence residual
            (imageParent residual r)).terminalNeighborCode := by
      simpa [terminalNeighborImageCode] using hcode
    have hneighbor_eq :=
      hselector_code_separates residual (imageParent residual q)
        (imageParent residual r) hcode'
    apply Subtype.ext
    calc
      q.1 = (terminalNeighborOfParent residual (imageParent residual q)).1 :=
        hq_image.symm
      _ = (terminalNeighborOfParent residual (imageParent residual r)).1 :=
        hneighbor_eq
      _ = r.1 := hr_image
  · intro residual
    simpa [selectedImage] using hcard residual

/-- A selected-image bound canonically supplies selector-code separation.

This bridge does not prove the selected-image bound.  It reuses the selector
and residual-local terminal-neighbor evidence from
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296`,
then replaces only the per-witness `terminalNeighborCode` field by the
canonical `finsetCodeOfCardLe` code on the already bounded selected image.
Thus equal codes separate selected terminal-neighbor values by
`finsetCodeOfCardLe_injective`. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296_of_residualFiberTerminalNeighborSelectorImageBound1296
    (hselector :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence, hcard⟩ :=
    hselector root k deleted parentOf essential hchoice himage hessential_subset
  let selectedImage :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L) :=
    fun residual =>
      (essential residual).attach.image
        (fun p => (terminalNeighborOfParent residual p).1)
  have hselected_mem :
      ∀ residual
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}),
        (terminalNeighborOfParent residual p).1 ∈ selectedImage residual := by
    intro residual p
    refine Finset.mem_image.mpr ?_
    exact ⟨p, by simp, rfl⟩
  let terminalNeighborSelectorEvidenceWithCode :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 (terminalNeighborOfParent residual p) :=
    fun residual p =>
      { target := (terminalNeighborSelectorEvidence residual p).target
        target_eq := (terminalNeighborSelectorEvidence residual p).target_eq
        source := (terminalNeighborSelectorEvidence residual p).source
        canonicalWalk :=
          (terminalNeighborSelectorEvidence residual p).canonicalWalk
        prefixToTerminalNeighbor :=
          (terminalNeighborSelectorEvidence residual p).prefixToTerminalNeighbor
        terminalNeighborSuffix :=
          (terminalNeighborSelectorEvidence residual p).terminalNeighborSuffix
        terminalNeighbor_is_last_edge :=
          (terminalNeighborSelectorEvidence residual p).terminalNeighbor_is_last_edge
        terminalNeighborCode :=
          finsetCodeOfCardLe (selectedImage residual)
            (by simpa [selectedImage] using hcard residual)
            ⟨(terminalNeighborOfParent residual p).1, hselected_mem residual p⟩ }
  refine ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidenceWithCode,
    ?_, ?_⟩
  · intro residual p q hcode
    have hsub :
        (⟨(terminalNeighborOfParent residual p).1, hselected_mem residual p⟩ :
          {x : ConcretePlaquette physicalClayDimension L //
            x ∈ selectedImage residual}) =
        (⟨(terminalNeighborOfParent residual q).1, hselected_mem residual q⟩ :
          {x : ConcretePlaquette physicalClayDimension L //
            x ∈ selectedImage residual}) := by
      exact finsetCodeOfCardLe_injective (selectedImage residual)
        (by simpa [selectedImage] using hcard residual) hcode
    exact congrArg
      (fun z : {x : ConcretePlaquette physicalClayDimension L //
        x ∈ selectedImage residual} => z.1) hsub
  · intro residual
    simpa [selectedImage] using hcard residual

/-- A residual terminal-neighbor dominating menu projects to image compression.

The proof is structural: the selector is chosen from the supplied domination
relation, and the selected image is covered by the bounded menu because every
chosen terminal neighbor is a member of that menu.  It does not construct the
menu from local degree, residual paths, root-shell reachability, residual size,
raw frontier growth, deleted-vertex adjacency, empirical search, or packing. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296_of_residualFiberTerminalNeighborDominatingMenu1296
    (hdominating :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborMenu, hmenu_subset, hmenu_card, hdominating_menu⟩ :=
    hdominating root k deleted parentOf essential hchoice himage hessential_subset
  let terminalNeighborOfParent :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} :=
    fun residual p =>
      ⟨(Classical.choose (hdominating_menu residual p)).1,
        hmenu_subset residual (Classical.choose (hdominating_menu residual p)).2⟩
  let terminalNeighborSelectorEvidence :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
            residual p.1 (terminalNeighborOfParent residual p) :=
    fun residual p => by
      simpa [terminalNeighborOfParent] using
        (Classical.choice (Classical.choose_spec (hdominating_menu residual p)))
  refine ⟨terminalNeighborMenu, hmenu_subset, hmenu_card,
    terminalNeighborOfParent, terminalNeighborSelectorEvidence, ?_, ?_⟩
  · intro residual p
    simpa [terminalNeighborOfParent] using
      (Classical.choose (hdominating_menu residual p)).2
  · intro residual x hx
    rcases Finset.mem_image.mp hx with ⟨p, _hp, rfl⟩
    simpa [terminalNeighborOfParent] using
      (Classical.choose (hdominating_menu residual p)).2

/-- A bounded residual terminal-neighbor menu projects to the selected-image
interface.

The proof is purely structural: it reuses the selector and residual-local
evidence supplied by
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296`, then
derives the selected-image cardinality bound from `selected image ⊆ menu` and
`menu.card <= 1296`.  It does not construct the menu from path existence,
root/root-shell data, local degree, residual size, raw frontier growth,
deleted-vertex adjacency, empirical search, or packing. -/
theorem physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296_of_residualFiberTerminalNeighborImageCompression1296
    (hcompression :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborMenu, _hmenu_subset, hmenu_card,
      terminalNeighborOfParent, terminalNeighborSelectorEvidence,
      _hselector_mem_menu, himage_subset_menu⟩ :=
    hcompression root k deleted parentOf essential hchoice himage hessential_subset
  refine ⟨terminalNeighborOfParent, terminalNeighborSelectorEvidence, ?_⟩
  intro residual
  exact le_trans (Finset.card_le_card (himage_subset_menu residual))
    (hmenu_card residual)

/-- Terminal-neighbor data repacks into the v2.142 terminal-suffix interface.

The proof is projection-only: it renames the selected `terminalNeighbor` as the
terminal predecessor in `PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixData`
and carries the selected-image cardinality bound unchanged.  It does not
construct terminal neighbors, does not use deleted-vertex adjacency outside the
residual, and does not replace the image bound by path existence,
root/root-shell reachability, local degree, residual size, raw frontier growth,
or packing of an already bounded menu. -/
theorem physicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296_of_residualFiberCanonicalTerminalNeighborImageBound1296
    (hneighbor :
      PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296) :
    PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalNeighborData, hcard⟩ :=
    hneighbor root k deleted parentOf essential hchoice himage hessential_subset
  let terminalSuffixData :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixData
            residual p.1 :=
    fun residual p =>
      { target := (terminalNeighborData residual p).target
        target_eq := (terminalNeighborData residual p).target_eq
        source := (terminalNeighborData residual p).source
        canonicalWalk := (terminalNeighborData residual p).canonicalWalk
        terminalPred := (terminalNeighborData residual p).terminalNeighbor
        prefixToTerminalPred :=
          (terminalNeighborData residual p).prefixToTerminalNeighbor
        terminalSuffix := (terminalNeighborData residual p).terminalNeighborSuffix
        terminalSuffix_is_last_edge :=
          (terminalNeighborData residual p).terminalNeighbor_is_last_edge
        terminalCode := (terminalNeighborData residual p).terminalNeighborCode }
  refine ⟨terminalSuffixData, ?_⟩
  intro residual
  simpa [terminalSuffixData] using hcard residual

/-- Terminal-suffix data repacks into the v2.139 walk terminal-edge interface.

The proof is projection-only: it forgets the explicit prefix-to-terminal
predecessor field and carries the terminal suffix, final-edge adjacency, and
selected-image cardinality bound into the v2.139 contract.  It does not
construct terminal suffixes, does not use deleted-vertex adjacency outside the
residual, and does not replace the image bound by path existence,
root/root-shell reachability, local degree, residual size, raw frontier growth,
or packing of an already bounded menu. -/
theorem physicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296_of_residualFiberCanonicalTerminalSuffixImageBound1296
    (hsuffix :
      PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296) :
    PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalSuffixData, hcard⟩ :=
    hsuffix root k deleted parentOf essential hchoice himage hessential_subset
  let walkTerminalEdgeData :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeData
            residual p.1 :=
    fun residual p =>
      { target := (terminalSuffixData residual p).target
        target_eq := (terminalSuffixData residual p).target_eq
        walkSource := (terminalSuffixData residual p).source
        canonicalWalk := (terminalSuffixData residual p).canonicalWalk
        terminalPred := (terminalSuffixData residual p).terminalPred
        terminalSuffix := (terminalSuffixData residual p).terminalSuffix
        terminalCode := (terminalSuffixData residual p).terminalCode }
  refine ⟨walkTerminalEdgeData, ?_, ?_⟩
  · intro residual p hnontrivial
    dsimp [walkTerminalEdgeData]
    exact (terminalSuffixData residual p).terminalSuffix_is_last_edge hnontrivial
  · intro residual
    simpa [walkTerminalEdgeData] using hcard residual

/-- Walk terminal-edge data repacks into the v2.136 terminal-edge selector.

This bridge is deliberately projection-only: it forgets the stronger v2.138
field names into `PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeData`.
It does not construct walk data, does not use deleted-vertex adjacency outside
the residual, and does not replace the selected-image bound by path existence,
root/root-shell reachability, local degree, residual size, raw frontier growth,
or packing of an already bounded menu. -/
theorem physicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296_of_residualFiberCanonicalWalkTerminalEdgeImageBound1296
    (hwalk :
      PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296) :
    PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨walkTerminalEdgeData, hterminalEdge, hcard⟩ :=
    hwalk root k deleted parentOf essential hchoice himage hessential_subset
  let terminalEdgeData :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeData
            residual p.1 :=
    fun residual p =>
      { target := (walkTerminalEdgeData residual p).target
        target_eq := (walkTerminalEdgeData residual p).target_eq
        pathSource := (walkTerminalEdgeData residual p).walkSource
        canonicalPath := (walkTerminalEdgeData residual p).canonicalWalk
        terminalPred := (walkTerminalEdgeData residual p).terminalPred
        terminalPath := (walkTerminalEdgeData residual p).terminalSuffix
        terminalCode := (walkTerminalEdgeData residual p).terminalCode }
  refine ⟨terminalEdgeData, ?_, ?_⟩
  · intro residual p hnontrivial
    dsimp [terminalEdgeData]
    exact hterminalEdge residual p hnontrivial
  · intro residual
    simpa [terminalEdgeData] using hcard residual

/-- Terminal-edge selector data repacks into the v2.132 canonical last-edge
image interface.

The proof projects the selected terminal predecessor and terminal path from the
new v2.135 data object.  It does not construct the selector, does not use
deleted-vertex adjacency outside the residual, and does not replace the selected
image bound by root-shell reachability, local degree, residual size, raw
frontier growth, or empirical search. -/
theorem physicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296_of_residualFiberCanonicalTerminalEdgeSelector1296
    (hselector :
      PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296) :
    PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨terminalEdgeData, hterminalEdge, hcard⟩ :=
    hselector root k deleted parentOf essential hchoice himage hessential_subset
  let canonicalLastEdgeData :
      ∀ residual,
        (p : {p : ConcretePlaquette physicalClayDimension L //
          p ∈ essential residual}) →
          PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData
            residual p.1 :=
    fun residual p =>
      { target := (terminalEdgeData residual p).target
        target_eq := (terminalEdgeData residual p).target_eq
        predecessor := (terminalEdgeData residual p).terminalPred
        path := (terminalEdgeData residual p).terminalPath
        code := (terminalEdgeData residual p).terminalCode }
  refine ⟨canonicalLastEdgeData, ?_, ?_⟩
  · intro residual p hnontrivial
    dsimp [canonicalLastEdgeData]
    exact hterminalEdge residual p hnontrivial
  · intro residual
    simpa [canonicalLastEdgeData] using hcard residual

/-- Residual-fiber selected terminal-predecessor image bound.

This is the graph-theoretic producer core behind
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`.  It is
indexed by the same v2.121 base-aware bookkeeping data and hypotheses, but it
does not package a menu existential directly.  Instead it asks for a
residual-indexed terminal-predecessor selector and the bound that the selector
image has cardinality at most `1296`.  The bridge below turns this image into
the menu required by the v2.126 producer interface. -/
def PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∃ terminalPredOfParent :
        ∀ residual,
          {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
        (∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual}),
          residual.card ≠ 1 →
            p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
              (terminalPredOfParent residual p).1) ∧
        (∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual}),
          ∃ target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual},
            target.1 = p.1 ∧
              Nonempty
                (((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
                  (terminalPredOfParent residual p) target)) ∧
        ∀ residual,
          ((essential residual).attach.image
            (fun p => (terminalPredOfParent residual p).1)).card ≤ 1296

/-- Canonical residual last-edge data projects to the v2.129 selected-image
interface.

The proof only repackages the `predecessor`, `target`, `target_eq`, and `path`
fields of `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData`.  It
does not construct canonical paths, does not use deleted-vertex adjacency
outside the residual, and does not invoke empirical search evidence. -/
theorem physicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296_of_residualFiberCanonicalLastEdgeImageBound1296
    (hcanonical :
      PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset
  letI : NeZero L := hL
  obtain ⟨canonicalLastEdgeData, hlastEdge, hcard⟩ :=
    hcanonical root k deleted parentOf essential hchoice himage hessential_subset
  let terminalPredOfParent :
      ∀ residual,
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} :=
    fun residual p => (canonicalLastEdgeData residual p).predecessor
  refine ⟨terminalPredOfParent, ?_, ?_, ?_⟩
  · intro residual p hcard_ne
    exact hlastEdge residual p hcard_ne
  · intro residual p
    refine ⟨(canonicalLastEdgeData residual p).target, ?_, ?_⟩
    · exact (canonicalLastEdgeData residual p).target_eq
    · exact ⟨(canonicalLastEdgeData residual p).path⟩
  · intro residual
    exact hcard residual

/-- Residual-fiber terminal-predecessor domination producer.

This is the producer counterpart to
`PhysicalPlaquetteGraphResidualDominatedTerminalPredecessorPacking1296`.  It is
indexed by the `deleted`/`parentOf`/`essential` data and bookkeeping clauses
from `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`;
therefore it does not claim that arbitrary `essential ⊆ residual` data is
last-edge dominated.  It supplies only the explicit selected menu, selected
terminal predecessor, path/domination evidence, and menu cardinality bound
that the v2.124 packing theorem can code into `Fin 1296`. -/
def PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
        deleted X ≠ root ∧
        X.erase (deleted X) ∈
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) ∧
        parentOf X ∈ X.erase (deleted X) ∧
        parentOf X ∈ essential (X.erase (deleted X)) ∧
        (((X.erase (deleted X)).card = 1 ∧
            parentOf X = root ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
          ((X.erase (deleted X)).card ≠ 1 ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) →
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) →
    (∀ residual, essential residual ⊆ residual) →
      ∀ residual,
        ∃ terminalPredMenu : Finset (ConcretePlaquette physicalClayDimension L),
        ∃ terminalPredOfParent :
          {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
          terminalPredMenu ⊆ residual ∧
          terminalPredMenu =
            (essential residual).attach.image
              (fun p => (terminalPredOfParent p).1) ∧
          (∀ p, (terminalPredOfParent p).1 ∈ terminalPredMenu) ∧
          (residual.card ≠ 1 →
            ∀ p : {p : ConcretePlaquette physicalClayDimension L //
                p ∈ essential residual},
              p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
                (terminalPredOfParent p).1) ∧
          (∀ p : {p : ConcretePlaquette physicalClayDimension L //
              p ∈ essential residual},
            ∃ target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual},
              target.1 = p.1 ∧
                Nonempty
                  (((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
                    (terminalPredOfParent p) target)) ∧
          terminalPredMenu.card ≤ 1296

/-- A residual-fiber selected-image bound supplies the v2.126 residual-fiber
terminal-predecessor producer.

The proof is purely a repacking bridge: it defines the terminal predecessor menu
as the image of the residual-indexed selector.  It does not construct the
selector, does not use deleted-vertex adjacency outside the residual, and does
not invoke empirical search evidence. -/
theorem physicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296_of_residualFiberTerminalPredecessorImageBound1296
    (himageBound :
      PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296 := by
  classical
  intro L hL root k deleted parentOf essential hchoice himage hessential_subset residual
  letI : NeZero L := hL
  obtain ⟨terminalPredOfParent, hlastEdge, hpath, hcard⟩ :=
    himageBound root k deleted parentOf essential hchoice himage hessential_subset
  let terminalPredMenu : Finset (ConcretePlaquette physicalClayDimension L) :=
    (essential residual).attach.image
      (fun p => (terminalPredOfParent residual p).1)
  refine ⟨terminalPredMenu, terminalPredOfParent residual, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    dsimp [terminalPredMenu] at hq
    rcases Finset.mem_image.mp hq with ⟨p, _hp, rfl⟩
    exact (terminalPredOfParent residual p).2
  · rfl
  · intro p
    dsimp [terminalPredMenu]
    exact Finset.mem_image.mpr ⟨p, by simp, rfl⟩
  · intro hcard_ne p
    exact hlastEdge residual p hcard_ne
  · intro p
    exact hpath residual p
  · exact hcard residual

/-- Base-aware deletion/parent bookkeeping for the terminal-predecessor bridge.

This contains exactly the `deleted`, `parentOf`, and `essential` data needed to
feed the residual-only terminal-predecessor domination theorem.  It deliberately
does not contain terminal-predecessor menus, codes, paths, or selected-image
bounds; those remain the responsibility of
`PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296`. -/
def PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
      (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X ∈ X ∧
          deleted X ≠ root ∧
          X.erase (deleted X) ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          parentOf X ∈ X.erase (deleted X) ∧
          parentOf X ∈ essential (X.erase (deleted X)) ∧
          (((X.erase (deleted X)).card = 1 ∧
              parentOf X = root ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
            ((X.erase (deleted X)).card ≠ 1 ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) ∧
      (∀ residual,
        essential residual =
          ((plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root k).filter
              (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
      ∀ residual, essential residual ⊆ residual

/-- Low-cardinality non-root fallback witness for base-aware bookkeeping.

The intended proof should come from the concrete physical plaquette
representation.  It is separated from the bookkeeping interface so the `k < 2`
branch cannot hide a non-root deleted plaquette behind an arbitrary default. -/
def PhysicalPlaquetteGraphRootHasDistinctPlaquette : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L),
    ∃ fallbackDeleted : ConcretePlaquette physicalClayDimension L,
      fallbackDeleted ≠ root

/-- Low-cardinality totalization for the v2.116 base-aware bookkeeping interface.

This interface isolates the `k ≤ 1` residual-fiber image/subset obligation.  It
does not invoke safe deletion, which is only available for `2 ≤ k`.  The
load-bearing low-cardinality clause is explicit: every current low-cardinality
anchored bucket must have `parentOf X ∈ X.erase (deleted X)`, so the eventual
proof cannot rely on hidden arbitrary defaults.

The intended bridge back into
`PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296` splits on
`k ≤ 1`: this interface supplies the low-cardinality image/subset branch, while
the existing safe-deletion and residual-parent APIs supply the `2 ≤ k` branch. -/
def PhysicalPlaquetteGraphBaseAwareLowCardBookkeepingTotalization1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    k ≤ 1 →
    ∃ fallbackDeleted : ConcretePlaquette physicalClayDimension L,
      fallbackDeleted ≠ root ∧
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
      (∀ X : Finset (ConcretePlaquette physicalClayDimension L),
        deleted X = fallbackDeleted ∧ parentOf X = root) ∧
      (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (_hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        parentOf X ∈ X.erase (deleted X)) ∧
      (∀ residual,
        essential residual =
          ((plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root k).filter
              (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
      ∀ residual, essential residual ⊆ residual

/-- Residual last-edge dominating-set bound for the v2.107 selector route.

This is deliberately factored below
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`.
It names a residual-only terminal-predecessor menu and an injective `Fin 1296`
code on that menu.  The mathematical burden is the selected terminal-predecessor
image; this is not a raw residual-frontier bound, not a residual-cardinality
bound, not the local degree of one fixed portal, and not first-shell
reachability. -/
def PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
      (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X ∈ X ∧
          deleted X ≠ root ∧
          X.erase (deleted X) ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          parentOf X ∈ X.erase (deleted X) ∧
          parentOf X ∈ essential (X.erase (deleted X)) ∧
          (((X.erase (deleted X)).card = 1 ∧
              parentOf X = root ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
            ((X.erase (deleted X)).card ≠ 1 ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) ∧
      ∃ terminalPredMenu :
        Finset (ConcretePlaquette physicalClayDimension L) →
          Finset (ConcretePlaquette physicalClayDimension L),
      ∃ terminalPredOfParent :
        ∀ residual,
          {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalPredCode :
        ∀ residual,
          {q : ConcretePlaquette physicalClayDimension L //
            q ∈ terminalPredMenu residual} → Fin 1296,
      ∃ terminalPredPath :
        ∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
          ∃ target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual},
            target.1 = p.1 ∧
              Nonempty
                (((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
                  (terminalPredOfParent residual p) target),
        (∀ residual,
          essential residual =
            ((plaquetteGraphPreconnectedSubsetsAnchoredCard
                physicalClayDimension L root k).filter
                (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
        (∀ residual, essential residual ⊆ residual) ∧
        (∀ residual,
          terminalPredMenu residual ⊆ residual ∧
            Function.Injective (terminalPredCode residual)) ∧
        (∀ residual,
          terminalPredMenu residual =
            (essential residual).attach.image
              (fun p => (terminalPredOfParent residual p).1)) ∧
        (∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
          (terminalPredOfParent residual p).1 ∈ terminalPredMenu residual) ∧
        ∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
          residual.card ≠ 1 →
            p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
              (terminalPredOfParent residual p).1

/-- Base-aware bookkeeping plus residual-only terminal-predecessor domination
repack into the v2.107 residual last-edge dominating-set interface.

This bridge proves no bookkeeping theorem and no terminal-predecessor domination
theorem.  It only applies the residual-only domination theorem to each
`essential residual` supplied by the bookkeeping layer and repacks the fields. -/
theorem physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_terminalPredecessorDomination1296
    (hbook : PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296)
    (hterminal : PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296) :
    PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨deleted, parentOf, essential, hchoice, himage, hessential_subset⟩ :=
    hbook root k
  let hwit :
      ∀ residual,
        ∃ terminalPredMenu : Finset (ConcretePlaquette physicalClayDimension L),
        ∃ terminalPredOfParent :
          {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
        ∃ terminalPredCode :
          {q : ConcretePlaquette physicalClayDimension L //
            q ∈ terminalPredMenu} → Fin 1296,
          terminalPredMenu ⊆ residual ∧
          Function.Injective terminalPredCode ∧
          terminalPredMenu =
            (essential residual).attach.image (fun p => (terminalPredOfParent p).1) ∧
          (∀ p, (terminalPredOfParent p).1 ∈ terminalPredMenu) ∧
          (residual.card ≠ 1 →
            ∀ p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual},
              p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
                (terminalPredOfParent p).1) ∧
          ∀ p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual},
            ∃ target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual},
              target.1 = p.1 ∧
                Nonempty
                  (((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
                    (terminalPredOfParent p) target) :=
    fun residual => hterminal residual (essential residual) (hessential_subset residual)
  let terminalPredMenu :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L) :=
    fun residual => Classical.choose (hwit residual)
  let hwitMenu residual := Classical.choose_spec (hwit residual)
  let terminalPredOfParent :
      ∀ residual,
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} :=
    fun residual => Classical.choose (hwitMenu residual)
  let hwitParent residual := Classical.choose_spec (hwitMenu residual)
  let terminalPredCode :
      ∀ residual,
        {q : ConcretePlaquette physicalClayDimension L //
          q ∈ terminalPredMenu residual} → Fin 1296 :=
    fun residual => Classical.choose (hwitParent residual)
  let hprops residual := Classical.choose_spec (hwitParent residual)
  let terminalPredPath :
      ∀ residual
        (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
        ∃ target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual},
          target.1 = p.1 ∧
            Nonempty
              (((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
                (terminalPredOfParent residual p) target) :=
    fun residual p => (hprops residual).2.2.2.2.2 p
  refine ⟨deleted, parentOf, essential, hchoice, terminalPredMenu,
    terminalPredOfParent, terminalPredCode, terminalPredPath, himage, hessential_subset,
    ?_, ?_, ?_, ?_⟩
  · intro residual
    exact ⟨(hprops residual).1, (hprops residual).2.1⟩
  · intro residual
    exact (hprops residual).2.2.1
  · intro residual p
    exact (hprops residual).2.2.2.1 p
  · intro residual p hcard
    exact (hprops residual).2.2.2.2.1 hcard p

/-- Base-aware bookkeeping plus a residual-fiber terminal-predecessor producer
and the explicit packing theorem repack into the v2.107 residual last-edge
dominating-set interface.

This bridge does not prove the residual-fiber domination producer and does not
infer domination from arbitrary `essential ⊆ residual` data.  The producer
supplies the selected menu, last-edge domination evidence, residual path
evidence, and cardinality bound for the bookkeeping fiber; the packing theorem
only supplies the injective `Fin 1296` code. -/
theorem physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_residualFiberTerminalPredecessorDomination1296_of_packing1296
    (hbook : PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296)
    (hfiber : PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296)
    (hpacking : PhysicalPlaquetteGraphResidualDominatedTerminalPredecessorPacking1296) :
    PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨deleted, parentOf, essential, hchoice, himage, hessential_subset⟩ :=
    hbook root k
  let hwit :
      ∀ residual,
        ∃ terminalPredMenu : Finset (ConcretePlaquette physicalClayDimension L),
        ∃ terminalPredOfParent :
          {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
          terminalPredMenu ⊆ residual ∧
          terminalPredMenu =
            (essential residual).attach.image (fun p => (terminalPredOfParent p).1) ∧
          (∀ p, (terminalPredOfParent p).1 ∈ terminalPredMenu) ∧
          (residual.card ≠ 1 →
            ∀ p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual},
              p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
                (terminalPredOfParent p).1) ∧
          (∀ p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual},
            ∃ target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual},
              target.1 = p.1 ∧
                Nonempty
                  (((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
                    (terminalPredOfParent p) target)) ∧
          terminalPredMenu.card ≤ 1296 :=
    fun residual => hfiber root k deleted parentOf essential hchoice himage
      hessential_subset residual
  let terminalPredMenu :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L) :=
    fun residual => Classical.choose (hwit residual)
  let hwitMenu residual := Classical.choose_spec (hwit residual)
  let terminalPredOfParent :
      ∀ residual,
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} :=
    fun residual => Classical.choose (hwitMenu residual)
  let hprops residual := Classical.choose_spec (hwitMenu residual)
  let terminalPredCode :
      ∀ residual,
        {q : ConcretePlaquette physicalClayDimension L //
          q ∈ terminalPredMenu residual} → Fin 1296 :=
    fun residual =>
      Classical.choose
        (hpacking residual (essential residual) (terminalPredMenu residual)
          (terminalPredOfParent residual) (hessential_subset residual)
          (hprops residual).1 (hprops residual).2.1 (hprops residual).2.2.1
          (hprops residual).2.2.2.1 (hprops residual).2.2.2.2.1
          (hprops residual).2.2.2.2.2)
  let hcode_inj residual :
      Function.Injective (terminalPredCode residual) :=
    Classical.choose_spec
      (hpacking residual (essential residual) (terminalPredMenu residual)
        (terminalPredOfParent residual) (hessential_subset residual)
        (hprops residual).1 (hprops residual).2.1 (hprops residual).2.2.1
        (hprops residual).2.2.2.1 (hprops residual).2.2.2.2.1
        (hprops residual).2.2.2.2.2)
  let terminalPredPath :
      ∀ residual
        (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
        ∃ target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual},
          target.1 = p.1 ∧
            Nonempty
              (((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
                (terminalPredOfParent residual p) target) :=
    fun residual p => (hprops residual).2.2.2.2.1 p
  refine ⟨deleted, parentOf, essential, hchoice, terminalPredMenu,
    terminalPredOfParent, terminalPredCode, terminalPredPath, himage, hessential_subset,
    ?_, ?_, ?_, ?_⟩
  · intro residual
    exact ⟨(hprops residual).1, hcode_inj residual⟩
  · intro residual
    exact (hprops residual).2.1
  · intro residual p
    exact (hprops residual).2.2.1 p
  · intro residual p hcard
    exact (hprops residual).2.2.2.1 hcard p

/-- A residual-only terminal-predecessor dominating menu supplies the v2.107
last-edge selector interface.  The bridge only repacks the named menu, selected
predecessor, and `Fin 1296` code; it proves no dominating-set existence theorem
and uses no empirical search evidence. -/
theorem physicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296_of_residualLastEdgeDominatingSetBound1296
    (hbound : PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296) :
    PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨deleted, parentOf, essential, hchoice, terminalPredMenu,
    terminalPredOfParent, terminalPredCode, terminalPredPath, himage, _hessential_subset,
    hmenu, _hmenu_image, hpred_mem_menu, hlastEdge⟩ :=
    hbound root k
  let canonicalLastEdgeData :
      ∀ residual
        (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
          PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData residual p.1 :=
    fun residual p =>
      let codePred :
          {q : ConcretePlaquette physicalClayDimension L //
            q ∈ terminalPredMenu residual} :=
        ⟨(terminalPredOfParent residual p).1, hpred_mem_menu residual p⟩
      let pathData := terminalPredPath residual p
      { target := Classical.choose pathData
        target_eq := (Classical.choose_spec pathData).1
        predecessor := terminalPredOfParent residual p
        path := Classical.choice (Classical.choose_spec pathData).2
        code := terminalPredCode residual codePred }
  refine ⟨deleted, parentOf, essential, hchoice, canonicalLastEdgeData,
    himage, ?_, ?_, ?_⟩
  · intro residual p hcard
    dsimp [canonicalLastEdgeData]
    exact hlastEdge residual p hcard
  · intro residual p q hcode
    dsimp [canonicalLastEdgeData] at hcode ⊢
    exact congrArg
      (fun q : {q : ConcretePlaquette physicalClayDimension L //
          q ∈ terminalPredMenu residual} => q.1)
      ((hmenu residual).2 hcode)
  · intro residual
    have hcard :=
      Fintype.card_le_of_injective (terminalPredCode residual) (hmenu residual).2
    have himage_subset :
        (essential residual).attach.image
            (fun p => (canonicalLastEdgeData residual p).predecessor.1) ⊆
          terminalPredMenu residual := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨p, _hp, rfl⟩ := hq
      dsimp [canonicalLastEdgeData]
      exact hpred_mem_menu residual p
    exact (Finset.card_le_card himage_subset).trans
      (by simpa [Fintype.card_fin] using hcard)

/-- Base-aware residual portal-menu bound for the v2.95 producer route.

This is deliberately factored as a sharper interface than the producer itself:
it first asks for the base-aware safe-deletion/parent choices, and then asks for
the residual-only non-singleton portal-menu cover for the resulting essential
parent fibers.  The mathematical burden is the portal-menu cover, not the
singleton root-shell branch and not a compression to any older decoder
constant. -/
def PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
      (∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X ∈ X ∧
          deleted X ≠ root ∧
          X.erase (deleted X) ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          parentOf X ∈ X.erase (deleted X) ∧
          parentOf X ∈ essential (X.erase (deleted X)) ∧
          (((X.erase (deleted X)).card = 1 ∧
              parentOf X = root ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset root) ∨
            ((X.erase (deleted X)).card ≠ 1 ∧
              deleted X ∈
                (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) ∧
      ∃ portalMenu :
        Finset (ConcretePlaquette physicalClayDimension L) →
          Finset (ConcretePlaquette physicalClayDimension L),
      ∃ portalOfParent :
        ∀ residual,
          {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
            ConcretePlaquette physicalClayDimension L,
        (∀ residual,
          essential residual =
            ((plaquetteGraphPreconnectedSubsetsAnchoredCard
                physicalClayDimension L root k).filter
                (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
        (∀ residual,
          portalMenu residual ⊆ residual ∧ (portalMenu residual).card ≤ 1296) ∧
        ∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}),
          residual.card ≠ 1 →
            portalOfParent residual p ∈ portalMenu residual ∧
              p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
                (portalOfParent residual p)

/-- A bounded last-step portal image yields the v2.98 base-aware residual
portal-menu bound by taking the portal menu to be exactly that selected image.
This bridge proves no image bound itself and makes no compression claim. -/
theorem physicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296_of_baseAwareResidualLastStepPortalImageBound1296
    (hbound : PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296) :
    PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨deleted, parentOf, essential, hchoice, lastStepPortalOfParent,
    himage, hlastStepPortal, himageBound⟩ := hbound root k
  let portalMenu :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L) :=
    fun residual =>
      (essential residual).attach.image
        (fun p => lastStepPortalOfParent residual p)
  refine ⟨deleted, parentOf, essential, hchoice, portalMenu,
    lastStepPortalOfParent, himage, ?_, ?_⟩
  · intro residual
    constructor
    · intro portal hportal
      dsimp [portalMenu] at hportal
      rw [Finset.mem_image] at hportal
      obtain ⟨p, _hp, rfl⟩ := hportal
      exact (hlastStepPortal residual p).1
    · exact himageBound residual
  · intro residual p hsingle
    exact ⟨by
      dsimp [portalMenu]
      rw [Finset.mem_image]
      exact ⟨p, by simp, rfl⟩, (hlastStepPortal residual p).2 hsingle⟩

/-- Canonical predecessor data repacks into the v2.101 last-step portal-image
interface by projecting out the predecessor component.  The `Fin 1296` code and
separation clause remain available for the future proof of the image bound; this
bridge itself proves no compression theorem. -/
theorem physicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296_of_baseAwareResidualCanonicalLastStepPredecessorImageBound1296
    (hbound :
      PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296) :
    PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨deleted, parentOf, essential, hchoice, canonicalLastStepPredecessor,
    himage, hadjacent, _hseparate, himageBound⟩ := hbound root k
  let lastStepPortalOfParent :
      ∀ residual,
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
          ConcretePlaquette physicalClayDimension L :=
    fun residual p => (canonicalLastStepPredecessor residual p).1.1
  refine ⟨deleted, parentOf, essential, hchoice, lastStepPortalOfParent,
    himage, ?_, ?_⟩
  · intro residual p
    constructor
    · exact (canonicalLastStepPredecessor residual p).1.2
    · exact hadjacent residual p
  · intro residual
    simpa [lastStepPortalOfParent] using himageBound residual

/-- Residual last-edge selector data repacks into the v2.104 canonical
last-step predecessor interface by projecting out its selected predecessor and
`Fin 1296` code.  This bridge proves no selector existence theorem and does not
compress any strengthened decoder alphabet. -/
theorem physicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296_of_baseAwareResidualCanonicalLastEdgePredecessorSelector1296
    (hbound :
      PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296) :
    PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨deleted, parentOf, essential, hchoice, canonicalLastEdgeData,
    himage, hadjacent, hseparate, himageBound⟩ := hbound root k
  let canonicalLastStepPredecessor :
      ∀ residual,
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} × Fin 1296 :=
    fun residual p =>
      ((canonicalLastEdgeData residual p).predecessor,
        (canonicalLastEdgeData residual p).code)
  refine ⟨deleted, parentOf, essential, hchoice, canonicalLastStepPredecessor,
    himage, ?_, ?_, ?_⟩
  · intro residual p
    simpa [canonicalLastStepPredecessor] using hadjacent residual p
  · intro residual p q hcode
    exact hseparate residual p q hcode
  · intro residual
    simpa [canonicalLastStepPredecessor] using himageBound residual

/-- The factored base-aware portal-menu bound repacks directly into the v2.95
base-aware multi-portal producer interface.  This bridge introduces no
compression claim and does not prove the portal-menu bound itself. -/
theorem physicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296_of_baseAwareResidualPortalMenuBound1296
    (hbound : PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296) :
    PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨deleted, parentOf, essential, hchoice, portalMenu, portalOfParent,
    himage, hportalMenu, hportalSupport⟩ := hbound root k
  exact ⟨deleted, parentOf, essential, portalMenu, portalOfParent,
    himage, hportalMenu, hportalSupport, hchoice⟩

/-- A multi-portal orientation yields the triple-symbol decoder contract by
enumerating the residual portal menu and then using the existing local neighbor
decoder twice: once from portal to parent, and once from parent to the deleted
plaquette.  This is a bridge only; it does not compress the triple symbol back
to the old `1296` or `1296 × 1296` constants. -/
theorem physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296_of_multiPortalSupportedSafeDeletionOrientation1296x1296
    (hmulti : PhysicalPlaquetteGraphMultiPortalSupportedSafeDeletionOrientation1296x1296) :
    PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨deleted, parentOf, essential, portalMenu, portalOfParent,
    _himage, hportalMenu, hportalSupport, hchoice⟩ := hmulti root k
  obtain ⟨code, hinj⟩ :=
    (plaquetteNeighborStepCodeBoundDim_physical_ternary (L := L))
  let portalDecode :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Fin 1296 → Option (ConcretePlaquette physicalClayDimension L) :=
    fun residual symbol =>
      if h :
          ∃ p : {p : ConcretePlaquette physicalClayDimension L // p ∈ portalMenu residual},
            finsetCodeOfCardLe (portalMenu residual) (hportalMenu residual).2 p = symbol then
        some (Classical.choose h).1
      else
        none
  refine ⟨fun residual symbol =>
    match portalDecode residual symbol.1 with
    | some portal =>
        match physicalNeighborDecodeOfStepCode code portal symbol.2.1 with
        | some parent => physicalNeighborDecodeOfStepCode code parent symbol.2.2
        | none => none
    | none => none, ?_⟩
  intro X hk hX
  obtain ⟨hzX, hz_ne_root, hresidual, hp_residual, hp_essential, hz_parent⟩ :=
    hchoice hk hX
  let residual := X.erase (deleted X)
  let parentSubtype :
      {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} :=
    ⟨parentOf X, hp_essential⟩
  let portal := portalOfParent residual parentSubtype
  have hportal := hportalSupport residual parentSubtype
  let portalSymbol : Fin 1296 :=
    finsetCodeOfCardLe (portalMenu residual) (hportalMenu residual).2
      ⟨portal, hportal.1⟩
  let parentSymbol : Fin 1296 := code portal (parentOf X)
  let deletedSymbol : Fin 1296 := code (parentOf X) (deleted X)
  refine ⟨deleted X, hzX, hz_ne_root, hresidual,
    (portalSymbol, (parentSymbol, deletedSymbol)), ?_⟩
  have hportalDecode :
      portalDecode residual portalSymbol = some portal := by
    dsimp [portalDecode, portalSymbol]
    rw [dif_pos ⟨⟨portal, hportal.1⟩, rfl⟩]
    have hchoose :=
      Classical.choose_spec
        (show
          ∃ q : {p : ConcretePlaquette physicalClayDimension L // p ∈ portalMenu residual},
            finsetCodeOfCardLe (portalMenu residual) (hportalMenu residual).2 q =
              finsetCodeOfCardLe (portalMenu residual) (hportalMenu residual).2
                ⟨portal, hportal.1⟩ from
          ⟨⟨portal, hportal.1⟩, rfl⟩)
    have hsub :
        Classical.choose
            (show
              ∃ q : {p : ConcretePlaquette physicalClayDimension L // p ∈ portalMenu residual},
                finsetCodeOfCardLe (portalMenu residual) (hportalMenu residual).2 q =
                  finsetCodeOfCardLe (portalMenu residual) (hportalMenu residual).2
                    ⟨portal, hportal.1⟩ from
              ⟨⟨portal, hportal.1⟩, rfl⟩) =
          ⟨portal, hportal.1⟩ :=
      finsetCodeOfCardLe_injective (portalMenu residual) (hportalMenu residual).2
        hchoose
    exact congrArg some (congrArg Subtype.val hsub)
  have hparentDecode :
      physicalNeighborDecodeOfStepCode code portal parentSymbol =
        some (parentOf X) := by
    simpa [parentSymbol] using
      physicalNeighborDecodeOfStepCode_spec hinj hportal.2
  have hdeletedDecode :
      physicalNeighborDecodeOfStepCode code (parentOf X) deletedSymbol =
        some (deleted X) := by
    simpa [deletedSymbol] using
      physicalNeighborDecodeOfStepCode_spec hinj hz_parent
  dsimp
  rw [hportalDecode]
  simp [hparentDecode, hdeletedDecode]

/-- A base-aware multi-portal orientation yields the triple-symbol decoder
contract.  Singleton residuals use the third symbol as a direct root-shell code;
non-singleton residuals use the v2.92 portal → parent → deleted route.  This is
still a triple-symbol bridge only and does not compress to older constants. -/
theorem physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296_of_baseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
    (hmulti :
      PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296) :
    PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨deleted, parentOf, essential, portalMenu, portalOfParent,
    _himage, hportalMenu, hportalSupport, hchoice⟩ := hmulti root k
  obtain ⟨code, hinj⟩ :=
    (plaquetteNeighborStepCodeBoundDim_physical_ternary (L := L))
  let portalDecode :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Fin 1296 → Option (ConcretePlaquette physicalClayDimension L) :=
    fun residual symbol =>
      if h :
          ∃ p : {p : ConcretePlaquette physicalClayDimension L // p ∈ portalMenu residual},
            finsetCodeOfCardLe (portalMenu residual) (hportalMenu residual).2 p = symbol then
        some (Classical.choose h).1
      else
        none
  refine ⟨fun residual symbol =>
    if h : residual.card = 1 then
      physicalNeighborDecodeOfStepCode code root symbol.2.2
    else
      match portalDecode residual symbol.1 with
      | some portal =>
          match physicalNeighborDecodeOfStepCode code portal symbol.2.1 with
          | some parent => physicalNeighborDecodeOfStepCode code parent symbol.2.2
          | none => none
      | none => none, ?_⟩
  intro X hk hX
  obtain ⟨hzX, hz_ne_root, hresidual, hp_residual, hp_essential, hbranch⟩ :=
    hchoice hk hX
  let residual := X.erase (deleted X)
  rcases hbranch with hbase | hrecursive
  · rcases hbase with ⟨hres_card, _hp_root, hz_root⟩
    let deletedSymbol : Fin 1296 := code root (deleted X)
    refine ⟨deleted X, hzX, hz_ne_root, hresidual,
      ((0 : Fin 1296), ((0 : Fin 1296), deletedSymbol)), ?_⟩
    have hdeletedDecode :
        physicalNeighborDecodeOfStepCode code root deletedSymbol =
          some (deleted X) := by
      simpa [deletedSymbol] using
        physicalNeighborDecodeOfStepCode_spec hinj hz_root
    simp [hres_card, hdeletedDecode]
  · rcases hrecursive with ⟨hres_card_ne, hz_parent⟩
    let parentSubtype :
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} :=
      ⟨parentOf X, hp_essential⟩
    let portal := portalOfParent residual parentSubtype
    have hportal := hportalSupport residual parentSubtype hres_card_ne
    let portalSymbol : Fin 1296 :=
      finsetCodeOfCardLe (portalMenu residual) (hportalMenu residual).2
        ⟨portal, hportal.1⟩
    let parentSymbol : Fin 1296 := code portal (parentOf X)
    let deletedSymbol : Fin 1296 := code (parentOf X) (deleted X)
    refine ⟨deleted X, hzX, hz_ne_root, hresidual,
      (portalSymbol, (parentSymbol, deletedSymbol)), ?_⟩
    have hportalDecode :
        portalDecode residual portalSymbol = some portal := by
      dsimp [portalDecode, portalSymbol]
      rw [dif_pos ⟨⟨portal, hportal.1⟩, rfl⟩]
      have hchoose :=
        Classical.choose_spec
          (show
            ∃ q : {p : ConcretePlaquette physicalClayDimension L // p ∈ portalMenu residual},
              finsetCodeOfCardLe (portalMenu residual) (hportalMenu residual).2 q =
                finsetCodeOfCardLe (portalMenu residual) (hportalMenu residual).2
                  ⟨portal, hportal.1⟩ from
            ⟨⟨portal, hportal.1⟩, rfl⟩)
      have hsub :
          Classical.choose
              (show
                ∃ q : {p : ConcretePlaquette physicalClayDimension L // p ∈ portalMenu residual},
                  finsetCodeOfCardLe (portalMenu residual) (hportalMenu residual).2 q =
                    finsetCodeOfCardLe (portalMenu residual) (hportalMenu residual).2
                      ⟨portal, hportal.1⟩ from
                ⟨⟨portal, hportal.1⟩, rfl⟩) =
            ⟨portal, hportal.1⟩ :=
        finsetCodeOfCardLe_injective (portalMenu residual) (hportalMenu residual).2
          hchoose
      exact congrArg some (congrArg Subtype.val hsub)
    have hparentDecode :
        physicalNeighborDecodeOfStepCode code portal parentSymbol =
          some (parentOf X) := by
      simpa [parentSymbol] using
        physicalNeighborDecodeOfStepCode_spec hinj hportal.2
    have hdeletedDecode :
        physicalNeighborDecodeOfStepCode code (parentOf X) deletedSymbol =
          some (deleted X) := by
      simpa [deletedSymbol] using
        physicalNeighborDecodeOfStepCode_spec hinj hz_parent
    simp [residual, hres_card_ne, hportalDecode, hparentDecode, hdeletedDecode]

/-- Portal-supported safe-deletion orientation for the v2.86 policy.

This is a strictly more structured target than
`PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296`: it does not
provide an orientation code.  Instead, it requires the essential chosen-parent
menu over every residual fiber to lie inside the local neighbor shell of a
residual-only portal.  The bridge below then derives the `Fin 1296` orientation
code from the already proved physical local neighbor-code bound. -/
def PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ portal :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Option (ConcretePlaquette physicalClayDimension L),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
      (∀ residual,
        essential residual =
          ((plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root k).filter
              (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
      (∀ residual, essential residual ⊆ residual) ∧
      (∀ residual,
        match portal residual with
        | some portalPoint =>
            essential residual ⊆
              (plaquetteGraph physicalClayDimension L).neighborFinset portalPoint
        | none => essential residual = ∅) ∧
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X ∈ X ∧
          deleted X ≠ root ∧
          X.erase (deleted X) ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          parentOf X ∈ X.erase (deleted X) ∧
          parentOf X ∈ essential (X.erase (deleted X)) ∧
          ∃ portalX,
            portal (X.erase (deleted X)) = some portalX ∧
            parentOf X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset portalX ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)

/-- A portal-local chosen-parent shell yields the orientation-code interface by
coding chosen parents with the local physical neighbor code of the residual
portal.  This bridge is conditional: it does not prove the portal-supported
orientation policy itself. -/
theorem physicalPlaquetteGraphSafeDeletionOrientationCodeBound1296_of_portalSupportedSafeDeletionOrientation1296
    (hportal : PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296) :
    PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨portal, deleted, parentOf, essential, himage, hsubset,
    hportal_shell, hchoice⟩ := hportal root k
  obtain ⟨code, hcode_inj⟩ :=
    (plaquetteNeighborStepCodeBoundDim_physical_ternary (L := L))
  let orientCode :
      ∀ residual,
        {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
          Fin 1296 :=
    fun residual p =>
      match portal residual with
      | some portalPoint => code portalPoint p.1
      | none => 0
  refine ⟨deleted, parentOf, essential, orientCode, himage, ?_, hsubset, ?_⟩
  · intro residual
    intro a b hab
    dsimp [orientCode] at hab
    cases hres : portal residual with
    | none =>
        have hempty : essential residual = ∅ := by
          simpa [hres] using hportal_shell residual
        have ha : a.1 ∈ (∅ : Finset (ConcretePlaquette physicalClayDimension L)) := by
          simpa [hempty] using a.2
        simp at ha
    | some portalPoint =>
        have hshell :
            essential residual ⊆
              (plaquetteGraph physicalClayDimension L).neighborFinset portalPoint := by
          simpa [hres] using hportal_shell residual
        have hab' : code portalPoint a.1 = code portalPoint b.1 := by
          simpa [hres] using hab
        apply Subtype.ext
        exact hcode_inj portalPoint (hshell a.2) (hshell b.2) hab'
  · intro X hk hX
    obtain ⟨hzX, hz_ne_root, hresidual, hp_residual, hp_essential,
      _portalX, _hportalX, _hp_shell, hneighbor⟩ := hchoice hk hX
    exact ⟨hzX, hz_ne_root, hresidual, hp_residual, hp_essential, hneighbor⟩

/-- A finite orientation-code injection into `Fin 1296` implies the essential
chosen-parent frontier bound. -/
theorem physicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296_of_safeDeletionOrientationCodeBound1296
    (horient : PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296) :
    PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296 := by
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨deleted, parentOf, essential, orientCode, himage, hcode_inj,
    hsubset, hchoice⟩ := horient root k
  refine ⟨deleted, parentOf, essential, himage, ?_, hchoice⟩
  intro residual
  refine ⟨hsubset residual, ?_⟩
  have hcard :=
    Fintype.card_le_of_injective (orientCode residual) (hcode_inj residual)
  simpa [Fintype.card_fin] using hcard

/-- Residual-frontier parent-menu bound for the strengthened symbolic B.2
decoder.

This is the missing bounded-menu statement isolated by v2.76.  It is different
from the local degree bound `plaquetteGraph_neighborFinset_card_le_physical_ternary`:
that theorem bounds the number of deleted plaquettes adjacent to one fixed
parent, while this proposition bounds the number of residual parent candidates
needed to cover all safe one-plaquette extensions of a residual bucket. -/
def PhysicalPlaquetteGraphResidualParentMenuBound1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ menu :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L),
      (∀ residual,
        menu residual ⊆ residual ∧ (menu residual).card ≤ 1296) ∧
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
          X.erase z ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          ∃ p, p ∈ menu (X.erase z) ∧
            z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p

/-- A proved essential safe-deletion parent-frontier bound gives the residual
parent-menu bound by taking each residual menu to be the essential parent image
over the canonical-deletion fiber.  This bridge is conditional: it does not
prove the essential frontier bound itself. -/
theorem physicalPlaquetteGraphResidualParentMenuBound1296_of_essentialSafeDeletionParentFrontierBound1296
    (hessential : PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296) :
    PhysicalPlaquetteGraphResidualParentMenuBound1296 := by
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨deleted, parentOf, essential, _himage, hessential_bound, hchoice⟩ :=
    hessential root k
  refine ⟨essential, hessential_bound, ?_⟩
  intro X hk hX
  obtain ⟨hzX, hz_ne_root, hresidual, hp_residual, hp_menu, hneighbor⟩ :=
    hchoice hk hX
  exact ⟨deleted X, hzX, hz_ne_root, hresidual, parentOf X, hp_menu, hneighbor⟩

/-- Residual-only parent-menu cover for the strengthened symbolic B.2 decoder.

For each residual bucket, the menu `parent residual : Fin 1296 → Option ...`
is fixed before the current extension is inspected.  The statement says that
every current anchored bucket has a safe deleted plaquette whose residual
neighbor-parent appears in that residual-only menu.  This is the exact
combinatorial content isolated by v2.74; it is still only a `Prop` target. -/
def PhysicalPlaquetteGraphResidualParentMenuCovers1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ parent :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Fin 1296 → Option (ConcretePlaquette physicalClayDimension L),
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
          X.erase z ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          ∃ parentSymbol : Fin 1296, ∃ p,
            parent (X.erase z) parentSymbol = some p ∧
            p ∈ X.erase z ∧
            z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p

/-- A proved residual-frontier menu-size bound can be enumerated into the
`Fin 1296` parent-menu interface.  This bridge is conditional: it does not prove
the residual-frontier bound itself. -/
theorem physicalPlaquetteGraphResidualParentMenuCovers1296_of_residualParentMenuBound1296
    (hbound : PhysicalPlaquetteGraphResidualParentMenuBound1296) :
    PhysicalPlaquetteGraphResidualParentMenuCovers1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨menu, hmenu_bound, hcover⟩ := hbound root k
  let parent :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Fin 1296 → Option (ConcretePlaquette physicalClayDimension L) :=
    fun residual symbol =>
      if h :
          ∃ p : {x : ConcretePlaquette physicalClayDimension L // x ∈ menu residual},
            finsetCodeOfCardLe (menu residual) (hmenu_bound residual).2 p = symbol then
        some (Classical.choose h).1
      else
        none
  refine ⟨parent, ?_⟩
  intro X hk hX
  obtain ⟨z, hzX, hz_ne_root, hresidual, p, hp_menu, hzp⟩ := hcover hk hX
  let residual := X.erase z
  let code :=
    finsetCodeOfCardLe (menu residual) (hmenu_bound residual).2
  let parentSymbol : Fin 1296 := code ⟨p, hp_menu⟩
  refine ⟨z, hzX, hz_ne_root, hresidual, parentSymbol, p, ?_, ?_, hzp⟩
  · dsimp [parent, parentSymbol, code, residual]
    rw [dif_pos ⟨⟨p, hp_menu⟩, rfl⟩]
    have hchoose :=
      Classical.choose_spec
        (show
          ∃ q : {x : ConcretePlaquette physicalClayDimension L // x ∈ menu (X.erase z)},
            finsetCodeOfCardLe (menu (X.erase z)) (hmenu_bound (X.erase z)).2 q =
              finsetCodeOfCardLe (menu (X.erase z)) (hmenu_bound (X.erase z)).2
                ⟨p, hp_menu⟩ from
          ⟨⟨p, hp_menu⟩, rfl⟩)
    have hsub :
        Classical.choose
            (show
              ∃ q : {x : ConcretePlaquette physicalClayDimension L // x ∈ menu (X.erase z)},
                finsetCodeOfCardLe (menu (X.erase z)) (hmenu_bound (X.erase z)).2 q =
                  finsetCodeOfCardLe (menu (X.erase z)) (hmenu_bound (X.erase z)).2
                    ⟨p, hp_menu⟩ from
              ⟨⟨p, hp_menu⟩, rfl⟩) =
          ⟨p, hp_menu⟩ :=
      finsetCodeOfCardLe_injective (menu (X.erase z)) (hmenu_bound (X.erase z)).2
        hchoose
    exact congrArg some (congrArg Subtype.val hsub)
  · exact (hmenu_bound (X.erase z)).1 hp_menu

/-- Symbolic residual parent selector for the strengthened B.2 decoder.

Unlike `PhysicalPlaquetteGraphCanonicalResidualParentSelector1296`, the parent
may depend on a first `Fin 1296` component.  The residual alone no longer has to
choose a single parent for all current extensions; the symbol carries that
branch information. -/
def PhysicalPlaquetteGraphSymbolicResidualParentSelector1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ parent :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Fin 1296 → Option (ConcretePlaquette physicalClayDimension L),
    ∃ code : ConcretePlaquette physicalClayDimension L →
      ConcretePlaquette physicalClayDimension L → Fin 1296,
      (∀ p, Set.InjOn (code p)
        {q | q ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p}) ∧
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
          X.erase z ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          ∃ parentSymbol : Fin 1296, ∃ p,
            parent (X.erase z) parentSymbol = some p ∧
            p ∈ X.erase z ∧
            z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p

/-- A residual-only 1296-parent menu plus the existing physical local neighbor
code gives the symbolic residual-parent selector.  This is a bridge only: it
does not prove the parent-menu cover. -/
theorem physicalPlaquetteGraphSymbolicResidualParentSelector1296_of_residualParentMenuCovers1296
    (hmenu : PhysicalPlaquetteGraphResidualParentMenuCovers1296) :
    PhysicalPlaquetteGraphSymbolicResidualParentSelector1296 := by
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨parent, hparent⟩ := hmenu root k
  obtain ⟨code, hinj⟩ :=
    (plaquetteNeighborStepCodeBoundDim_physical_ternary (L := L))
  exact ⟨parent, code, hinj, hparent⟩

/-- A symbolic residual-parent selector closes the strengthened product-symbol
deleted-vertex decoder by reusing the existing local neighbor-code inverse. -/
theorem physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296_of_symbolicResidualParentSelector1296
    (hselector : PhysicalPlaquetteGraphSymbolicResidualParentSelector1296) :
    PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  obtain ⟨parent, code, hinj, hcover⟩ := hselector root k
  refine ⟨fun residual symbol =>
    match parent residual symbol.1 with
    | some p => physicalNeighborDecodeOfStepCode code p symbol.2
    | none => none, ?_⟩
  intro X hk hX
  obtain ⟨z, hzX, hz_ne_root, hresidual, parentSymbol, p, hparent,
    _hp_residual, hzp⟩ := hcover hk hX
  refine ⟨z, hzX, hz_ne_root, hresidual, (parentSymbol, code p z), ?_⟩
  dsimp
  rw [hparent]
  exact physicalNeighborDecodeOfStepCode_spec hinj hzp

/-- Any non-root deleted vertex in an anchored bucket has at least one parent in
the residual bucket.  This is the local frontier fact needed by the v2.67
invariant; it does not choose a canonical parent depending only on the
residual. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root z : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hzX : z ∈ X) (hz_ne_root : z ≠ root) :
    ∃ p, p ∈ X.erase z ∧
      z ∈ (plaquetteGraph d L).neighborFinset p := by
  have hroot : root ∈ X :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hX
  have hpre :
      ((plaquetteGraph d L).induce {x | x ∈ X}).Preconnected :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected hX
  obtain ⟨walk⟩ := hpre ⟨z, hzX⟩ ⟨root, hroot⟩
  have hne :
      (⟨z, hzX⟩ : {x : ConcretePlaquette d L // x ∈ X}) ≠
        ⟨root, hroot⟩ := by
    intro h
    exact hz_ne_root (congrArg Subtype.val h)
  obtain ⟨p, hpAdjInd⟩ :=
    simpleGraph_walk_exists_adj_start_of_ne walk hne
  have hpAdj : (plaquetteGraph d L).Adj z p.1 :=
    SimpleGraph.induce_adj.mp hpAdjInd
  have hp_ne_z : p.1 ≠ z :=
    hpAdj.ne'
  have hp_erase : p.1 ∈ X.erase z := by
    simpa [Finset.mem_erase] using And.intro hp_ne_z p.2
  have hz_neighbor :
      z ∈ (plaquetteGraph d L).neighborFinset p.1 :=
    (SimpleGraph.mem_neighborFinset (plaquetteGraph d L) p.1 z).mpr hpAdj.symm
  exact ⟨p.1, hp_erase, hz_neighbor⟩

/-- Physical specialization: any non-root deleted physical plaquette has a
residual neighbor-parent. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
    {L k : ℕ} [NeZero L]
    {root z : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hzX : z ∈ X) (hz_ne_root : z ≠ root) :
    ∃ p, p ∈ X.erase z ∧
      z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p :=
  plaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
    (d := physicalClayDimension) (L := L) (k := k)
    (root := root) (z := z) (X := X) hX hzX hz_ne_root

/-- Member-targeted first BFS step: every non-root member of an anchored bucket
is reached through some plaquette in the root shell. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset_to_member
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root y : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hy : y ∈ X) (hyne : root ≠ y) :
    ∃ z, z ∈ X ∧ z ∈ (plaquetteGraph d L).neighborFinset root := by
  have hroot : root ∈ X :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hX
  have hpre :
      ((plaquetteGraph d L).induce {x | x ∈ X}).Preconnected :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected hX
  obtain ⟨p⟩ := hpre ⟨root, hroot⟩ ⟨y, hy⟩
  have hne :
      (⟨root, hroot⟩ : {x : ConcretePlaquette d L // x ∈ X}) ≠
        ⟨y, hy⟩ := by
    intro h
    exact hyne (congrArg Subtype.val h)
  obtain ⟨z, hz⟩ := simpleGraph_walk_exists_adj_start_of_ne p hne
  have hzAdj : (plaquetteGraph d L).Adj root z.1 :=
    SimpleGraph.induce_adj.mp hz
  exact ⟨z.1, z.2,
    (SimpleGraph.mem_neighborFinset (plaquetteGraph d L) root z.1).mpr hzAdj⟩

/-- Member-targeted first BFS step with residual tail: every non-root member
of an anchored bucket is reached through a root-shell plaquette, and the
induced walk from that plaquette to the target member stays inside the bucket. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset_tail_to_member
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root y : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hy : y ∈ X) (hyne : root ≠ y) :
    ∃ z : {x : ConcretePlaquette d L // x ∈ X},
      ∃ _tail : ((plaquetteGraph d L).induce {x | x ∈ X}).Walk z ⟨y, hy⟩,
        z.1 ∈ (plaquetteGraph d L).neighborFinset root := by
  have hroot : root ∈ X :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hX
  have hpre :
      ((plaquetteGraph d L).induce {x | x ∈ X}).Preconnected :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected hX
  obtain ⟨p⟩ := hpre ⟨root, hroot⟩ ⟨y, hy⟩
  have hne :
      (⟨root, hroot⟩ : {x : ConcretePlaquette d L // x ∈ X}) ≠
        ⟨y, hy⟩ := by
    intro h
    exact hyne (congrArg Subtype.val h)
  obtain ⟨z, hzAdjInd, htail, _⟩ :=
    simpleGraph_walk_exists_adj_start_and_tail_of_ne p hne
  have hzAdj : (plaquetteGraph d L).Adj root z.1 :=
    SimpleGraph.induce_adj.mp hzAdjInd
  exact ⟨z, htail,
    (SimpleGraph.mem_neighborFinset (plaquetteGraph d L) root z.1).mpr hzAdj⟩

/-- Physical member-targeted first-shell code: every non-root member of an
anchored bucket has at least one coded first branch from the root shell. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_to_member
    {L k : ℕ} [NeZero L]
    {root y : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hy : y ∈ X) (hyne : root ≠ y) :
    ∃ c : Fin 1296,
      ∃ z : {z : ConcretePlaquette physicalClayDimension L //
        z ∈ X ∩ (plaquetteGraph physicalClayDimension L).neighborFinset root},
        physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296 hX z = c := by
  obtain ⟨z, hzX, hzN⟩ :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset_to_member
      hX hy hyne
  have hzShell : z ∈ X ∩ (plaquetteGraph physicalClayDimension L).neighborFinset root := by
    simp [hzX, hzN]
  exact ⟨physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296 hX
      ⟨z, hzShell⟩,
    ⟨⟨z, hzShell⟩, rfl⟩⟩

/-- Physical member-targeted coded first BFS step with residual tail.  This
packages the first `Fin 1296` branch together with the remaining induced walk
from that branch to the target member. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_tail_to_member
    {L k : ℕ} [NeZero L]
    {root y : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hy : y ∈ X) (hyne : root ≠ y) :
    ∃ c : Fin 1296,
      ∃ z : {z : ConcretePlaquette physicalClayDimension L //
        z ∈ X ∩ (plaquetteGraph physicalClayDimension L).neighborFinset root},
        ∃ _tail :
          ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ X}).Walk
            ⟨z.1, (Finset.mem_inter.mp z.2).1⟩ ⟨y, hy⟩,
          physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296 hX z = c := by
  obtain ⟨z, htail, hzN⟩ :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset_tail_to_member
      hX hy hyne
  have hzShell :
      z.1 ∈ X ∩ (plaquetteGraph physicalClayDimension L).neighborFinset root := by
    simp [z.2, hzN]
  let zShell : {z : ConcretePlaquette physicalClayDimension L //
      z ∈ X ∩ (plaquetteGraph physicalClayDimension L).neighborFinset root} :=
    ⟨z.1, hzShell⟩
  have htail' :
      ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ X}).Walk
        ⟨zShell.1, (Finset.mem_inter.mp zShell.2).1⟩ ⟨y, hy⟩ := by
    simpa [zShell] using htail
  exact ⟨physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296 hX
      zShell,
    zShell, htail', rfl⟩

/-- Reachability API for the member-targeted first BFS branch: every non-root
member is reachable from some root-shell plaquette inside the induced bucket
graph. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset_reachable_to_member
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root y : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hy : y ∈ X) (hyne : root ≠ y) :
    ∃ z : {x : ConcretePlaquette d L // x ∈ X},
      z.1 ∈ (plaquetteGraph d L).neighborFinset root ∧
        ((plaquetteGraph d L).induce {x | x ∈ X}).Reachable z ⟨y, hy⟩ := by
  obtain ⟨z, tail, hzN⟩ :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset_tail_to_member
      hX hy hyne
  exact ⟨z, hzN, ⟨tail⟩⟩

/-- Physical coded reachability API for the member-targeted first BFS branch:
every non-root member is reachable from a `Fin 1296`-coded root-shell
plaquette inside the induced bucket graph. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_reachable_to_member
    {L k : ℕ} [NeZero L]
    {root y : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hy : y ∈ X) (hyne : root ≠ y) :
    ∃ c : Fin 1296,
      ∃ z : {z : ConcretePlaquette physicalClayDimension L //
        z ∈ X ∩ (plaquetteGraph physicalClayDimension L).neighborFinset root},
        ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ X}).Reachable
          ⟨z.1, (Finset.mem_inter.mp z.2).1⟩ ⟨y, hy⟩ ∧
          physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296 hX z = c := by
  obtain ⟨c, z, tail, hcode⟩ :=
    physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_tail_to_member
      hX hy hyne
  exact ⟨c, z, ⟨⟨tail⟩, hcode⟩⟩

/-- Canonical first-shell parent code for a non-root member of a physical
anchored bucket.  This turns the previous existential first-branch theorem
into a functional parent-map API, which is the form needed by a recursive
BFS/Klarner decoder. -/
noncomputable def physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (y : {y : ConcretePlaquette physicalClayDimension L // y ∈ X ∧ root ≠ y}) :
    Fin 1296 :=
  Classical.choose
    (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_reachable_to_member
      hX y.2.1 y.2.2)

/-- Canonical first-shell parent for a non-root member of a physical anchored
bucket.  The parent lies in the root shell `X ∩ neighborFinset root`. -/
noncomputable def physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (y : {y : ConcretePlaquette physicalClayDimension L // y ∈ X ∧ root ≠ y}) :
    {z : ConcretePlaquette physicalClayDimension L //
      z ∈ X ∩ (plaquetteGraph physicalClayDimension L).neighborFinset root} :=
  Classical.choose
    (Classical.choose_spec
      (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_reachable_to_member
        hX y.2.1 y.2.2))

/-- The canonical first-shell parent reaches the target member inside the
bucket-induced graph. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (y : {y : ConcretePlaquette physicalClayDimension L // y ∈ X ∧ root ≠ y}) :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ X}).Reachable
      ⟨(physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296
          hX y).1,
        (Finset.mem_inter.mp
          (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296
            hX y).2).1⟩
      ⟨y.1, y.2.1⟩ := by
  let h :=
    physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_reachable_to_member
      hX y.2.1 y.2.2
  exact (Classical.choose_spec (Classical.choose_spec h)).1

/-- The canonical first-shell parent has exactly the canonical parent code.
This is the code-stability equation needed when the parent map is iterated into
full bucket words. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296_spec
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (y : {y : ConcretePlaquette physicalClayDimension L // y ∈ X ∧ root ≠ y}) :
    physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296 hX
      (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296
        hX y) =
      physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296
        hX y := by
  let h :=
    physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_reachable_to_member
      hX y.2.1 y.2.2
  exact (Classical.choose_spec (Classical.choose_spec h)).2

/-- Any nontrivial anchored bucket has a first root-neighbor symbol in any
available neighbor-choice alphabet. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborCode
    {d D L k : ℕ} [NeZero d] [NeZero L]
    (hchoice : PlaquetteNeighborChoiceCodeBoundDim d D)
    {root : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hk : 1 < k) :
    ∃ c : Fin D, ∃ z, ∃ hzX : z ∈ X,
      ∃ hzN : z ∈ (plaquetteGraph d L).neighborFinset root,
        Classical.choose (hchoice root) ⟨z, hzN⟩ = c := by
  obtain ⟨z, hzX, hzN⟩ :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset hX hk
  exact ⟨Classical.choose (hchoice root) ⟨z, hzN⟩, z, hzX, hzN, rfl⟩

/-- Physical four-dimensional version: a nontrivial anchored bucket has a first
root-neighbor symbol in the current `1296`-letter alphabet. -/
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborCode1296
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (hk : 1 < k) :
    ∃ c : Fin 1296, ∃ z, ∃ hzX : z ∈ X,
      ∃ hzN : z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset root,
        Classical.choose (plaquetteNeighborChoiceCodeBoundDim_physical_ternary root)
          ⟨z, hzN⟩ = c :=
  plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborCode
    plaquetteNeighborChoiceCodeBoundDim_physical_ternary hX hk

/-- The anchored graph-animal bucket of size zero is empty, because every
bucket element must contain the root. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_eq_empty
    {d L : ℕ} [NeZero d] [NeZero L]
    (root : ConcretePlaquette d L) :
    plaquetteGraphPreconnectedSubsetsAnchoredCard d L root 0 = ∅ := by
  ext X
  constructor
  · intro hX
    unfold plaquetteGraphPreconnectedSubsetsAnchoredCard at hX
    rw [Finset.mem_filter] at hX
    have hroot : root ∈ X := hX.2.1
    have hX_empty : X = ∅ := Finset.card_eq_zero.mp hX.2.2.1
    have hroot_not : root ∉ X := by
      simp [hX_empty]
    exact False.elim (hroot_not hroot)
  · intro hX
    simp at hX

/-- The anchored graph-animal bucket of size one is contained in the singleton
bucket containing only `{root}`. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_one_subset_singleton
    {d L : ℕ} [NeZero d] [NeZero L]
    (root : ConcretePlaquette d L) :
    plaquetteGraphPreconnectedSubsetsAnchoredCard d L root 1 ⊆
      ({({root} : Finset (ConcretePlaquette d L))} :
        Finset (Finset (ConcretePlaquette d L))) := by
  intro X hX
  unfold plaquetteGraphPreconnectedSubsetsAnchoredCard at hX
  rw [Finset.mem_filter] at hX
  rw [Finset.mem_singleton]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hX.2.2.1
  have hroot_mem_singleton : root ∈ ({a} : Finset (ConcretePlaquette d L)) := by
    simpa [ha] using hX.2.1
  have hroot_eq_a : root = a := by
    simpa using hroot_mem_singleton
  simpa [ha, hroot_eq_a]

/-- The anchored graph-animal bucket of size one has cardinality at most one. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_one_card_le_one
    {d L : ℕ} [NeZero d] [NeZero L]
    (root : ConcretePlaquette d L) :
    (plaquetteGraphPreconnectedSubsetsAnchoredCard d L root 1).card ≤ 1 := by
  simpa using
    Finset.card_le_card
      (plaquetteGraphPreconnectedSubsetsAnchoredCard_one_subset_singleton root)

/-- Size-zero anchored graph-animal buckets satisfy the target exponential
count inequality for every growth constant. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_card_le_pow
    {d L : ℕ} [NeZero d] [NeZero L]
    (root : ConcretePlaquette d L) (K : ℕ) :
    (plaquetteGraphPreconnectedSubsetsAnchoredCard d L root 0).card ≤ K ^ 0 := by
  rw [plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_eq_empty root]
  simp

/-- Size-one anchored graph-animal buckets satisfy the target exponential count
inequality for every growth constant `K ≥ 1`. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_one_card_le_pow
    {d L : ℕ} [NeZero d] [NeZero L]
    (root : ConcretePlaquette d L) {K : ℕ} (hK : 1 ≤ K) :
    (plaquetteGraphPreconnectedSubsetsAnchoredCard d L root 1).card ≤ K ^ 1 := by
  exact (plaquetteGraphPreconnectedSubsetsAnchoredCard_one_card_le_one root).trans
    (by simpa using hK)

/-- Uniform base dispatcher for the anchored graph-animal count target at
sizes `k ≤ 1`. The positive-size case needs only the eventual growth constant
lower bound `K ≥ 1`. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_base_card_le_pow
    {d L : ℕ} [NeZero d] [NeZero L]
    (root : ConcretePlaquette d L) {K k : ℕ} (hK : 1 ≤ K) (hk : k ≤ 1) :
    (plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k).card ≤ K ^ k := by
  cases k with
  | zero =>
      exact plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_card_le_pow root K
  | succ k =>
      cases k with
      | zero =>
          simpa using
            (plaquetteGraphPreconnectedSubsetsAnchoredCard_one_card_le_pow
              root (K := K) hK)
      | succ k =>
          omega

/-- In physical dimension, every plaquette has a distinct plaquette at the same
site, obtained by changing the orientation when necessary. -/
theorem physicalPlaquetteGraph_root_has_distinct_plaquette :
    PhysicalPlaquetteGraphRootHasDistinctPlaquette := by
  intro L _ root
  let d0 : Fin physicalClayDimension :=
    ⟨0, by norm_num [physicalClayDimension]⟩
  let d1 : Fin physicalClayDimension :=
    ⟨1, by norm_num [physicalClayDimension]⟩
  let d2 : Fin physicalClayDimension :=
    ⟨2, by norm_num [physicalClayDimension]⟩
  let p01 : ConcretePlaquette physicalClayDimension L :=
    ⟨root.site, d0, d1, by
      rw [Fin.lt_def]
      norm_num [d0, d1]⟩
  let p02 : ConcretePlaquette physicalClayDimension L :=
    ⟨root.site, d0, d2, by
      rw [Fin.lt_def]
      norm_num [d0, d2]⟩
  have hp01_ne_p02 : p01 ≠ p02 := by
    intro hp
    have hdir :
        (ConcretePlaquette.dir2 p01).val =
          (ConcretePlaquette.dir2 p02).val := by
      simpa using congrArg (fun q : ConcretePlaquette physicalClayDimension L => q.dir2.val) hp
    norm_num [p01, p02, d1, d2] at hdir
  by_cases hroot : root = p01
  · refine ⟨p02, ?_⟩
    intro hp02
    exact hp01_ne_p02 (hroot.symm.trans hp02.symm)
  · refine ⟨p01, ?_⟩
    intro hp01
    exact hroot hp01.symm

/-- Low-cardinality totalization for the base-aware bookkeeping interface.
For `k = 0` the family is empty; for `k = 1` every anchored bucket is `{root}`,
so a non-root fallback deletion leaves `root` in the residual. -/
theorem physicalPlaquetteGraph_baseAwareLowCardBookkeepingTotalization1296 :
    PhysicalPlaquetteGraphBaseAwareLowCardBookkeepingTotalization1296 := by
  classical
  intro L hL root k hk
  letI : NeZero L := hL
  obtain ⟨fallbackDeleted, hfallback_ne⟩ :=
    physicalPlaquetteGraph_root_has_distinct_plaquette (root := root)
  let deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L :=
    fun _ => fallbackDeleted
  let parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L :=
    fun _ => root
  let essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L) :=
    fun residual =>
      ((plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k).filter
        (fun X => X.erase (deleted X) = residual)).image parentOf
  have hparent_mem :
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)},
        X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k →
        parentOf X ∈ X.erase (deleted X) := by
    intro X hX
    cases k with
    | zero =>
        rw [plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_eq_empty root] at hX
        simp at hX
    | succ k =>
        cases k with
        | zero =>
            have hX_singleton :
                X ∈ ({ {root} } :
                  Finset (Finset (ConcretePlaquette physicalClayDimension L))) :=
              plaquetteGraphPreconnectedSubsetsAnchoredCard_one_subset_singleton
                root hX
            rw [Finset.mem_singleton] at hX_singleton
            subst X
            simp [deleted, parentOf, hfallback_ne]
        | succ k =>
            omega
  refine ⟨fallbackDeleted, hfallback_ne, deleted, parentOf, essential, ?_, hparent_mem, ?_, ?_⟩
  · intro X
    exact ⟨rfl, rfl⟩
  · intro residual
    rfl
  · intro residual p hp
    dsimp [essential] at hp
    rcases Finset.mem_image.mp hp with ⟨X, hX, rfl⟩
    rw [Finset.mem_filter] at hX
    simpa [hX.2] using hparent_mem hX.1

/-- Base-aware bookkeeping follows by combining the proved low-cardinality
totalization with the existing safe-deletion and residual-parent APIs. -/
theorem physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296 :
    PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296 := by
  classical
  intro L hL root k
  letI : NeZero L := hL
  by_cases hk_low : k ≤ 1
  · obtain ⟨_fallbackDeleted, _hfallback_ne, deleted, parentOf, essential,
      _hdefault, _hparent_mem, himage, hessential_subset⟩ :=
        physicalPlaquetteGraph_baseAwareLowCardBookkeepingTotalization1296
          (root := root) (k := k) hk_low
    refine ⟨deleted, parentOf, essential, ?_, himage, hessential_subset⟩
    intro X hk hX
    omega
  · have hk_high : 2 ≤ k := by omega
    let family : Finset (Finset (ConcretePlaquette physicalClayDimension L)) :=
      plaquetteGraphPreconnectedSubsetsAnchoredCard physicalClayDimension L root k
    have hdelExists :
        ∀ X : Finset (ConcretePlaquette physicalClayDimension L),
          X ∈ family →
          ∃ z, ∃ hzX : z ∈ X, z ≠ root ∧
            X.erase z ∈
              plaquetteGraphPreconnectedSubsetsAnchoredCard
                physicalClayDimension L root (k - 1) := by
      intro X hX
      exact
        physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem
          (L := L) (k := k) (root := root) (X := X) hk_high hX
    let deleted :
        Finset (ConcretePlaquette physicalClayDimension L) →
          ConcretePlaquette physicalClayDimension L :=
      fun X =>
        if hX : X ∈ family then
          Classical.choose (hdelExists X hX)
        else
          root
    have hdeleted_spec :
        ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)},
          (hX : X ∈ family) →
          deleted X ∈ X ∧
            deleted X ≠ root ∧
            X.erase (deleted X) ∈
              plaquetteGraphPreconnectedSubsetsAnchoredCard
                physicalClayDimension L root (k - 1) := by
      intro X hX
      dsimp [deleted]
      rw [dif_pos hX]
      obtain ⟨hzX, hz_ne_root, hresidual⟩ :=
        Classical.choose_spec (hdelExists X hX)
      exact ⟨hzX, hz_ne_root, hresidual⟩
    have hparentExists :
        ∀ X : Finset (ConcretePlaquette physicalClayDimension L),
          (hX : X ∈ family) →
          ∃ p, p ∈ X.erase (deleted X) ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset p := by
      intro X hX
      have hdel := hdeleted_spec hX
      exact
        physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
          (L := L) (k := k) (root := root) (z := deleted X) (X := X)
          hX hdel.1 hdel.2.1
    let parentOf :
        Finset (ConcretePlaquette physicalClayDimension L) →
          ConcretePlaquette physicalClayDimension L :=
      fun X =>
        if hX : X ∈ family then
          Classical.choose (hparentExists X hX)
        else
          root
    have hparent_spec :
        ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)},
          (hX : X ∈ family) →
          parentOf X ∈ X.erase (deleted X) ∧
            deleted X ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X) := by
      intro X hX
      simpa [parentOf, hX] using
        (Classical.choose_spec (hparentExists X hX))
    let essential :
        Finset (ConcretePlaquette physicalClayDimension L) →
          Finset (ConcretePlaquette physicalClayDimension L) :=
      fun residual =>
        (family.filter (fun X => X.erase (deleted X) = residual)).image parentOf
    refine ⟨deleted, parentOf, essential, ?_, ?_, ?_⟩
    · intro X hk hX
      have hdel := hdeleted_spec (X := X) hX
      have hparent := hparent_spec (X := X) hX
      have hparent_essential :
          parentOf X ∈ essential (X.erase (deleted X)) := by
        dsimp [essential]
        exact Finset.mem_image.mpr ⟨X, by simp [family, hX], rfl⟩
      refine ⟨hdel.1, hdel.2.1, hdel.2.2, hparent.1, hparent_essential, ?_⟩
      by_cases hcard :
          (X.erase (deleted X)).card = 1
      · have hroot_residual :
            root ∈ X.erase (deleted X) :=
          plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem hdel.2.2
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
        have hparent_mem_singleton :
            parentOf X ∈ ({a} :
              Finset (ConcretePlaquette physicalClayDimension L)) := by
          simpa [ha] using hparent.1
        have hroot_mem_singleton :
            root ∈ ({a} :
              Finset (ConcretePlaquette physicalClayDimension L)) := by
          simpa [ha] using hroot_residual
        have hparent_eq_a : parentOf X = a := by
          simpa using hparent_mem_singleton
        have hroot_eq_a : root = a := by
          simpa using hroot_mem_singleton
        have hparent_root : parentOf X = root :=
          hparent_eq_a.trans hroot_eq_a.symm
        exact Or.inl ⟨hcard, hparent_root, by simpa [hparent_root] using hparent.2⟩
      · exact Or.inr ⟨hcard, hparent.2⟩
    · intro residual
      rfl
    · intro residual p hp
      dsimp [essential] at hp
      rcases Finset.mem_image.mp hp with ⟨X, hX, rfl⟩
      rw [Finset.mem_filter] at hX
      simpa [hX.2] using (hparent_spec (X := X) hX.1).1

/-- An explicit `1296`-bounded selected terminal-predecessor menu packs into an
injective `Fin 1296` code.

All domination and residual-path facts are inputs; this theorem proves only the
finite coding step and does not assert that arbitrary residual/essential data is
dominated. -/
theorem physicalPlaquetteGraph_residualDominatedTerminalPredecessorPacking1296 :
    PhysicalPlaquetteGraphResidualDominatedTerminalPredecessorPacking1296 := by
  classical
  intro L hL residual essential terminalPredMenu terminalPredOfParent
    _hessential_subset _hmenu_subset _hmenu_image _hpred_mem_menu
    _hlastEdge _hpath hcard
  letI : NeZero L := hL
  exact ⟨finsetCodeOfCardLe terminalPredMenu hcard,
    finsetCodeOfCardLe_injective terminalPredMenu hcard⟩

/-- The empty anchored bucket has a vacuous word decoder. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_wordDecoderCovers
    {d L K : ℕ} [NeZero d] [NeZero L]
    (root : ConcretePlaquette d L) :
    ∃ decode : (Fin 0 → Fin K) → Finset (ConcretePlaquette d L),
      ∀ X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root 0,
        ∃ word : Fin 0 → Fin K, decode word = X := by
  refine ⟨fun _ => ∅, ?_⟩
  intro X hX
  rw [plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_eq_empty root] at hX
  simp at hX

/-- The size-one anchored bucket is covered by the constant singleton decoder,
provided the alphabet has at least one symbol. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_one_wordDecoderCovers
    {d L K : ℕ} [NeZero d] [NeZero L]
    (root : ConcretePlaquette d L) (hK : 1 ≤ K) :
    ∃ decode : (Fin 1 → Fin K) → Finset (ConcretePlaquette d L),
      ∀ X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root 1,
        ∃ word : Fin 1 → Fin K, decode word = X := by
  refine ⟨fun _ => {root}, ?_⟩
  intro X hX
  have hX_singleton :
      X ∈ ({ {root} } : Finset (Finset (ConcretePlaquette d L))) :=
    plaquetteGraphPreconnectedSubsetsAnchoredCard_one_subset_singleton root hX
  rw [Finset.mem_singleton] at hX_singleton
  subst X
  exact ⟨fun _ => ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hK⟩, rfl⟩

/-- Uniform base dispatcher for anchored word-decoder coverage at sizes
`k ≤ 1`. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_base_wordDecoderCovers
    {d L K : ℕ} [NeZero d] [NeZero L]
    (root : ConcretePlaquette d L) {k : ℕ} (hK : 1 ≤ K) (hk : k ≤ 1) :
    ∃ decode : (Fin k → Fin K) → Finset (ConcretePlaquette d L),
      ∀ X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k,
        ∃ word : Fin k → Fin K, decode word = X := by
  cases k with
  | zero =>
      exact plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_wordDecoderCovers
        (K := K) root
  | succ k =>
      cases k with
      | zero =>
          simpa using
            (plaquetteGraphPreconnectedSubsetsAnchoredCard_one_wordDecoderCovers
              root hK)
      | succ k =>
          omega

/-- In an anchored preconnected bucket, every plaquette in the bucket is
reachable from the root inside the induced graph on that same bucket. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_root_reachable
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root y : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hy : y ∈ X) :
    ((plaquetteGraph d L).induce {x | x ∈ X}).Reachable
      ⟨root, by
        unfold plaquetteGraphPreconnectedSubsetsAnchoredCard at hX
        rw [Finset.mem_filter] at hX
        exact hX.2.1⟩
      ⟨y, hy⟩ := by
  unfold plaquetteGraphPreconnectedSubsetsAnchoredCard at hX
  rw [Finset.mem_filter] at hX
  exact hX.2.2.2 ⟨root, hX.2.1⟩ ⟨y, hy⟩

/-- Path-form version of root reachability inside an anchored bucket. This is
the local graph-theoretic ingredient used by BFS/Klarner enumerations. -/
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path
    {d L k : ℕ} [NeZero d] [NeZero L]
    {root y : ConcretePlaquette d L} {X : Finset (ConcretePlaquette d L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k)
    (hy : y ∈ X) :
    ∃ p : ((plaquetteGraph d L).induce {x | x ∈ X}).Walk
        ⟨root, by
          unfold plaquetteGraphPreconnectedSubsetsAnchoredCard at hX
          rw [Finset.mem_filter] at hX
          exact hX.2.1⟩
        ⟨y, hy⟩,
      p.IsPath :=
  (plaquetteGraphPreconnectedSubsetsAnchoredCard_root_reachable hX hy).exists_isPath

/-- Decoder-form anchored graph-animal target: every anchored bucket element is
covered by a word of length equal to its cardinality over an alphabet of size
`K`. This is the direct BFS/Klarner proof shape for the anchored count
frontier. -/
def PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound (K : ℕ) : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ decode : (Fin k → Fin K) → Finset (ConcretePlaquette physicalClayDimension L),
      ∀ X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k,
        ∃ word : Fin k → Fin K, decode word = X

/-- To prove the physical anchored word-decoder target, it is enough to prove
the nontrivial `1 < k` cases.  The `k = 0` and `k = 1` cases are discharged by
the base decoder lemmas above. -/
theorem PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound.of_nontrivial
    {K : ℕ} (hK : 1 ≤ K)
    (hlarge :
      ∀ {L : ℕ} [NeZero L]
        (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
        1 < k →
          ∃ decode : (Fin k → Fin K) →
              Finset (ConcretePlaquette physicalClayDimension L),
            ∀ X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
                physicalClayDimension L root k,
              ∃ word : Fin k → Fin K, decode word = X) :
    PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound K := by
  intro L _ root k
  by_cases hk : k ≤ 1
  · exact plaquetteGraphPreconnectedSubsetsAnchoredCard_base_wordDecoderCovers
      root hK hk
  · exact hlarge root k (by omega)

/-- Physical `1296` specialization of the nontrivial-case anchored decoder
frontier.  This pins the target alphabet used by the physical branching bound
and leaves only the `1 < k` recursive decoder cases as the remaining input. -/
theorem physicalPlaquetteGraphAnimalAnchoredWordDecoderBound1296_of_nontrivial
    (hlarge :
      ∀ {L : ℕ} [NeZero L]
        (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
        1 < k →
          ∃ decode : (Fin k → Fin 1296) →
              Finset (ConcretePlaquette physicalClayDimension L),
            ∀ X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
                physicalClayDimension L root k,
              ∃ word : Fin k → Fin 1296, decode word = X) :
    PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound 1296 :=
  PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound.of_nontrivial
    (K := 1296) (by norm_num) hlarge

/-- The anchored word-decoder target is monotone in the alphabet size. -/
theorem PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound.mono
    {K K' : ℕ} (hdecode : PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound K)
    (hK : 1 ≤ K) (hKK' : K ≤ K') :
    PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound K' := by
  intro L _ root k
  obtain ⟨decode, hcover⟩ := hdecode root k
  let project : Fin K' → Fin K := fun a =>
    if h : a.val < K then ⟨a.val, h⟩ else ⟨0, hK⟩
  refine ⟨fun word' => decode (fun i => project (word' i)), ?_⟩
  intro X hX
  obtain ⟨word, hword⟩ := hcover X hX
  refine ⟨fun i => Fin.castLE hKK' (word i), ?_⟩
  dsimp [project]
  have hproj : (fun i : Fin k =>
      (if h : (Fin.castLE hKK' (word i)).val < K then
        ⟨(Fin.castLE hKK' (word i)).val, h⟩
      else ⟨0, hK⟩ : Fin K)) = word := by
    funext i
    simp [Fin.ext_iff]
  simpa [hproj] using hword

/-- Choose, for each anchored graph-animal bucket element, one word decoding to
it. -/
noncomputable def physicalPlaquetteGraphAnimalAnchoredWordCodeOfDecoder
    {K : ℕ} (hdecode : PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound K)
    {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ) :
    {X : Finset (ConcretePlaquette physicalClayDimension L) //
      X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k} →
      (Fin k → Fin K) :=
  let hcover := Classical.choose_spec (hdecode root k)
  fun X => Classical.choose (hcover X.1 X.2)

/-- The chosen word code from a covering anchored decoder is injective. -/
theorem physicalPlaquetteGraphAnimalAnchoredWordCodeOfDecoder_injective
    {K : ℕ} (hdecode : PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound K)
    {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ) :
    Function.Injective
      (physicalPlaquetteGraphAnimalAnchoredWordCodeOfDecoder hdecode root k) := by
  intro X Y h
  apply Subtype.ext
  let decode := Classical.choose (hdecode root k)
  let hcover := Classical.choose_spec (hdecode root k)
  have hX : decode (Classical.choose (hcover X.1 X.2)) = X.1 := by
    exact Classical.choose_spec (hcover X.1 X.2)
  have hY : decode (Classical.choose (hcover Y.1 Y.2)) = Y.1 := by
    exact Classical.choose_spec (hcover Y.1 Y.2)
  have hdec := congrArg decode h
  dsimp [physicalPlaquetteGraphAnimalAnchoredWordCodeOfDecoder] at hdec
  change decode (Classical.choose (hcover X.1 X.2)) =
    decode (Classical.choose (hcover Y.1 Y.2)) at hdec
  rw [hX, hY] at hdec
  exact hdec

/-- Physical anchored graph-animal count target.

This is the classical lattice-animal counting shape: the number of connected
plaquette subsets of cardinality `k` containing a fixed root is bounded by
`K^k`, uniformly in the volume. -/
def PhysicalPlaquetteGraphAnimalAnchoredCountBound (K : ℕ) : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    (plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k).card ≤ K ^ k

/-- A covering anchored word decoder gives the physical anchored graph-animal
count bound. -/
theorem physicalPlaquetteGraphAnimalAnchoredCountBound_of_wordDecoder
    {K : ℕ}
    (hdecode : PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound K) :
    PhysicalPlaquetteGraphAnimalAnchoredCountBound K := by
  intro L _ root k
  let S := plaquetteGraphPreconnectedSubsetsAnchoredCard
    physicalClayDimension L root k
  have hcard :
      Fintype.card {X : Finset (ConcretePlaquette physicalClayDimension L) //
          X ∈ S} ≤
        Fintype.card (Fin k → Fin K) :=
    Fintype.card_le_of_injective
      (physicalPlaquetteGraphAnimalAnchoredWordCodeOfDecoder hdecode root k)
      (physicalPlaquetteGraphAnimalAnchoredWordCodeOfDecoder_injective
        hdecode root k)
  simpa [S, Fintype.card_subtype, Fintype.card_fun] using hcard

/-- The anchored graph-animal count target is monotone in the exponential
growth constant. This lets the eventual combinatorial proof produce any
convenient explicit constant `K`, while downstream terminal packages may use a
larger constant if that is more ergonomic. -/
theorem PhysicalPlaquetteGraphAnimalAnchoredCountBound.mono
    {K K' : ℕ}
    (hbound : PhysicalPlaquetteGraphAnimalAnchoredCountBound K)
    (hKK' : K ≤ K') :
    PhysicalPlaquetteGraphAnimalAnchoredCountBound K' := by
  intro L _ root k
  exact (hbound root k).trans (Nat.pow_le_pow_left hKK' k)

/-- Every connecting-cluster bucket element is an anchored preconnected
plaquette-graph animal after forgetting the second marked plaquette. -/
theorem connectingCluster_filter_subset_preconnectedSubsetsAnchoredCard
    {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (k : ℕ) :
    ((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X => p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧ X.card = k)) ⊆
        plaquetteGraphPreconnectedSubsetsAnchoredCard d L p k := by
  intro X hX
  rw [Finset.mem_filter] at hX
  unfold plaquetteGraphPreconnectedSubsetsAnchoredCard
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ X,
    hX.2.1,
    hX.2.2.2.2,
    polymerConnected_plaquetteGraph_induce_preconnected hX.2.2.2.1⟩

/-- The shifted connecting-cluster bucket is bounded by the corresponding
anchored graph-animal bucket. -/
theorem connectingCluster_filter_card_le_preconnectedSubsetsAnchoredCard
    {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ) :
    ((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card ≤
        (plaquetteGraphPreconnectedSubsetsAnchoredCard d L p
          (n + ⌈siteLatticeDist p.site q.site⌉₊)).card := by
  exact Finset.card_le_card
    (connectingCluster_filter_subset_preconnectedSubsetsAnchoredCard p q
      (n + ⌈siteLatticeDist p.site q.site⌉₊))

/-- Shifted graph-animal bucket with both marked plaquettes retained.  This is
the exact graph-theoretic count shape needed for the exponential F3 count
frontier. -/
noncomputable def plaquetteGraphPreconnectedConnectingSubsetsShifted
    (L : ℕ) [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    Finset (Finset (ConcretePlaquette physicalClayDimension L)) :=
  (Finset.univ.filter fun X =>
    p ∈ X ∧ q ∈ X ∧
      X.card = n + ⌈siteLatticeDist p.site q.site⌉₊ ∧
      ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ X}).Preconnected)

/-- The two-marked shifted graph-animal bucket is contained in the anchored
graph-animal bucket obtained by forgetting the second marked plaquette. -/
theorem plaquetteGraphPreconnectedConnectingSubsetsShifted_subset_anchored
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n ⊆
      plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L p
        (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
  intro X hX
  unfold plaquetteGraphPreconnectedConnectingSubsetsShifted at hX
  unfold plaquetteGraphPreconnectedSubsetsAnchoredCard
  rw [Finset.mem_filter] at hX ⊢
  exact ⟨Finset.mem_univ X,
    hX.2.1,
    hX.2.2.2.1,
    hX.2.2.2.2⟩

/-- Cardinality reduction from the two-marked shifted graph-animal bucket to
the anchored graph-animal bucket. -/
theorem plaquetteGraphPreconnectedConnectingSubsetsShifted_card_le_anchored
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    (plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n).card ≤
      (plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L p
        (n + ⌈siteLatticeDist p.site q.site⌉₊)).card := by
  exact Finset.card_le_card
    (plaquetteGraphPreconnectedConnectingSubsetsShifted_subset_anchored
      p q n)

/-- The physical shifted polymer bucket is contained in the corresponding
shifted graph-animal bucket. -/
theorem physical_connectingCluster_filter_subset_graphAnimalShifted
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    ((Finset.univ : Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)) ⊆
        plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n := by
  intro X hX
  rw [Finset.mem_filter] at hX
  unfold plaquetteGraphPreconnectedConnectingSubsetsShifted
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ X,
    hX.2.1,
    hX.2.2.1,
    hX.2.2.2.2,
    polymerConnected_plaquetteGraph_induce_preconnected hX.2.2.2.1⟩

/-- Cardinality reduction from the physical shifted polymer bucket to the
shifted graph-animal bucket. -/
theorem physical_connectingCluster_filter_card_le_graphAnimalShifted
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    ((Finset.univ : Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card ≤
        (plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n).card := by
  exact Finset.card_le_card
    (physical_connectingCluster_filter_subset_graphAnimalShifted p q n)

/-- Pure graph-animal form of the remaining physical F3-count estimate. -/
def PhysicalConnectingClusterGraphAnimalShiftedCountBound (K : ℕ) : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ),
    (plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n).card ≤ K ^ n

/-- Decoder-form graph-animal target: every shifted graph-animal bucket is in
the image of a length-`n` word decoder over an alphabet of size `K`. -/
def PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound (K : ℕ) : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ),
    ∃ decode : (Fin n → Fin K) → Finset (ConcretePlaquette physicalClayDimension L),
      ∀ X ∈ plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n,
        ∃ word : Fin n → Fin K, decode word = X

/-- Choose, for each shifted graph-animal bucket element, one word decoding to
it. -/
noncomputable def physicalGraphAnimalShiftedWordCodeOfDecoder
    {K : ℕ} (hdecode :
      PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound K)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    {X : Finset (ConcretePlaquette physicalClayDimension L) //
      X ∈ plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n} →
      (Fin n → Fin K) :=
  let hcover := Classical.choose_spec (hdecode p q n)
  fun X => Classical.choose (hcover X.1 X.2)

/-- The chosen word code from a covering graph-animal decoder is injective. -/
theorem physicalGraphAnimalShiftedWordCodeOfDecoder_injective
    {K : ℕ} (hdecode :
      PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound K)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    Function.Injective
      (physicalGraphAnimalShiftedWordCodeOfDecoder hdecode p q n) := by
  intro X Y h
  apply Subtype.ext
  let decode := Classical.choose (hdecode p q n)
  let hcover := Classical.choose_spec (hdecode p q n)
  have hX : decode (Classical.choose (hcover X.1 X.2)) = X.1 := by
    exact Classical.choose_spec (hcover X.1 X.2)
  have hY : decode (Classical.choose (hcover Y.1 Y.2)) = Y.1 := by
    exact Classical.choose_spec (hcover Y.1 Y.2)
  have hdec := congrArg decode h
  dsimp [physicalGraphAnimalShiftedWordCodeOfDecoder] at hdec
  change decode (Classical.choose (hcover X.1 X.2)) =
    decode (Classical.choose (hcover Y.1 Y.2)) at hdec
  rw [hX, hY] at hdec
  exact hdec

/-- A graph-animal word decoder gives the exact `K^n` graph-animal count
bound. -/
theorem physicalGraphAnimalShiftedCountBound_of_wordDecoder
    {K : ℕ}
    (hdecode : PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound K) :
    PhysicalConnectingClusterGraphAnimalShiftedCountBound K := by
  intro L _ p q n
  let S := plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n
  have hcard :
      Fintype.card {X : Finset (ConcretePlaquette physicalClayDimension L) //
          X ∈ S} ≤
        Fintype.card (Fin n → Fin K) :=
    Fintype.card_le_of_injective
      (physicalGraphAnimalShiftedWordCodeOfDecoder hdecode p q n)
      (physicalGraphAnimalShiftedWordCodeOfDecoder_injective hdecode p q n)
  simpa [S, Fintype.card_subtype, Fintype.card_fun] using hcard

/-- Audit canary for the exact shifted graph-animal target: at `n = 0`, the
bound forces the minimal connecting graph-animal bucket to have cardinality at
most one.  This records why the raw `K^n` shifted target is much stronger than
the usual total-size lattice-animal count when several minimal connectors can
exist. -/
theorem physicalGraphAnimalShiftedCountBound_zero_card_le_one
    {K : ℕ}
    (hgraph : PhysicalConnectingClusterGraphAnimalShiftedCountBound K)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) :
    (plaquetteGraphPreconnectedConnectingSubsetsShifted L p q 0).card ≤ 1 := by
  simpa using hgraph p q 0

/-! ### Total-size graph-animal word-decoder target -/

/-- Total-size decoder-form graph-animal target: every shifted graph-animal
bucket is covered by words whose length is the full cardinality
`n + ⌈dist(p,q)⌉₊`.  This is the direct BFS/Klarner counting shape before the
distance factor is absorbed into the analytic decay. -/
def PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound (K : ℕ) : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ),
    ∃ decode :
      (Fin (n + ⌈siteLatticeDist p.site q.site⌉₊) → Fin K) →
        Finset (ConcretePlaquette physicalClayDimension L),
      ∀ X ∈ plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n,
        ∃ word : Fin (n + ⌈siteLatticeDist p.site q.site⌉₊) → Fin K,
          decode word = X

/-- Choose, for each shifted graph-animal bucket element, one total-size word
decoding to it. -/
noncomputable def physicalGraphAnimalTotalWordCodeOfDecoder
    {K : ℕ} (hdecode :
      PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound K)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    {X : Finset (ConcretePlaquette physicalClayDimension L) //
      X ∈ plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n} →
      (Fin (n + ⌈siteLatticeDist p.site q.site⌉₊) → Fin K) :=
  let hcover := Classical.choose_spec (hdecode p q n)
  fun X => Classical.choose (hcover X.1 X.2)

/-- The chosen total-size word code from a covering decoder is injective. -/
theorem physicalGraphAnimalTotalWordCodeOfDecoder_injective
    {K : ℕ} (hdecode :
      PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound K)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    Function.Injective
      (physicalGraphAnimalTotalWordCodeOfDecoder hdecode p q n) := by
  intro X Y h
  apply Subtype.ext
  let decode := Classical.choose (hdecode p q n)
  let hcover := Classical.choose_spec (hdecode p q n)
  have hX : decode (Classical.choose (hcover X.1 X.2)) = X.1 := by
    exact Classical.choose_spec (hcover X.1 X.2)
  have hY : decode (Classical.choose (hcover Y.1 Y.2)) = Y.1 := by
    exact Classical.choose_spec (hcover Y.1 Y.2)
  have hdec := congrArg decode h
  dsimp [physicalGraphAnimalTotalWordCodeOfDecoder] at hdec
  change decode (Classical.choose (hcover X.1 X.2)) =
    decode (Classical.choose (hcover Y.1 Y.2)) at hdec
  rw [hX, hY] at hdec
  exact hdec

/-- A total-size graph-animal word decoder gives the standard total-cardinality
`K^(n + ceil dist)` graph-animal count bound. -/
theorem physicalGraphAnimalTotalCountBound_of_wordDecoder
    {K : ℕ}
    (hdecode : PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound K)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    (plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n).card ≤
      K ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
  let S := plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n
  have hcard :
      Fintype.card {X : Finset (ConcretePlaquette physicalClayDimension L) //
          X ∈ S} ≤
        Fintype.card
          (Fin (n + ⌈siteLatticeDist p.site q.site⌉₊) → Fin K) :=
    Fintype.card_le_of_injective
      (physicalGraphAnimalTotalWordCodeOfDecoder hdecode p q n)
      (physicalGraphAnimalTotalWordCodeOfDecoder_injective hdecode p q n)
  simpa [S, Fintype.card_subtype, Fintype.card_fun] using hcard

/-- Direct total-size graph-animal count target.

This is the standard BFS/Klarner output shape: the shifted graph-animal bucket
is bounded by `K` to the full cardinality scale `n + ceil dist`. -/
def PhysicalConnectingClusterGraphAnimalTotalCountBound (K : ℕ) : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ),
    (plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n).card ≤
      K ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)

/-- The direct total-size graph-animal count target is monotone in the
exponential growth constant. -/
theorem PhysicalConnectingClusterGraphAnimalTotalCountBound.mono
    {K K' : ℕ}
    (hbound : PhysicalConnectingClusterGraphAnimalTotalCountBound K)
    (hKK' : K ≤ K') :
    PhysicalConnectingClusterGraphAnimalTotalCountBound K' := by
  intro L _ p q n
  exact (hbound p q n).trans
    (Nat.pow_le_pow_left hKK' (n + ⌈siteLatticeDist p.site q.site⌉₊))

/-- An anchored graph-animal count bound gives the direct total-size
two-marked graph-animal count target. -/
theorem physicalGraphAnimalTotalCountBound_of_anchoredCountBound
    {K : ℕ}
    (hanchored : PhysicalPlaquetteGraphAnimalAnchoredCountBound K) :
    PhysicalConnectingClusterGraphAnimalTotalCountBound K := by
  intro L _ p q n
  exact
    (plaquetteGraphPreconnectedConnectingSubsetsShifted_card_le_anchored
      p q n).trans
      (hanchored p (n + ⌈siteLatticeDist p.site q.site⌉₊))

/-- A total-size word decoder gives the direct graph-animal count target. -/
theorem physicalGraphAnimalTotalCountBound_of_totalWordDecoder
    {K : ℕ}
    (hdecode : PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound K) :
    PhysicalConnectingClusterGraphAnimalTotalCountBound K := by
  intro L _ p q n
  exact physicalGraphAnimalTotalCountBound_of_wordDecoder hdecode p q n

/-- Physical total-size graph-animal word-decoder target at the current `1296`
alphabet constant. -/
abbrev PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound1296 : Prop :=
  PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound 1296

/-- Physical total-size graph-animal count target at the current `1296`
alphabet constant. -/
abbrev PhysicalConnectingClusterGraphAnimalTotalCountBound1296 : Prop :=
  PhysicalConnectingClusterGraphAnimalTotalCountBound 1296

/-- Physical anchored graph-animal count target at the current `1296`
alphabet constant. -/
abbrev PhysicalPlaquetteGraphAnimalAnchoredCountBound1296 : Prop :=
  PhysicalPlaquetteGraphAnimalAnchoredCountBound 1296

/-- A physical `1296` anchored graph-animal count bound gives the direct
two-marked total-size graph-animal count target. -/
theorem physicalGraphAnimalTotalCountBound1296_of_anchoredCountBound
    (hanchored : PhysicalPlaquetteGraphAnimalAnchoredCountBound1296) :
    PhysicalConnectingClusterGraphAnimalTotalCountBound1296 :=
  physicalGraphAnimalTotalCountBound_of_anchoredCountBound hanchored

/-- A physical `1296` total-size graph-animal word decoder gives the standard
`1296^(n + ceil dist)` shifted graph-animal count. -/
theorem physicalGraphAnimalTotalCountBound1296_of_wordDecoder
    (hdecode : PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound1296)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ) :
    (plaquetteGraphPreconnectedConnectingSubsetsShifted L p q n).card ≤
      1296 ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) :=
  physicalGraphAnimalTotalCountBound_of_wordDecoder hdecode p q n

/-- A total-size graph-animal word decoder discharges the physical total-size
exponential F3-count frontier. -/
theorem physicalTotalConnectingClusterCountBoundExp_of_graphAnimalTotalWordDecoder
    {K : ℕ} (hdecode : PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound K) :
    PhysicalTotalConnectingClusterCountBoundExp 1 K := by
  intro L _ p q n _hn _hdist
  have hnat :
      ((Finset.univ :
        Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
          (fun X =>
            p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
              X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card ≤
        K ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) :=
    (physical_connectingCluster_filter_card_le_graphAnimalShifted p q n).trans
      (physicalGraphAnimalTotalCountBound_of_wordDecoder hdecode p q n)
  have hreal :
      (((Finset.univ :
        Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
          (fun X =>
            p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
              X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        ((K ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simpa [one_mul, Nat.cast_pow] using hreal

/-- A direct total-size graph-animal count bound discharges the physical
total-size exponential F3-count frontier. -/
theorem physicalTotalConnectingClusterCountBoundExp_of_graphAnimalTotalCountBound
    {K : ℕ} (hgraph : PhysicalConnectingClusterGraphAnimalTotalCountBound K) :
    PhysicalTotalConnectingClusterCountBoundExp 1 K := by
  intro L _ p q n _hn _hdist
  have hnat :
      ((Finset.univ :
        Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
          (fun X =>
            p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
              X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card ≤
        K ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) :=
    (physical_connectingCluster_filter_card_le_graphAnimalShifted p q n).trans
      (hgraph p q n)
  have hreal :
      (((Finset.univ :
        Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
          (fun X =>
            p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
              X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        ((K ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simpa [one_mul, Nat.cast_pow] using hreal

/-- A physical `1296` total-size graph-animal word decoder discharges the
physical total-size exponential F3-count frontier. -/
theorem physicalTotalConnectingClusterCountBoundExp_of_graphAnimalTotalWordDecoder1296
    (hdecode : PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound1296) :
    PhysicalTotalConnectingClusterCountBoundExp 1 1296 :=
  physicalTotalConnectingClusterCountBoundExp_of_graphAnimalTotalWordDecoder hdecode

/-- A physical `1296` total-size graph-animal count bound discharges the
physical total-size exponential F3-count frontier. -/
theorem physicalTotalConnectingClusterCountBoundExp_of_graphAnimalTotalCountBound1296
    (hgraph : PhysicalConnectingClusterGraphAnimalTotalCountBound1296) :
    PhysicalTotalConnectingClusterCountBoundExp 1 1296 :=
  physicalTotalConnectingClusterCountBoundExp_of_graphAnimalTotalCountBound hgraph

/-- Package the physical `1296` total-size graph-animal word-decoder target as
the physical total-size exponential F3-count package consumed downstream. -/
def physicalTotalF3CountPackageExp_of_graphAnimalTotalWordDecoder1296
    (hdecode : PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound1296) :
    PhysicalTotalF3CountPackageExp :=
  PhysicalTotalF3CountPackageExp.ofBound 1 1296 one_pos (by norm_num)
    (physicalTotalConnectingClusterCountBoundExp_of_graphAnimalTotalWordDecoder1296
      hdecode)

/-- Package the physical `1296` total-size graph-animal count target as the
physical total-size exponential F3-count package consumed downstream. -/
def physicalTotalF3CountPackageExp_of_graphAnimalTotalCountBound1296
    (hgraph : PhysicalConnectingClusterGraphAnimalTotalCountBound1296) :
    PhysicalTotalF3CountPackageExp :=
  PhysicalTotalF3CountPackageExp.ofBound 1 1296 one_pos (by norm_num)
    (physicalTotalConnectingClusterCountBoundExp_of_graphAnimalTotalCountBound1296
      hgraph)

/-- Package a physical `1296` anchored graph-animal count bound as the physical
total-size exponential F3-count package consumed downstream. -/
def physicalTotalF3CountPackageExp_of_anchoredCountBound1296
    (hanchored : PhysicalPlaquetteGraphAnimalAnchoredCountBound1296) :
    PhysicalTotalF3CountPackageExp :=
  physicalTotalF3CountPackageExp_of_graphAnimalTotalCountBound1296
    (physicalGraphAnimalTotalCountBound1296_of_anchoredCountBound hanchored)

/-- A shifted graph-animal count estimate discharges the physical exponential
F3-count frontier. -/
theorem physicalShiftedConnectingClusterCountBoundExp_of_graphAnimalShiftedCount
    {K : ℕ} (hgraph : PhysicalConnectingClusterGraphAnimalShiftedCountBound K) :
    PhysicalShiftedConnectingClusterCountBoundExp 1 K := by
  intro L _ p q n _hn _hdist
  have hnat :
      ((Finset.univ :
        Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
          (fun X =>
            p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
              X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card ≤
        K ^ n :=
    (physical_connectingCluster_filter_card_le_graphAnimalShifted p q n).trans
      (hgraph p q n)
  have hreal :
      (((Finset.univ :
        Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
          (fun X =>
            p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
              X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        ((K ^ n : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simpa using hreal

/-- Physical graph-animal shifted count target at the current `1296` alphabet
constant. -/
abbrev PhysicalConnectingClusterGraphAnimalShiftedCountBound1296 : Prop :=
  PhysicalConnectingClusterGraphAnimalShiftedCountBound 1296

/-- Physical-specialized bridge from the graph-animal shifted count target to
the exponential F3-count frontier. -/
theorem physicalShiftedConnectingClusterCountBoundExp_of_graphAnimalShiftedCount1296
    (hgraph : PhysicalConnectingClusterGraphAnimalShiftedCountBound1296) :
    PhysicalShiftedConnectingClusterCountBoundExp 1 1296 :=
  physicalShiftedConnectingClusterCountBoundExp_of_graphAnimalShiftedCount hgraph

/-- Package the physical `1296` graph-animal shifted count target as the
physical exponential F3-count package consumed downstream. -/
def physicalShiftedF3CountPackageExp_of_graphAnimalShiftedCount1296
    (hgraph : PhysicalConnectingClusterGraphAnimalShiftedCountBound1296) :
    PhysicalShiftedF3CountPackageExp :=
  PhysicalShiftedF3CountPackageExp.ofBound 1 1296 one_pos (by norm_num)
    (physicalShiftedConnectingClusterCountBoundExp_of_graphAnimalShiftedCount1296
      hgraph)

/-- Physical graph-animal word-decoder target at the current `1296` alphabet
constant. -/
abbrev PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound1296 : Prop :=
  PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound 1296

/-- A physical `1296` graph-animal word decoder gives the physical
graph-animal shifted count target. -/
theorem physicalGraphAnimalShiftedCountBound1296_of_wordDecoder
    (hdecode : PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound1296) :
    PhysicalConnectingClusterGraphAnimalShiftedCountBound1296 :=
  physicalGraphAnimalShiftedCountBound_of_wordDecoder hdecode

/-- A physical `1296` graph-animal word decoder discharges the physical
exponential F3-count frontier. -/
theorem physicalShiftedConnectingClusterCountBoundExp_of_graphAnimalWordDecoder1296
    (hdecode : PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound1296) :
    PhysicalShiftedConnectingClusterCountBoundExp 1 1296 :=
  physicalShiftedConnectingClusterCountBoundExp_of_graphAnimalShiftedCount1296
    (physicalGraphAnimalShiftedCountBound1296_of_wordDecoder hdecode)

/-- Package the physical `1296` graph-animal word-decoder target as the
physical exponential F3-count package consumed downstream. -/
def physicalShiftedF3CountPackageExp_of_graphAnimalWordDecoder1296
    (hdecode : PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound1296) :
    PhysicalShiftedF3CountPackageExp :=
  PhysicalShiftedF3CountPackageExp.ofBound 1 1296 one_pos (by norm_num)
    (physicalShiftedConnectingClusterCountBoundExp_of_graphAnimalWordDecoder1296
      hdecode)

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
#print axioms finsetCodeOfCardLe_injective
#print axioms plaquetteNeighborChoiceCodeBoundDim_of_branchingBoundDim
#print axioms plaquetteNeighborChoiceCodeBoundDim_physical_ternary
#print axioms plaquetteNeighborStepCodeOfChoice_injOn
#print axioms plaquetteNeighborStepCodeBoundDim_of_choiceCodeBoundDim
#print axioms plaquetteNeighborStepCodeBoundDim_of_branchingBoundDim
#print axioms plaquetteNeighborStepCodeBoundDim_physical_ternary
#print axioms plaquetteWalk_card_le_of_injective_code
#print axioms plaquetteWalk_card_le_of_codeBoundDim
#print axioms plaquetteWalkCodeOfStepCode_injective
#print axioms plaquetteWalkCodeBoundDim_of_neighborStepCodeBoundDim
#print axioms plaquetteWalkCodeBoundDim_of_neighborChoiceCodeBoundDim
#print axioms plaquetteWalkCodeBoundDim_of_branchingBoundDim
#print axioms plaquetteWalkCodeBoundDim_physical_ternary
#print axioms plaquetteWalk_card_le_physical_ternary
#print axioms plaquetteWalk_start_mem_rangeFinset
#print axioms plaquetteWalk_vertex_mem_rangeFinset
#print axioms plaquetteWalk_rangeFinset_card_le
#print axioms connectingClusterBucket_card_eq_filter
#print axioms connectingClusterBucket_card_le_walks_of_walkCode
#print axioms connectingClusterBucket_card_le_physical_walk_exp_of_walkCode
#print axioms physical_connectingCluster_filter_card_le_walk_exp_of_walkCode
#print axioms physical_connectingCluster_filter_card_le_extra_walk_exp_of_walkCode
#print axioms physicalShiftedConnectingClusterCountBoundExp_of_extraWalkCode
#print axioms physicalConnectingClusterExtraWalkCodeOfDecoder_injective
#print axioms physicalConnectingClusterExtraWalkCodeBound_of_decoderBound
#print axioms physicalShiftedConnectingClusterCountBoundExp_of_extraWalkDecoder
#print axioms physicalConnectingClusterExtraWalkDecoderBound_of_rangeDecoderCovers
#print axioms physicalShiftedConnectingClusterCountBoundExp_of_rangeDecoderCovers
#print axioms physicalConnectingClusterRangeDecoderCovers_forces_dist_ceiling_le_one
#print axioms physicalConnectingClusterExtraWalkDecoderBound_of_baselineExtraDecoderCovers
#print axioms physicalShiftedConnectingClusterCountBoundExp_of_baselineExtraDecoderCovers
#print axioms physicalConnectingClusterExtraWordCodeOfDecoder_injective
#print axioms connectingClusterBucket_card_le_extra_word_of_decoder
#print axioms physicalShiftedConnectingClusterCountBoundExp_of_extraWordDecoder
#print axioms physicalConnectingClusterExtraWordDecoderBound_of_baselineExtraWordDecoderCovers
#print axioms physicalShiftedConnectingClusterCountBoundExp_of_baselineExtraWordDecoderCovers
#print axioms physicalShiftedConnectingClusterCountBoundExp_of_baselineExtraWordDecoderCovers1296
#print axioms physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296
#print axioms plaquetteGraph_isChain_of_nodup_siteLatticeDist_isChain
#print axioms polymerConnected_exists_plaquetteGraph_chain
#print axioms plaquetteGraph_reachable_of_chain_endpoints
#print axioms polymerConnected_plaquetteGraph_reachable
#print axioms plaquetteGraph_induce_reachable_of_chain_endpoints
#print axioms polymerConnected_plaquetteGraph_induce_reachable
#print axioms polymerConnected_plaquetteGraph_induce_preconnected
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_card_eq
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_card_pos
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_ne_root
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_ne_member
#print axioms simpleGraph_walk_exists_adj_start_of_ne
#print axioms simpleGraph_walk_exists_adj_start_and_tail_of_ne
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_nonSingleton_member_has_neighbor
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighbor
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_nonempty
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_pos
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_neighborFinset
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_branching
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_1296
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCodeOfBranching_injective
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296_injective
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteCode1296_spec
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296_mem_erase_root
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296_card
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem_firstDeleteResidual1296
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_preconnected
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296_mem_of_preconnected
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_preconnected_of_induced_degree_one
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_induced_degree_one
#print axioms plaquetteGraphAnchoredSafeDeletionExists_of_degreeOneDeletionExists
#print axioms physicalPlaquetteGraphAnchoredSafeDeletionExists_of_degreeOneDeletionExists
#print axioms plaquetteGraphAnchoredSafeDeletionExists_of_nonRootNonCutExists
#print axioms plaquetteGraphAnchoredNonRootNonCutExists_of_twoNonCutExists
#print axioms plaquetteGraphAnchoredSafeDeletionExists_of_twoNonCutExists
#print axioms plaquetteGraphAnchoredNonRootNonCutExists_of_safeDeletionExists
#print axioms plaquetteGraphAnchoredSafeDeletionExists_iff_nonRootNonCutExists
#print axioms physicalPlaquetteGraphAnchoredSafeDeletionExists_of_nonRootNonCutExists
#print axioms physicalPlaquetteGraphAnchoredNonRootNonCutExists_of_twoNonCutExists
#print axioms physicalPlaquetteGraphAnchoredSafeDeletionExists_of_twoNonCutExists
#print axioms physicalPlaquetteGraphAnchoredNonRootNonCutExists_of_safeDeletionExists
#print axioms physicalPlaquetteGraphAnchoredSafeDeletionExists_iff_nonRootNonCutExists
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_preconnected_unrooted
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_preconnected_unrooted
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_two
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_two
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_three
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_three
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_le_three
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_le_three
#print axioms plaquetteGraphAnchoredSafeDeletionExists_of_highCardTwoNonCutExists
#print axioms physicalPlaquetteGraphAnchoredSafeDeletionExists_of_highCardTwoNonCutExists
#print axioms plaquetteGraph_erase_preconnected_of_subtype_compl_preconnected
#print axioms simpleGraph_isTree_exists_two_distinct_degree_one_of_card_ge_two
#print axioms simpleGraphHighCardTwoNonCutExists
#print axioms plaquetteGraphAnchoredHighCardTwoNonCutExists_of_simpleGraph
#print axioms physicalPlaquetteGraphAnchoredHighCardTwoNonCutExists_of_simpleGraph
#print axioms plaquetteGraphAnchoredHighCardTwoNonCutExists
#print axioms physicalPlaquetteGraphAnchoredHighCardTwoNonCutExists
#print axioms plaquetteGraphAnchoredSafeDeletionExists
#print axioms physicalPlaquetteGraphAnchoredSafeDeletionExists
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem
#print axioms physicalPlaquetteGraphDeletedVertexDecoderStep1296_exists_recoverable_deletion
#print axioms physicalNeighborDecodeOfStepCode_spec
#print axioms physicalPlaquetteGraphCanonicalResidualParentSelector1296_of_residualExtensionCompatibility1296
#print axioms physicalPlaquetteGraphResidualExtensionCompatibility1296_of_canonicalResidualParentSelector1296
#print axioms physicalPlaquetteGraphResidualExtensionCompatibility1296_iff_canonicalResidualParentSelector1296
#print axioms physicalPlaquetteGraphResidualParentInvariant1296_of_canonicalResidualParentSelector1296
#print axioms physicalPlaquetteGraphDeletedVertexDecoderStep1296_of_residualParentInvariant1296
#print axioms physicalPlaquetteGraphDeletedVertexDecoderStep1296_of_canonicalResidualParentSelector1296
#print axioms physicalPlaquetteGraphResidualParentMenuBound1296_of_essentialSafeDeletionParentFrontierBound1296
#print axioms physicalPlaquetteGraphSafeDeletionOrientationCodeBound1296_of_portalSupportedSafeDeletionOrientation1296
#print axioms physicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296_of_safeDeletionOrientationCodeBound1296
#print axioms physicalPlaquetteGraphResidualParentMenuCovers1296_of_residualParentMenuBound1296
#print axioms physicalPlaquetteGraphSymbolicResidualParentSelector1296_of_residualParentMenuCovers1296
#print axioms physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296_of_symbolicResidualParentSelector1296
#print axioms physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296_of_multiPortalSupportedSafeDeletionOrientation1296x1296
#print axioms physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296_of_baseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296
#print axioms physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_terminalPredecessorDomination1296
#print axioms physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_residualFiberTerminalPredecessorDomination1296_of_packing1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296_of_residualFiberTerminalPredecessorImageBound1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296_of_residualFiberCanonicalLastEdgeImageBound1296
#print axioms PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296
#print axioms physicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296
#print axioms PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
#print axioms physicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296_of_residualFiberNonSingletonMemberNeighborWalkSplit1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296_of_residualFiberTerminalNeighborSelectorDataSource1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominationRelation1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominatingMenu1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296_of_residualFiberTerminalNeighborCodeSeparation1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296_of_residualFiberTerminalNeighborSelectorCodeSeparation1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296_of_residualFiberTerminalNeighborSelectorImageBound1296
#print axioms PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData
#print axioms PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjectionData
#print axioms PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSourceData
#print axioms PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparationData
#print axioms PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSourceData
#print axioms PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData
#print axioms PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296
#print axioms physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296_of_baseZoneResidualValueCodeSeparation1296
#print axioms PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealizationData
#print axioms PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296
#print axioms physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296_of_baseZoneResidualValueCodeRealization1296
#print axioms PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSourceData
#print axioms PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296
#print axioms physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296_of_baseZoneResidualValueCodeSource1296
#print axioms PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjectionData
#print axioms PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
#print axioms physicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296_of_baseZoneOriginCertificateCodeInjection1296
#print axioms PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateSource1296
#print axioms physicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296_of_baseZoneOriginCertificateSource1296
#print axioms PhysicalPlaquetteGraphResidualFiberBaseZoneCoordinateRealizationSeparation1296
#print axioms physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296_of_baseZoneCoordinateRealizationSeparation1296
#print axioms PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
#print axioms physicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateSource1296
#print axioms PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
#print axioms physicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296_of_residualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296
#print axioms PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296
#print axioms physicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296_of_residualFiberBookkeepingBaseZoneTagCoordinate1296
#print axioms PhysicalPlaquetteGraphResidualFiberBookkeepingTagSpaceInjection1296
#print axioms physicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296_of_residualFiberBookkeepingTagSpaceInjection1296
#print axioms PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBookkeepingTagInjection1296
#print axioms physicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296_of_residualFiberSelectorAdmissibleBookkeepingTagInjection1296
#print axioms PhysicalPlaquetteGraphResidualFiberBookkeepingTagAdmissibleValueSeparation1296
#print axioms physicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296_of_residualFiberBookkeepingTagAdmissibleValueSeparation1296
#print axioms PhysicalPlaquetteGraphResidualFiberBookkeepingTagCoordinate1296
#print axioms physicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296_of_residualFiberBookkeepingTagCoordinate1296
#print axioms PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueSeparation1296
#print axioms physicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296_of_residualFiberBookkeepingTagValueSeparation1296
#print axioms PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296
#print axioms physicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296_of_residualFiberBookkeepingTagValueCodeSource1296
#print axioms physicalPlaquetteGraphResidualFiberBookkeepingTagMap1296_of_residualFiberTerminalNeighborSelectorSource1296_of_residualFiberBookkeepingTagCodeForSelector1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296_of_residualFiberBookkeepingTagMap1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296_of_residualFiberTerminalNeighborAmbientBookkeepingTagCode1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296_of_residualFiberTerminalNeighborAmbientValueCode1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296_of_residualFiberTerminalNeighborAbsoluteSelectedValueCode1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296_of_residualFiberTerminalNeighborBasepointIndependentCode1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296_of_residualFiberTerminalNeighborGeometricSelectorCode1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296_of_residualFiberTerminalNeighborDominatingMenu1296
#print axioms physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296_of_residualFiberTerminalNeighborImageCompression1296
#print axioms physicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296_of_residualFiberTerminalNeighborSelectorImageBound1296
#print axioms physicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296_of_residualFiberCanonicalTerminalNeighborImageBound1296
#print axioms physicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296_of_residualFiberCanonicalTerminalSuffixImageBound1296
#print axioms physicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296_of_residualFiberCanonicalWalkTerminalEdgeImageBound1296
#print axioms physicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296_of_residualFiberCanonicalTerminalEdgeSelector1296
#print axioms physicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296_of_residualLastEdgeDominatingSetBound1296
#print axioms physicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296_of_baseAwareResidualCanonicalLastEdgePredecessorSelector1296
#print axioms physicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296_of_baseAwareResidualCanonicalLastStepPredecessorImageBound1296
#print axioms physicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296_of_baseAwareResidualLastStepPortalImageBound1296
#print axioms physicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296_of_baseAwareResidualPortalMenuBound1296
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset_to_member
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_to_member
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset_tail_to_member
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_tail_to_member
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset_reachable_to_member
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_reachable_to_member
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296_spec
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborCode
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborCode1296
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_eq_empty
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_one_subset_singleton
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_one_card_le_one
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_card_le_pow
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_one_card_le_pow
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_base_card_le_pow
#print axioms physicalPlaquetteGraph_root_has_distinct_plaquette
#print axioms physicalPlaquetteGraph_baseAwareLowCardBookkeepingTotalization1296
#print axioms physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296
#print axioms physicalPlaquetteGraph_residualDominatedTerminalPredecessorPacking1296
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_wordDecoderCovers
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_one_wordDecoderCovers
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_base_wordDecoderCovers
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_root_reachable
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path
#print axioms PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound.of_nontrivial
#print axioms physicalPlaquetteGraphAnimalAnchoredWordDecoderBound1296_of_nontrivial
#print axioms PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound.mono
#print axioms physicalPlaquetteGraphAnimalAnchoredWordCodeOfDecoder_injective
#print axioms physicalPlaquetteGraphAnimalAnchoredCountBound_of_wordDecoder
#print axioms PhysicalPlaquetteGraphAnimalAnchoredCountBound.mono
#print axioms plaquetteGraphPreconnectedConnectingSubsetsShifted_subset_anchored
#print axioms plaquetteGraphPreconnectedConnectingSubsetsShifted_card_le_anchored
#print axioms connectingCluster_filter_subset_preconnectedSubsetsAnchoredCard
#print axioms connectingCluster_filter_card_le_preconnectedSubsetsAnchoredCard
#print axioms physical_connectingCluster_filter_subset_graphAnimalShifted
#print axioms physical_connectingCluster_filter_card_le_graphAnimalShifted
#print axioms physicalGraphAnimalShiftedWordCodeOfDecoder_injective
#print axioms physicalGraphAnimalShiftedCountBound_of_wordDecoder
#print axioms physicalGraphAnimalShiftedCountBound_zero_card_le_one
#print axioms physicalGraphAnimalTotalWordCodeOfDecoder_injective
#print axioms physicalGraphAnimalTotalCountBound_of_wordDecoder
#print axioms PhysicalConnectingClusterGraphAnimalTotalCountBound.mono
#print axioms physicalGraphAnimalTotalCountBound_of_anchoredCountBound
#print axioms physicalGraphAnimalTotalCountBound_of_totalWordDecoder
#print axioms physicalGraphAnimalTotalCountBound1296_of_anchoredCountBound
#print axioms physicalGraphAnimalTotalCountBound1296_of_wordDecoder
#print axioms physicalTotalConnectingClusterCountBoundExp_of_graphAnimalTotalWordDecoder
#print axioms physicalTotalConnectingClusterCountBoundExp_of_graphAnimalTotalCountBound
#print axioms physicalTotalConnectingClusterCountBoundExp_of_graphAnimalTotalWordDecoder1296
#print axioms physicalTotalConnectingClusterCountBoundExp_of_graphAnimalTotalCountBound1296
#print axioms physicalTotalF3CountPackageExp_of_graphAnimalTotalWordDecoder1296
#print axioms physicalTotalF3CountPackageExp_of_graphAnimalTotalCountBound1296
#print axioms physicalTotalF3CountPackageExp_of_anchoredCountBound1296
#print axioms physicalShiftedConnectingClusterCountBoundExp_of_graphAnimalShiftedCount
#print axioms physicalShiftedConnectingClusterCountBoundExp_of_graphAnimalShiftedCount1296
#print axioms physicalShiftedF3CountPackageExp_of_graphAnimalShiftedCount1296
#print axioms physicalGraphAnimalShiftedCountBound1296_of_wordDecoder
#print axioms physicalShiftedConnectingClusterCountBoundExp_of_graphAnimalWordDecoder1296
#print axioms physicalShiftedF3CountPackageExp_of_graphAnimalWordDecoder1296

end YangMills
