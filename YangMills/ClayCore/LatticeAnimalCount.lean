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

/-- Physical specialization: degree-one deletion existence is sufficient for
safe deletion existence. -/
theorem physicalPlaquetteGraphAnchoredSafeDeletionExists_of_degreeOneDeletionExists
    {L : ℕ} [NeZero L]
    (hdegone : PhysicalPlaquetteGraphAnchoredDegreeOneDeletionExists L) :
    PhysicalPlaquetteGraphAnchoredSafeDeletionExists L :=
  plaquetteGraphAnchoredSafeDeletionExists_of_degreeOneDeletionExists
    (d := physicalClayDimension) (L := L) hdegone

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
#print axioms simpleGraph_walk_exists_adj_start_of_ne
#print axioms simpleGraph_walk_exists_adj_start_and_tail_of_ne
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
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion
#print axioms physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion
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
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_wordDecoderCovers
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_one_wordDecoderCovers
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_base_wordDecoderCovers
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_root_reachable
#print axioms plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path
#print axioms PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound.of_nontrivial
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
