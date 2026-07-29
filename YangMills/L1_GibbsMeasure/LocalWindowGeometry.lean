/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalMarginal
import YangMills.L1_GibbsMeasure.ClusterGeometry

/-!
# Common finite windows for different tori

Small marked clusters are compared through ordinary natural-number
coordinates after translating the observable away from every periodic seam.
This file defines the common coordinate objects and their injective
realizations in any torus large enough to contain the window.

The strict fitting predicate for a plaquette includes one lattice step.  It
therefore records the thickness of the plaquette, rather than merely bounding
its base site.  No map between complete configurations of different volumes
is introduced.
-/

namespace YangMills

/-- A site in a common non-periodic natural-coordinate window. -/
abbrev WindowSite (d : ℕ) := Fin d → ℕ

/-- Positive unit shift of a common-window site. -/
def WindowSite.shift {d : ℕ} (x : WindowSite d) (i : Fin d) :
    WindowSite d :=
  fun j => x j + if j = i then 1 else 0

/-- A positive edge in a common non-periodic window. -/
structure WindowPosEdge (d : ℕ) where
  source : WindowSite d
  dir : Fin d
  deriving DecidableEq

/-- A positively oriented plaquette in a common non-periodic window. -/
structure WindowPlaquette (d : ℕ) where
  site : WindowSite d
  dir1 : Fin d
  dir2 : Fin d
  hlt : dir1 < dir2
  deriving DecidableEq

@[ext]
theorem WindowPosEdge.ext {d : ℕ} {e f : WindowPosEdge d}
    (hsource : e.source = f.source) (hdir : e.dir = f.dir) : e = f := by
  cases e
  cases f
  simp_all

@[ext]
theorem WindowPlaquette.ext {d : ℕ} {p q : WindowPlaquette d}
    (hsite : p.site = q.site) (hdir1 : p.dir1 = q.dir1)
    (hdir2 : p.dir2 = q.dir2) : p = q := by
  cases p
  cases q
  simp_all

/-- A window site fits in the side-`N` box without reduction modulo `N`. -/
def WindowSite.Fits {d : ℕ} (x : WindowSite d) (N : ℕ) : Prop :=
  ∀ j, x j < N

/-- A window edge fits in the side-`N` box. -/
def WindowPosEdge.Fits {d : ℕ} (e : WindowPosEdge d) (N : ℕ) : Prop :=
  e.source.Fits N

/-- A window plaquette fits strictly in the side-`N` box, including all
sites reached by one positive lattice step. -/
def WindowPlaquette.Fits {d : ℕ} (p : WindowPlaquette d) (N : ℕ) : Prop :=
  ∀ j, p.site j + 1 < N

/-- Realize a fitting common-window site in a finite box. -/
def WindowSite.toFinBox {d N : ℕ} (x : WindowSite d)
    (h : x.Fits N) : FinBox d N :=
  fun j => ⟨x j, h j⟩

/-- Realize a fitting common-window positive edge in a torus. -/
def WindowPosEdge.toPosEdge {d N : ℕ} (e : WindowPosEdge d)
    (h : e.Fits N) : PosEdge d N :=
  ⟨⟨e.source.toFinBox h, e.dir, true⟩, rfl⟩

/-- Realize a strictly fitting common-window plaquette in a torus. -/
def WindowPlaquette.toConcrete {d N : ℕ} (p : WindowPlaquette d)
    (h : p.Fits N) : ConcretePlaquette d N :=
  ⟨p.site.toFinBox (fun j => lt_trans (Nat.lt_succ_self _) (h j)),
    p.dir1, p.dir2, p.hlt⟩

/-- The four positive window edges read by a window plaquette. -/
def WindowPlaquette.posEdge {d : ℕ} (p : WindowPlaquette d) :
    Fin 4 → WindowPosEdge d
  | ⟨0, _⟩ => ⟨p.site, p.dir1⟩
  | ⟨1, _⟩ => ⟨p.site.shift p.dir1, p.dir2⟩
  | ⟨2, _⟩ => ⟨p.site.shift p.dir2, p.dir1⟩
  | ⟨3, _⟩ => ⟨p.site, p.dir2⟩

/-- Every positive edge of a strictly fitting plaquette also fits. -/
theorem WindowPlaquette.posEdge_fits {d N : ℕ}
    (p : WindowPlaquette d) (h : p.Fits N) (k : Fin 4) :
    (p.posEdge k).Fits N := by
  intro j
  fin_cases k
  · exact lt_trans (Nat.lt_succ_self _) (h j)
  · by_cases hj : j = p.dir1
    · simpa [WindowPlaquette.posEdge, WindowPosEdge.Fits,
        WindowSite.Fits, WindowSite.shift, hj] using h j
    · exact lt_trans (Nat.lt_succ_self _)
        (by simpa [WindowPlaquette.posEdge, WindowPosEdge.Fits,
          WindowSite.Fits, WindowSite.shift, hj] using h j)
  · by_cases hj : j = p.dir2
    · simpa [WindowPlaquette.posEdge, WindowPosEdge.Fits,
        WindowSite.Fits, WindowSite.shift, hj] using h j
    · exact lt_trans (Nat.lt_succ_self _)
        (by simpa [WindowPlaquette.posEdge, WindowPosEdge.Fits,
          WindowSite.Fits, WindowSite.shift, hj] using h j)
  · exact lt_trans (Nat.lt_succ_self _) (h j)

/-- Strict fitting makes ordinary window shifts commute with the periodic
`FinBox.shift`, because no modulo wrap occurs. -/
theorem WindowSite.toFinBox_shift {d N : ℕ} [NeZero N]
    (x : WindowSite d) (h : ∀ j, x j + 1 < N) (i : Fin d) :
    (x.toFinBox (fun j => lt_trans (Nat.lt_succ_self _) (h j))).shift i =
      (x.shift i).toFinBox (fun j => by
        by_cases hj : j = i
        · simpa [WindowSite.shift, hj] using h j
        · exact lt_trans (Nat.lt_succ_self _)
            (by simpa [WindowSite.shift, hj] using h j)) := by
  funext j
  apply Fin.ext
  by_cases hj : j = i
  · subst j
    simp [WindowSite.toFinBox, WindowSite.shift, FinBox.shift,
      Nat.mod_eq_of_lt (h i)]
  · simp [WindowSite.toFinBox, WindowSite.shift, FinBox.shift, hj]

/-- Realization commutes with the four-edge boundary of a plaquette. -/
theorem WindowPlaquette.toConcrete_edge_pos {d N : ℕ} [NeZero N]
    (p : WindowPlaquette d) (h : p.Fits N) (k : Fin 4) :
    ((p.toConcrete h).edges k).pos =
      (p.posEdge k).toPosEdge (p.posEdge_fits h k) := by
  apply Subtype.ext
  fin_cases k
  · rfl
  · change ConcreteEdge.mk
        ((p.site.toFinBox _).shift p.dir1) p.dir2 true =
      ConcreteEdge.mk ((p.site.shift p.dir1).toFinBox _) p.dir2 true
    congr 1
    exact WindowSite.toFinBox_shift p.site h p.dir1
  · change ConcreteEdge.mk
        ((p.site.toFinBox _).shift p.dir2) p.dir1 true =
      ConcreteEdge.mk ((p.site.shift p.dir2).toFinBox _) p.dir1 true
    congr 1
    exact WindowSite.toFinBox_shift p.site h p.dir2
  · rfl

/-- Common-window positive edges embed injectively in every volume in which
they fit. -/
theorem WindowPosEdge.toPosEdge_injective {d N : ℕ}
    {S : Finset (WindowPosEdge d)} (hS : ∀ e ∈ S, e.Fits N) :
    Function.Injective
      (fun e : ↥S => e.1.toPosEdge (hS e.1 e.2)) := by
  intro e f hef
  have hsource : e.1.source = f.1.source := by
    funext j
    have hj := congrArg (fun q => (q.1.source j).val) hef
    simpa [WindowPosEdge.toPosEdge, WindowSite.toFinBox] using hj
  have hdir : e.1.dir = f.1.dir := by
    have hd := congrArg (fun q => q.1.dir) hef
    simpa [WindowPosEdge.toPosEdge] using hd
  apply Subtype.ext
  exact WindowPosEdge.ext hsource hdir

/-- Equality of two individually fitting realized edges already holds in the
common window.  This non-subtype form is convenient when comparing the four
boundary slots of two plaquettes. -/
theorem WindowPosEdge.eq_of_toPosEdge_eq {d N : ℕ}
    {e f : WindowPosEdge d} (he : e.Fits N) (hf : f.Fits N)
    (h : e.toPosEdge he = f.toPosEdge hf) :
    e = f := by
  have hsource : e.source = f.source := by
    funext j
    have hj := congrArg (fun q => (q.1.source j).val) h
    simpa [WindowPosEdge.toPosEdge, WindowSite.toFinBox] using hj
  have hdir : e.dir = f.dir := by
    have hd := congrArg (fun q => q.1.dir) h
    simpa [WindowPosEdge.toPosEdge] using hd
  exact WindowPosEdge.ext hsource hdir

/-- Realization of a finite common-window edge set in one torus.  The
subtype in the image remembers the fitting proof for each edge. -/
noncomputable def WindowPosEdge.realizedFinset
    {d N : ℕ} (S : Finset (WindowPosEdge d))
    (hS : ∀ e ∈ S, e.Fits N) :
    Finset (PosEdge d N) :=
  Finset.univ.image
    (fun e : ↥S => e.1.toPosEdge (hS e.1 e.2))

@[simp]
theorem WindowPosEdge.mem_realizedFinset_iff
    {d N : ℕ} {S : Finset (WindowPosEdge d)}
    {hS : ∀ e ∈ S, e.Fits N} {q : PosEdge d N} :
    q ∈ WindowPosEdge.realizedFinset S hS ↔
      ∃ e : ↥S, e.1.toPosEdge (hS e.1 e.2) = q := by
  simp [WindowPosEdge.realizedFinset]

/-- Inclusion of common-window edge sets is preserved by realization. -/
theorem WindowPosEdge.realizedFinset_mono
    {d N : ℕ} {S T : Finset (WindowPosEdge d)}
    (hST : S ⊆ T)
    (hS : ∀ e ∈ S, e.Fits N) (hT : ∀ e ∈ T, e.Fits N) :
    WindowPosEdge.realizedFinset S hS ⊆
      WindowPosEdge.realizedFinset T hT := by
  intro q hq
  obtain ⟨e, he⟩ :=
    WindowPosEdge.mem_realizedFinset_iff.mp hq
  apply WindowPosEdge.mem_realizedFinset_iff.mpr
  refine ⟨⟨e.1, hST e.2⟩, ?_⟩
  simpa using he

/-- Realization into a fitting torus preserves and reflects disjointness of
finite common-window edge sets. -/
theorem WindowPosEdge.disjoint_realizedFinset_iff
    {d N : ℕ} [NeZero N]
    {S T : Finset (WindowPosEdge d)}
    (hS : ∀ e ∈ S, e.Fits N) (hT : ∀ e ∈ T, e.Fits N) :
    Disjoint (WindowPosEdge.realizedFinset S hS)
        (WindowPosEdge.realizedFinset T hT) ↔
      Disjoint S T := by
  rw [Finset.disjoint_left, Finset.disjoint_left]
  constructor
  · intro h e heS heT
    apply h
    · apply WindowPosEdge.mem_realizedFinset_iff.mpr
      exact ⟨⟨e, heS⟩, rfl⟩
    · apply WindowPosEdge.mem_realizedFinset_iff.mpr
      exact ⟨⟨e, heT⟩, rfl⟩
  · intro h q hqS hqT
    obtain ⟨eS, heS⟩ :=
      WindowPosEdge.mem_realizedFinset_iff.mp hqS
    obtain ⟨eT, heT⟩ :=
      WindowPosEdge.mem_realizedFinset_iff.mp hqT
    have he : eS.1 = eT.1 :=
      WindowPosEdge.eq_of_toPosEdge_eq
        (hS eS.1 eS.2) (hT eT.1 eT.2) (heS.trans heT.symm)
    exact h eS.2 (by simpa [he] using eT.2)

/-- A finite common-window edge set is canonically equivalent to its
realization in every fitting torus. -/
noncomputable def WindowPosEdge.realizedEquiv
    {d N : ℕ} (S : Finset (WindowPosEdge d))
    (hS : ∀ e ∈ S, e.Fits N) :
    ↥S ≃ {q : PosEdge d N //
      q ∈ WindowPosEdge.realizedFinset S hS} :=
  Equiv.ofBijective
    (fun e : ↥S =>
      ⟨e.1.toPosEdge (hS e.1 e.2),
        WindowPosEdge.mem_realizedFinset_iff.mpr ⟨e, rfl⟩⟩)
    ⟨by
      intro e f hef
      apply WindowPosEdge.toPosEdge_injective hS
      exact congrArg Subtype.val hef,
     by
      intro q
      obtain ⟨e, he⟩ :=
        WindowPosEdge.mem_realizedFinset_iff.mp q.2
      exact ⟨e, Subtype.ext he⟩⟩

/-- The canonical finite-support equivalence between two torus
realizations of the same common-window edge set. -/
noncomputable def WindowPosEdge.realizedSupportEquiv
    {d N M : ℕ} (S : Finset (WindowPosEdge d))
    (hN : ∀ e ∈ S, e.Fits N) (hM : ∀ e ∈ S, e.Fits M) :
    {q : PosEdge d N // q ∈ WindowPosEdge.realizedFinset S hN} ≃
      {q : PosEdge d M // q ∈ WindowPosEdge.realizedFinset S hM} :=
  (WindowPosEdge.realizedEquiv S hN).symm.trans
    (WindowPosEdge.realizedEquiv S hM)

@[simp]
theorem WindowPosEdge.realizedSupportEquiv_apply
    {d N M : ℕ} (S : Finset (WindowPosEdge d))
    (hN : ∀ e ∈ S, e.Fits N) (hM : ∀ e ∈ S, e.Fits M)
    (e : ↥S) :
    WindowPosEdge.realizedSupportEquiv S hN hM
        (WindowPosEdge.realizedEquiv S hN e) =
      WindowPosEdge.realizedEquiv S hM e := by
  simp [WindowPosEdge.realizedSupportEquiv]

/-- Corresponding extensions of one finite-support assignment agree on
every common-window edge. -/
theorem WindowPosEdge.extend_realizedSupportEquiv_apply
    {d N M : ℕ} {G : Type*}
    (S : Finset (WindowPosEdge d))
    (hN : ∀ e ∈ S, e.Fits N) (hM : ∀ e ∈ S, e.Fits M)
    (g₀ : G)
    (a : {q : PosEdge d N //
      q ∈ WindowPosEdge.realizedFinset S hN} → G)
    (e : ↥S) :
    extendOnFinset
        (fun q : PosEdge d N =>
          q ∈ WindowPosEdge.realizedFinset S hN) g₀ a
        ((WindowPosEdge.realizedEquiv S hN e).1)
      =
    extendOnFinset
        (fun q : PosEdge d M =>
          q ∈ WindowPosEdge.realizedFinset S hM) g₀
        (fun t => a
          ((WindowPosEdge.realizedSupportEquiv S hN hM).symm t))
        ((WindowPosEdge.realizedEquiv S hM e).1) := by
  simp [extendOnFinset]
  apply congrArg a
  let E := WindowPosEdge.realizedSupportEquiv S hN hM
  calc
    WindowPosEdge.realizedEquiv S hN e
        = E.symm (E (WindowPosEdge.realizedEquiv S hN e)) :=
      (E.symm_apply_apply _).symm
    _ = E.symm (WindowPosEdge.realizedEquiv S hM e) :=
      congrArg E.symm
        (WindowPosEdge.realizedSupportEquiv_apply S hN hM e)

/-- Common-window plaquettes embed injectively in every volume in which they
fit strictly. -/
theorem WindowPlaquette.toConcrete_injective {d N : ℕ}
    {S : Finset (WindowPlaquette d)} (hS : ∀ p ∈ S, p.Fits N) :
    Function.Injective
      (fun p : ↥S => p.1.toConcrete (hS p.1 p.2)) := by
  intro p q hpq
  have hsite : p.1.site = q.1.site := by
    funext j
    have hj := congrArg (fun r => (r.site j).val) hpq
    simpa [WindowPlaquette.toConcrete, WindowSite.toFinBox] using hj
  have hdir1 : p.1.dir1 = q.1.dir1 :=
    congrArg ConcretePlaquette.dir1 hpq
  have hdir2 : p.1.dir2 = q.1.dir2 :=
    congrArg ConcretePlaquette.dir2 hpq
  apply Subtype.ext
  exact WindowPlaquette.ext hsite hdir1 hdir2

/-- Two common-window plaquettes touch when two of their four positive
boundary edges coincide. -/
def WindowPlaquette.Touches {d : ℕ}
    (p q : WindowPlaquette d) : Prop :=
  ∃ i j : Fin 4, p.posEdge i = q.posEdge j

/-- The four positive common-window edges of one plaquette. -/
def WindowPlaquette.boundaryEdges {d : ℕ}
    (p : WindowPlaquette d) : Finset (WindowPosEdge d) :=
  Finset.univ.image p.posEdge

@[simp]
theorem WindowPlaquette.mem_boundaryEdges_iff
    {d : ℕ} {p : WindowPlaquette d} {e : WindowPosEdge d} :
    e ∈ p.boundaryEdges ↔ ∃ k : Fin 4, p.posEdge k = e := by
  simp [WindowPlaquette.boundaryEdges]

/-- Positive-edge support of a finite common-window plaquette set. -/
def WindowPlaquette.edgeSupport {d : ℕ}
    (S : Finset (WindowPlaquette d)) : Finset (WindowPosEdge d) :=
  S.biUnion WindowPlaquette.boundaryEdges

/-- If all plaquettes fit, every edge in their common-window support fits. -/
theorem WindowPlaquette.edgeSupport_fits
    {d N : ℕ} {S : Finset (WindowPlaquette d)}
    (hS : ∀ p ∈ S, p.Fits N) :
    ∀ e ∈ WindowPlaquette.edgeSupport S, e.Fits N := by
  intro e he
  obtain ⟨p, hp, hep⟩ :=
    Finset.mem_biUnion.mp he
  obtain ⟨k, hk⟩ :=
    WindowPlaquette.mem_boundaryEdges_iff.mp hep
  rw [← hk]
  exact p.posEdge_fits (hS p hp) k

/-- Realization of a finite common-window plaquette set in one torus. -/
noncomputable def WindowPlaquette.realizedFinset
    {d N : ℕ} (S : Finset (WindowPlaquette d))
    (hS : ∀ p ∈ S, p.Fits N) :
    Finset (ConcretePlaquette d N) :=
  Finset.univ.image
    (fun p : ↥S => p.1.toConcrete (hS p.1 p.2))

@[simp]
theorem WindowPlaquette.mem_realizedFinset_iff
    {d N : ℕ} {S : Finset (WindowPlaquette d)}
    {hS : ∀ p ∈ S, p.Fits N} {q : ConcretePlaquette d N} :
    q ∈ WindowPlaquette.realizedFinset S hS ↔
      ∃ p : ↥S, p.1.toConcrete (hS p.1 p.2) = q := by
  simp [WindowPlaquette.realizedFinset]

/-- A finite common-window plaquette set is canonically equivalent to its
realization in a fitting torus. -/
noncomputable def WindowPlaquette.realizedEquiv
    {d N : ℕ} (S : Finset (WindowPlaquette d))
    (hS : ∀ p ∈ S, p.Fits N) :
    ↥S ≃ {q : ConcretePlaquette d N //
      q ∈ WindowPlaquette.realizedFinset S hS} :=
  Equiv.ofBijective
    (fun p : ↥S =>
      ⟨p.1.toConcrete (hS p.1 p.2),
        WindowPlaquette.mem_realizedFinset_iff.mpr ⟨p, rfl⟩⟩)
    ⟨by
      intro p q hpq
      apply WindowPlaquette.toConcrete_injective hS
      exact congrArg Subtype.val hpq,
     by
      intro q
      obtain ⟨p, hp⟩ :=
        WindowPlaquette.mem_realizedFinset_iff.mp q.2
      exact ⟨p, Subtype.ext hp⟩⟩

/-- Realization preserves the cardinality of a finite window plaquette set. -/
theorem WindowPlaquette.card_realizedFinset
    {d N : ℕ} {S : Finset (WindowPlaquette d)}
    (hS : ∀ p ∈ S, p.Fits N) :
    (WindowPlaquette.realizedFinset S hS).card = S.card := by
  rw [WindowPlaquette.realizedFinset,
    Finset.card_image_of_injective]
  · exact Fintype.card_coe S
  · exact WindowPlaquette.toConcrete_injective hS

/-- Products over a realized set can be pulled back to the common-window
subtype without multiplicities. -/
theorem WindowPlaquette.prod_realizedFinset
    {d N : ℕ} {S : Finset (WindowPlaquette d)}
    (hS : ∀ p ∈ S, p.Fits N)
    {α : Type*} [CommMonoid α]
    (f : ConcretePlaquette d N → α) :
    ∏ q ∈ WindowPlaquette.realizedFinset S hS, f q =
      ∏ p : ↥S, f (p.1.toConcrete (hS p.1 p.2)) := by
  rw [WindowPlaquette.realizedFinset,
    Finset.prod_image]
  intro p _ q _ hpq
  exact WindowPlaquette.toConcrete_injective hS hpq

/-- Every realized boundary slot belongs to the usual torus plaquette
support. -/
theorem WindowPlaquette.toConcrete_posEdge_mem_support
    {d N : ℕ} [NeZero N] (p : WindowPlaquette d)
    (h : p.Fits N) (k : Fin 4) :
    (p.posEdge k).toPosEdge (p.posEdge_fits h k) ∈
      plaquetteSupport (p.toConcrete h) := by
  rw [mem_plaquetteSupport_iff]
  fin_cases k
  · exact Or.inl (p.toConcrete_edge_pos h 0).symm
  · exact Or.inr (Or.inl (p.toConcrete_edge_pos h 1).symm)
  · exact Or.inr (Or.inr
      (Or.inl (p.toConcrete_edge_pos h 2).symm))
  · exact Or.inr (Or.inr
      (Or.inr (p.toConcrete_edge_pos h 3).symm))

/-- Every positive support edge of a realized common-window plaquette comes
from one of its four common-window slots. -/
theorem WindowPlaquette.exists_posEdge_eq_of_mem_support
    {d N : ℕ} [NeZero N] (p : WindowPlaquette d)
    (h : p.Fits N) {e : PosEdge d N}
    (he : e ∈ plaquetteSupport (p.toConcrete h)) :
    ∃ k : Fin 4,
      e = (p.posEdge k).toPosEdge (p.posEdge_fits h k) := by
  rcases (mem_plaquetteSupport_iff (p.toConcrete h) e).mp he with
      he | he | he | he
  · exact ⟨0, he.trans (p.toConcrete_edge_pos h 0)⟩
  · exact ⟨1, he.trans (p.toConcrete_edge_pos h 1)⟩
  · exact ⟨2, he.trans (p.toConcrete_edge_pos h 2)⟩
  · exact ⟨3, he.trans (p.toConcrete_edge_pos h 3)⟩

/-- Common-window touching is exactly torus touching in every volume in
which both plaquettes fit. -/
theorem WindowPlaquette.touches_iff_toConcrete
    {d N : ℕ} [NeZero N] (p q : WindowPlaquette d)
    (hp : p.Fits N) (hq : q.Fits N) :
    p.Touches q ↔ plaquetteTouches (p.toConcrete hp) (q.toConcrete hq) := by
  constructor
  · rintro ⟨i, j, hij⟩ hdisj
    have hpi := p.toConcrete_posEdge_mem_support hp i
    have hqj := q.toConcrete_posEdge_mem_support hq j
    exact (Finset.disjoint_left.mp hdisj hpi) (by
      simpa [hij] using hqj)
  · intro ht
    obtain ⟨e, hep, heq⟩ := Finset.not_disjoint_iff.mp ht
    obtain ⟨i, hi⟩ := p.exists_posEdge_eq_of_mem_support hp hep
    obtain ⟨j, hj⟩ := q.exists_posEdge_eq_of_mem_support hq heq
    refine ⟨i, j, WindowPosEdge.eq_of_toPosEdge_eq
      (p.posEdge_fits hp i) (q.posEdge_fits hq j) ?_⟩
    exact hi.symm.trans hj

open Classical in
/-- The positive-edge support of a realized plaquette set is exactly the
realization of its common-window edge support. -/
theorem WindowPlaquette.biUnion_support_realizedFinset
    {d N : ℕ} [NeZero N] {S : Finset (WindowPlaquette d)}
    (hS : ∀ p ∈ S, p.Fits N) :
    (WindowPlaquette.realizedFinset S hS).biUnion plaquetteSupport =
      WindowPosEdge.realizedFinset (WindowPlaquette.edgeSupport S)
        (WindowPlaquette.edgeSupport_fits hS) := by
  ext q
  constructor
  · intro hq
    obtain ⟨pN, hpN, hqp⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨p, hp⟩ :=
      WindowPlaquette.mem_realizedFinset_iff.mp hpN
    rw [← hp] at hqp
    obtain ⟨k, hk⟩ :=
      WindowPlaquette.exists_posEdge_eq_of_mem_support
        p.1 (hS p.1 p.2) hqp
    have heS : p.1.posEdge k ∈ WindowPlaquette.edgeSupport S := by
      apply Finset.mem_biUnion.mpr
      exact ⟨p.1, p.2,
        WindowPlaquette.mem_boundaryEdges_iff.mpr ⟨k, rfl⟩⟩
    apply WindowPosEdge.mem_realizedFinset_iff.mpr
    refine ⟨⟨p.1.posEdge k, heS⟩, ?_⟩
    simpa using hk.symm
  · intro hq
    obtain ⟨e, heq⟩ :=
      WindowPosEdge.mem_realizedFinset_iff.mp hq
    obtain ⟨p, hp, hep⟩ :=
      Finset.mem_biUnion.mp e.2
    obtain ⟨k, hk⟩ :=
      WindowPlaquette.mem_boundaryEdges_iff.mp hep
    apply Finset.mem_biUnion.mpr
    refine ⟨p.toConcrete (hS p hp), ?_, ?_⟩
    · apply WindowPlaquette.mem_realizedFinset_iff.mpr
      exact ⟨⟨p, hp⟩, rfl⟩
    · have hmem :=
        WindowPlaquette.toConcrete_posEdge_mem_support
          p (hS p hp) k
      rw [← heq]
      simpa [hk] using hmem

/-- Connectedness of a finite common-window plaquette set in its touching
graph. -/
def WindowPlaquette.IsConnectedPolymer {d : ℕ}
    (S : Finset (WindowPlaquette d)) : Prop :=
  (SimpleGraph.fromRel
    (fun p q : ↥S => p.1.Touches q.1)).Connected

/-- Realization gives an isomorphism of the two finite touching graphs. -/
noncomputable def WindowPlaquette.realizedGraphIso
    {d N : ℕ} [NeZero N] (S : Finset (WindowPlaquette d))
    (hS : ∀ p ∈ S, p.Fits N) :
    SimpleGraph.fromRel (fun p q : ↥S => p.1.Touches q.1) ≃g
      SimpleGraph.fromRel
        (fun p q : ↥(WindowPlaquette.realizedFinset S hS) =>
          plaquetteTouches p.1 q.1) where
  toEquiv := WindowPlaquette.realizedEquiv S hS
  map_rel_iff' := by
    intro p q
    rw [SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
    have hpq :
        p.1.Touches q.1 ↔
          plaquetteTouches
            ((WindowPlaquette.realizedEquiv S hS p).1)
            ((WindowPlaquette.realizedEquiv S hS q).1) := by
      change p.1.Touches q.1 ↔
        plaquetteTouches
          (p.1.toConcrete (hS p.1 p.2))
          (q.1.toConcrete (hS q.1 q.2))
      exact p.1.touches_iff_toConcrete q.1
        (hS p.1 p.2) (hS q.1 q.2)
    have hqp :
        q.1.Touches p.1 ↔
          plaquetteTouches
            ((WindowPlaquette.realizedEquiv S hS q).1)
            ((WindowPlaquette.realizedEquiv S hS p).1) := by
      change q.1.Touches p.1 ↔
        plaquetteTouches
          (q.1.toConcrete (hS q.1 q.2))
          (p.1.toConcrete (hS p.1 p.2))
      exact q.1.touches_iff_toConcrete p.1
        (hS q.1 q.2) (hS p.1 p.2)
    constructor
    · rintro ⟨hne, hrel⟩
      refine ⟨fun he => hne
        (congrArg (WindowPlaquette.realizedEquiv S hS) he), ?_⟩
      exact hrel.imp hpq.mpr hqp.mpr
    · rintro ⟨hne, hrel⟩
      refine ⟨fun he => hne
        ((WindowPlaquette.realizedEquiv S hS).injective he), ?_⟩
      exact hrel.imp hpq.mp hqp.mp

/-- Connected-polymer status is preserved and reflected by realization. -/
theorem WindowPlaquette.isConnectedPolymer_realizedFinset_iff
    {d N : ℕ} [NeZero N] (S : Finset (WindowPlaquette d))
    (hS : ∀ p ∈ S, p.Fits N) :
    WindowPlaquette.IsConnectedPolymer S ↔
      _root_.YangMills.IsConnectedPolymer
        (WindowPlaquette.realizedFinset S hS) :=
  (WindowPlaquette.realizedGraphIso S hS).connected_iff

/-! ## Quantitative seam avoidance -/

/-- A torus plaquette has margin `r` from every periodic seam when every
base coordinate is at least `r`, while the base coordinate, `r` further
steps, and the one-step plaquette thickness still lie strictly below `N`.

The asymmetric-looking final `+ 1` is the thickness of a plaquette.  This
normalization makes one touching step consume exactly one unit of margin. -/
def ConcretePlaquette.SiteMargin {d N : ℕ}
    (p : ConcretePlaquette d N) (r : ℕ) : Prop :=
  ∀ j, r ≤ (p.site j).val ∧ (p.site j).val + r + 1 < N

/-- Reading a shifted coordinate cannot move it more than one unit forward,
provided the source is away from the upper periodic seam. -/
private lemma FinBox.base_le_shift_apply_of_noWrap {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i j : Fin d) (h : (x i).val + 1 < N) :
    (x j).val ≤ ((x.shift i) j).val ∧
      ((x.shift i) j).val ≤ (x j).val + 1 := by
  by_cases hji : j = i
  · subst j
    simp [FinBox.shift, Nat.mod_eq_of_lt h]
  · simp [FinBox.shift, hji]

/-- Conversely, a positive shifted coordinate determines its unshifted
source up to one unit.  Positivity rules out the unique wrap-around case. -/
private lemma FinBox.shift_apply_bounds_base_of_pos {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i j : Fin d)
    (hpos : 0 < ((x.shift i) j).val) :
    ((x.shift i) j).val - 1 ≤ (x j).val ∧
      (x j).val ≤ ((x.shift i) j).val := by
  by_cases hji : j = i
  · subst j
    have hxle : (x i).val + 1 ≤ N := by omega
    have hxne : (x i).val + 1 ≠ N := by
      intro hx
      have : ((x.shift i) i).val = 0 := by
        simp [FinBox.shift, hx]
      omega
    have hxlt : (x i).val + 1 < N := by omega
    simp [FinBox.shift, Nat.mod_eq_of_lt hxlt]
  · simp [FinBox.shift, hji]

/-- Under one-step upper seam avoidance, every source coordinate of every
positive boundary edge lies between the plaquette base and base plus one. -/
private lemma plaquetteSupport_source_bounds_of_noWrap
    {d N : ℕ} [NeZero N] (p : ConcretePlaquette d N)
    (hupper : ∀ j, (p.site j).val + 1 < N)
    {e : PosEdge d N} (he : e ∈ plaquetteSupport p) (j : Fin d) :
    (p.site j).val ≤ (e.1.source j).val ∧
      (e.1.source j).val ≤ (p.site j).val + 1 := by
  rcases (mem_plaquetteSupport_iff p e).mp he with h | h | h | h
  · rw [h, (plaquette_pos_edges p).1]
    simp
  · rw [h, (plaquette_pos_edges p).2.1]
    exact FinBox.base_le_shift_apply_of_noWrap
      p.site p.dir1 j (hupper p.dir1)
  · rw [h, (plaquette_pos_edges p).2.2.1]
    exact FinBox.base_le_shift_apply_of_noWrap
      p.site p.dir2 j (hupper p.dir2)
  · rw [h, (plaquette_pos_edges p).2.2.2]
    simp

/-- If a positive boundary-edge source is nonzero, the plaquette base lies
between that source minus one and the source.  This is the inverse estimate
needed when the neighbouring plaquette is not yet known to avoid the seam. -/
private lemma plaquetteSupport_base_bounds_of_source_pos
    {d N : ℕ} [NeZero N] (p : ConcretePlaquette d N)
    {e : PosEdge d N} (he : e ∈ plaquetteSupport p) (j : Fin d)
    (hpos : 0 < (e.1.source j).val) :
    (e.1.source j).val - 1 ≤ (p.site j).val ∧
      (p.site j).val ≤ (e.1.source j).val := by
  rcases (mem_plaquetteSupport_iff p e).mp he with h | h | h | h
  · rw [h, (plaquette_pos_edges p).1]
    simp
  · rw [h, (plaquette_pos_edges p).2.1] at hpos ⊢
    exact FinBox.shift_apply_bounds_base_of_pos p.site p.dir1 j hpos
  · rw [h, (plaquette_pos_edges p).2.2.1] at hpos ⊢
    exact FinBox.shift_apply_bounds_base_of_pos p.site p.dir2 j hpos
  · rw [h, (plaquette_pos_edges p).2.2.2]
    simp

/-- **One contact consumes one margin unit.**  A plaquette touching one with
margin `r+1` has margin `r`.  In particular, a touching path of length `L`
starting with margin `L` never wraps around the torus. -/
theorem ConcretePlaquette.siteMargin_of_touches
    {d N r : ℕ} [NeZero N] {p q : ConcretePlaquette d N}
    (hp : p.SiteMargin (r + 1)) (htouch : plaquetteTouches p q) :
    q.SiteMargin r := by
  obtain ⟨e, hep, heq⟩ := Finset.not_disjoint_iff.mp htouch
  intro j
  have hpj := hp j
  have hpupper : ∀ k, (p.site k).val + 1 < N := by
    intro k
    have := (hp k).2
    omega
  have hpe :=
    plaquetteSupport_source_bounds_of_noWrap p hpupper hep j
  have hepos : 0 < (e.1.source j).val := by omega
  have hqe :=
    plaquetteSupport_base_bounds_of_source_pos q heq j hepos
  constructor <;> omega

/-- A larger seam margin implies every smaller one. -/
theorem ConcretePlaquette.SiteMargin.mono
    {d N r s : ℕ} {p : ConcretePlaquette d N}
    (hp : p.SiteMargin r) (h : s ≤ r) :
    p.SiteMargin s := by
  intro j
  have hpj := hp j
  constructor <;> omega

/-- Margin loss accumulates linearly along a touching walk. -/
theorem ConcretePlaquette.siteMargin_of_touchWalk
    {d N : ℕ} [NeZero N] {p q : ConcretePlaquette d N}
    (W : (touchGraph d N).Walk p q) {r : ℕ}
    (hp : p.SiteMargin (r + W.length)) :
    q.SiteMargin r := by
  induction W generalizing r with
  | nil =>
      simpa using hp
  | @cons u v w h W ih =>
      have ht : plaquetteTouches u v := by
        rw [touchGraph, SimpleGraph.fromRel_adj] at h
        rcases h.2 with huv | hvu
        · exact huv
        · exact plaquetteTouches_symm hvu
      have hu : u.SiteMargin ((r + W.length) + 1) := by
        simpa [SimpleGraph.Walk.length_cons, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using hp
      have hv : v.SiteMargin (r + W.length) :=
        ConcretePlaquette.siteMargin_of_touches hu ht
      exact ih hv

/-- Every plaquette of a connected polymer remains in the common window
when one marked plaquette has margin equal to the polymer cardinality. -/
theorem siteMargin_zero_of_mem_connected
    {d N : ℕ} [NeZero N]
    {c : Finset (ConcretePlaquette d N)} (hc : IsConnectedPolymer c)
    {p q : ConcretePlaquette d N} (hp : p ∈ c) (hq : q ∈ c)
    (hmargin : p.SiteMargin c.card) :
    q.SiteMargin 0 := by
  obtain ⟨W, hW⟩ := exists_touchWalk_of_connected hc hp hq
  have hshort : W.length ≤ c.card := Nat.le_of_lt hW
  exact ConcretePlaquette.siteMargin_of_touchWalk W
    (hmargin.mono (by simpa using hshort))

/-- Decode a torus plaquette into its ordinary natural-number coordinates.
This operation is always defined; `SiteMargin 0` is what makes the result
fit strictly and makes re-realization exact. -/
def ConcretePlaquette.toWindow {d N : ℕ}
    (p : ConcretePlaquette d N) : WindowPlaquette d where
  site := fun j => (p.site j).val
  dir1 := p.dir1
  dir2 := p.dir2
  hlt := p.hlt

/-- Margin zero is precisely enough for the decoded plaquette, including its
one-step thickness, to fit in the common window. -/
theorem ConcretePlaquette.toWindow_fits {d N : ℕ}
    {p : ConcretePlaquette d N} (hp : p.SiteMargin 0) :
    p.toWindow.Fits N := by
  intro j
  simpa [ConcretePlaquette.SiteMargin, ConcretePlaquette.toWindow]
    using (hp j).2

/-- Decoding and re-realizing a seam-avoiding plaquette is exact. -/
theorem ConcretePlaquette.toConcrete_toWindow {d N : ℕ}
    {p : ConcretePlaquette d N} (hp : p.SiteMargin 0) :
    p.toWindow.toConcrete (p.toWindow_fits hp) = p := by
  cases p with
  | mk site dir1 dir2 hlt =>
      congr 1

end YangMills
