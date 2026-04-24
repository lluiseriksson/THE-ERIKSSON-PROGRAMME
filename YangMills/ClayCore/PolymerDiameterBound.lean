/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.ClayAuthentic
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

/-!
# Phase 15a: Polymer diameter bound (Layer C2)

Oracle target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills

open scoped BigOperators
open Finset Real

/-! ### Embedding sites into Euclidean space -/

/-- Embed a lattice site `x : FinBox d N` into `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def siteEmbed {d N : ℕ} (x : FinBox d N) :
    EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => ((x i : ℤ) : ℝ))

theorem siteEmbed_apply {d N : ℕ} (x : FinBox d N) (i : Fin d) :
    (siteEmbed x) i = ((x i : ℤ) : ℝ) := by
  simp [siteEmbed]

/-- `siteLatticeDist` equals the Euclidean distance of the embeddings. -/
theorem siteLatticeDist_eq_dist {d N : ℕ} (p q : FinBox d N) :
    siteLatticeDist p q = dist (siteEmbed p) (siteEmbed q) := by
  rw [EuclideanSpace.dist_eq]
  unfold siteLatticeDist latticeDist siteDisplacement
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [siteEmbed_apply, siteEmbed_apply, Real.dist_eq]
  rw [sq_abs]
  push_cast
  ring

/-- Triangle inequality for `siteLatticeDist`. -/
theorem siteLatticeDist_triangle {d N : ℕ} (p q r : FinBox d N) :
    siteLatticeDist p r ≤ siteLatticeDist p q + siteLatticeDist q r := by
  rw [siteLatticeDist_eq_dist, siteLatticeDist_eq_dist, siteLatticeDist_eq_dist]
  exact dist_triangle _ _ _

/-- Self-distance vanishes. -/
theorem siteLatticeDist_self {d N : ℕ} (p : FinBox d N) :
    siteLatticeDist p p = 0 := by
  unfold siteLatticeDist
  have : siteDisplacement p p = 0 := by
    funext i; simp [siteDisplacement]
  rw [this, latticeDist_zero]

/-! ### Polymer connectivity -/

/-- A polymer `X` is (nearest-neighbour) connected if between any two of
its members there is an internal path whose consecutive plaquette sites
are within Euclidean distance `1`. -/
def PolymerConnected {d L : ℕ}
    (X : Finset (ConcretePlaquette d L)) : Prop :=
  ∀ p ∈ X, ∀ q ∈ X, ∃ path : List (ConcretePlaquette d L),
    path.head? = some p ∧
    path.getLast? = some q ∧
    path.Nodup ∧
    (∀ x ∈ path, x ∈ X) ∧
    List.IsChain (fun a b => siteLatticeDist a.site b.site ≤ 1) path

/-! ### Chain-length bound -/

/-- End-to-end Euclidean distance is bounded by `path.length - 1`
for an `IsChain`-connected path. -/
theorem siteLatticeDist_ischain_le {d L : ℕ} :
    ∀ (l : List (ConcretePlaquette d L)),
      List.IsChain (fun a b => siteLatticeDist a.site b.site ≤ 1) l →
      ∀ p q : ConcretePlaquette d L,
        l.head? = some p → l.getLast? = some q →
        siteLatticeDist p.site q.site ≤ ((l.length : ℝ) - 1) := by
  intro l
  induction l with
  | nil =>
      intro _ p q hh _
      simp at hh
  | cons a rest ih =>
      intro hchain p q hh hl
      have hap : a = p := by
        rw [List.head?_cons, Option.some.injEq] at hh
        exact hh
      subst hap
      match rest, hchain, hl with
      | [], _, hl =>
          -- [p] case: getLast? = some p, want p = q
          simp only [List.getLast?_singleton, Option.some.injEq] at hl
          subst hl
          rw [siteLatticeDist_self]
          simp
      | b :: rest', hchain, hl =>
          -- (p :: b :: rest') case
          cases hchain with
          | cons_cons hpb hchain' =>
              -- recursive: ih on (b :: rest')
              have hh' : (b :: rest').head? = some b := by simp
              have hl' : (b :: rest').getLast? = some q := by
                simpa [List.getLast?] using hl
              have hrec := ih hchain' b q hh' hl'
              have hbr : ((b :: rest').length : ℝ) - 1 = (rest'.length : ℝ) := by
                simp [List.length_cons]
              rw [hbr] at hrec
              have htri :
                  siteLatticeDist a.site q.site ≤
                    siteLatticeDist a.site b.site + siteLatticeDist b.site q.site :=
                siteLatticeDist_triangle _ _ _
              have hpbr : ((a :: b :: rest').length : ℝ) - 1 = 1 + (rest'.length : ℝ) := by
                simp [List.length_cons]; ring
              linarith

/-! ### Main polymer diameter bound -/

/-- **Phase 15a target (Layer C2).**
For a connected polymer `X`, the Euclidean distance between the sites of
any two of its plaquettes is at most `X.card - 1`. -/
theorem polymer_size_ge_site_dist_succ
    {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L)
    (X : Finset (ConcretePlaquette d L))
    (hpX : p ∈ X) (hqX : q ∈ X) (hconn : PolymerConnected X) :
    siteLatticeDist p.site q.site ≤ (X.card : ℝ) - 1 := by
  obtain ⟨path, hhead, hlast, hnodup, hsub, hchain⟩ := hconn p hpX q hqX
  have hpath_bound :
      siteLatticeDist p.site q.site ≤ ((path.length : ℝ) - 1) :=
    siteLatticeDist_ischain_le path hchain p q hhead hlast
  have hpath_card : path.toFinset.card = path.length :=
    List.toFinset_card_of_nodup hnodup
  have hpath_sub : path.toFinset ⊆ X := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact hsub x hx
  have hlen_le : path.length ≤ X.card := by
    calc path.length = path.toFinset.card := hpath_card.symm
      _ ≤ X.card := Finset.card_le_card hpath_sub
  have hineq : ((path.length : ℝ) - 1) ≤ ((X.card : ℝ) - 1) := by
    have : (path.length : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hlen_le
    linarith
  linarith

/-- Natural-number form of `polymer_size_ge_site_dist_succ`.
Any connected polymer containing `p` and `q` has cardinality at least
the ceiling of the lattice distance between them. -/
theorem ceil_siteLatticeDist_le_polymer_card
    {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L)
    (X : Finset (ConcretePlaquette d L))
    (hpX : p ∈ X) (hqX : q ∈ X) (hconn : PolymerConnected X) :
    ⌈siteLatticeDist p.site q.site⌉₊ ≤ X.card := by
  have hdist_card : siteLatticeDist p.site q.site ≤ (X.card : ℝ) := by
    have h := polymer_size_ge_site_dist_succ p q X hpX hqX hconn
    linarith
  exact Nat.ceil_le.mpr hdist_card

#print axioms ceil_siteLatticeDist_le_polymer_card

end YangMills
