/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.AnimalCount
import YangMills.RG.PolymerRemainder

/-!
# The lattice animal count `c_n ≤ Cⁿ` (gauge-RG, `hRpoly` campaign bricks P1b/P1c)

`docs/HRPOLY-CAMPAIGN-PLAN.md`.  Branch C of `hRpoly` (the geometric
summability `∑_{X⊇□} e^{−κ₀ d_M} ≤ K₀`) was reduced to the **lattice animal
count**: the number of connected size-`n` vertex sets containing a fixed root
is `≤ Cⁿ`.  This file closes that count, building on the walk-count engine
`card_walks_length_le_degree_pow` (P1a) and the detour splice
`exists_detour_walk` (P1b-ii engine), both in `RG/AnimalCount.lean`.

The construction is the classical spanning-walk encoding:

* **`exists_peel`** (P1b-i) — in an `S`-connected set with `≥ 2` vertices,
  the `r`-farthest vertex (max `mlen`, the minimal in-`S` walk length) is
  removable: deleting it keeps `S`-connectivity and it retains a neighbour
  inside.  (A max-distance vertex is never a cut vertex — proved via
  `takeUntil`/`dropUntil` length comparison, no spanning-tree object needed.)
* **`exists_spanning_closed_walk`** (P1b-ii) — by induction on `#S`, peeling
  the farthest vertex and splicing it back with `exists_detour_walk`, an
  `S`-connected set of `n` vertices gets a closed walk from `r` of length
  `2(n−1)` whose support is exactly `S`.
* **`animal_card_le`** (P1c) — each animal maps to its spanning closed walk;
  the map is injective (the animal is the walk's support); the walks of
  length `2(n−1)` number `≤ Δ^{2(n−1)}` by P1a.  Hence `c_n ≤ Δ^{2(n−1)}`.

Everything stays in the ambient graph `G` (no induced-subgraph type surgery),
matching `exists_detour_walk`.  Pure graph combinatorics; no measure theory,
no cluster expansion, no Bałaban/Dimock source.  **Consumer:** the polymer
model P2 instantiates this against `RG.polymer_weight_summability` (which
needs `c_n ≤ Cⁿ`).

**Source.**  Standard lattice-animal / self-avoiding-walk counting
(Madras–Slade); strategy/framing Lluis Eriksson (AIRR ARR-2026-4P13YY8RKA84FRBQ).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open Finset

namespace YangMills.RG

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {r : V}

/-- `w` stays inside `S`: every vertex it visits lies in `S`. -/
def IsSWalk (S : Finset V) {x : V} (w : G.Walk r x) : Prop := ∀ y ∈ w.support, y ∈ S

/-- Minimal length of an `S`-walk from `r` to `x` (junk `0` if none exists). -/
noncomputable def mlen (G : SimpleGraph V) (r : V) (S : Finset V) (x : V) : ℕ :=
  sInf {n | ∃ w : G.Walk r x, IsSWalk S w ∧ w.length = n}

/-- **Peel lemma** (P1b-i).  In an `S`-connected set with `≥ 2` vertices, the
`r`-farthest vertex `u` (max `mlen`) is removable: `S.erase u` is still
connected from `r`, and `u` has a neighbour in `S.erase u`.  The classical
fact that a max-distance vertex is not a cut vertex. -/
theorem exists_peel (S : Finset V) (hr : r ∈ S) (hcard : 2 ≤ S.card)
    (hconn : ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w) :
    ∃ u ∈ S, u ≠ r ∧ (∀ x ∈ S.erase u, ∃ w : G.Walk r x, IsSWalk (S.erase u) w)
      ∧ ∃ p ∈ S.erase u, G.Adj p u := by
  classical
  have hSne : S.Nonempty := ⟨r, hr⟩
  obtain ⟨u, huS, humax⟩ := S.exists_max_image (mlen G r S) hSne
  have hach : ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w ∧ w.length = mlen G r S x := by
    intro x hx
    obtain ⟨w0, hw0⟩ := hconn x hx
    have hne : {n | ∃ w : G.Walk r x, IsSWalk S w ∧ w.length = n}.Nonempty :=
      ⟨w0.length, w0, hw0, rfl⟩
    exact Nat.sInf_mem hne
  have hmin : ∀ {x : V} (w : G.Walk r x), IsSWalk S w → mlen G r S x ≤ w.length := by
    intro x w hw
    exact Nat.sInf_le ⟨w, hw, rfl⟩
  have hune : u ≠ r := by
    intro hur
    have hmlr : mlen G r S r = 0 := by
      have hnil : IsSWalk S (Walk.nil : G.Walk r r) := by
        intro y hy; rw [Walk.support_nil, List.mem_singleton] at hy; subst hy; exact hr
      have := hmin (Walk.nil : G.Walk r r) hnil
      simpa using this
    have hxexists : ∃ x ∈ S, x ≠ r := by
      obtain ⟨a, haS, b, hbS, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
      rcases eq_or_ne a r with rfl | har
      · refine ⟨b, hbS, ?_⟩; rintro rfl; exact hab rfl
      · exact ⟨a, haS, har⟩
    obtain ⟨x, hxS, hxr⟩ := hxexists
    have hle : mlen G r S x ≤ mlen G r S u := humax x hxS
    rw [hur, hmlr] at hle
    have hmx0 : mlen G r S x = 0 := Nat.le_zero.mp hle
    obtain ⟨w, _, hwlen⟩ := hach x hxS
    rw [hmx0] at hwlen
    exact hxr (Walk.eq_of_length_eq_zero hwlen).symm
  refine ⟨u, huS, hune, ?_, ?_⟩
  · intro z hz
    have hzS : z ∈ S := Finset.mem_of_mem_erase hz
    have hzu : z ≠ u := Finset.ne_of_mem_erase hz
    obtain ⟨P, hP, hPlen⟩ := hach z hzS
    refine ⟨P, ?_⟩
    intro y hy
    have hyS : y ∈ S := hP y hy
    rw [Finset.mem_erase]
    refine ⟨?_, hyS⟩
    intro huy
    have hu_supp : u ∈ P.support := huy ▸ hy
    have htake : IsSWalk S (P.takeUntil u hu_supp) := fun a ha =>
      hP a (P.support_takeUntil_subset hu_supp ha)
    have hmlu_le : mlen G r S u ≤ (P.takeUntil u hu_supp).length := hmin _ htake
    have hsum : (P.takeUntil u hu_supp).length + (P.dropUntil u hu_supp).length = P.length := by
      rw [← Walk.length_append, Walk.take_spec]
    have hmlz_le : mlen G r S z ≤ mlen G r S u := humax z hzS
    have hdrop0 : (P.dropUntil u hu_supp).length = 0 := by omega
    exact hzu (Walk.eq_of_length_eq_zero hdrop0).symm
  · obtain ⟨Pu, hPu, hPulen⟩ := hach u huS
    have hlenpos : 0 < Pu.length := by
      rcases Nat.eq_zero_or_pos Pu.length with h0 | hpos
      · exact absurd (Walk.eq_of_length_eq_zero h0) (Ne.symm hune)
      · exact hpos
    have hadj : G.Adj (Pu.getVert (Pu.length - 1)) u := by
      have h := Pu.adj_getVert_succ (by omega : Pu.length - 1 < Pu.length)
      rwa [Nat.sub_add_cancel hlenpos, Pu.getVert_length] at h
    refine ⟨Pu.getVert (Pu.length - 1), ?_, hadj⟩
    rw [Finset.mem_erase]
    exact ⟨hadj.ne, hPu _ (Pu.getVert_mem_support _)⟩

/-- **Spanning closed walk** (P1b-ii, full tour).  An `S`-connected set of `n`
vertices admits a closed walk from `r` whose vertex support is exactly `S`
and whose length is `2(n−1)`.  Induction on `#S`: peel the farthest vertex
(`exists_peel`), recurse, splice it back with `exists_detour_walk`. -/
theorem exists_spanning_closed_walk (S : Finset V) (hr : r ∈ S)
    (hconn : ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w) :
    ∃ w : G.Walk r r, w.support.toFinset = S ∧ w.length = 2 * (S.card - 1) := by
  classical
  suffices H : ∀ n : ℕ, ∀ T : Finset V, T.card = n → r ∈ T →
      (∀ x ∈ T, ∃ w : G.Walk r x, IsSWalk T w) →
      ∃ w : G.Walk r r, w.support.toFinset = T ∧ w.length = 2 * (T.card - 1) by
    exact H S.card S rfl hr hconn
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro T hcard hrT hconnT
    rcases lt_or_ge T.card 2 with hlt | hge
    · have hcard1 : T.card = 1 := by
        have : 1 ≤ T.card := Finset.card_pos.mpr ⟨r, hrT⟩
        omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
      have hra : r = a := by rw [ha] at hrT; exact Finset.mem_singleton.mp hrT
      subst hra
      refine ⟨Walk.nil, ?_, ?_⟩
      · simp [Walk.support_nil, ha]
      · simp [hcard1]
    · obtain ⟨u, huT, hune, hconn', p, hpT, hadj⟩ := exists_peel T hrT hge hconnT
      have hcard' : (T.erase u).card = T.card - 1 := Finset.card_erase_of_mem huT
      have hlt' : (T.erase u).card < n := by rw [hcard']; omega
      have hrT' : r ∈ T.erase u := Finset.mem_erase.mpr ⟨Ne.symm hune, hrT⟩
      obtain ⟨w', hw'supp, hw'len⟩ := IH (T.erase u).card hlt' (T.erase u) rfl hrT' hconn'
      have hp_supp : p ∈ w'.support := by
        rw [← List.mem_toFinset, hw'supp]; exact hpT
      obtain ⟨w, hwlen, hwsupp⟩ := exists_detour_walk w' hp_supp hadj
      refine ⟨w, ?_, ?_⟩
      · rw [hwsupp, hw'supp, Finset.insert_erase huT]
      · rw [hwlen, hw'len, hcard']; omega

/-- **Lattice animal count** (P1c).  Any family `A` of `S`-connected vertex
sets of size `n`, each containing the root `r`, on a graph of max degree
`≤ Δ`, has at most `Δ^{2(n−1)}` members — the geometric animal bound `c_n ≤ Cⁿ`
with `C = Δ²`.  Each animal maps to its spanning closed walk
(`exists_spanning_closed_walk`, length `2(n−1)`); the map is injective (the
animal is recovered as the walk's support); the closed walks are counted by
P1a (`card_walks_length_le_degree_pow`). -/
theorem animal_card_le [Fintype V] [DecidableRel G.Adj] (A : Finset (Finset V))
    {Δ n : ℕ} (hΔ : ∀ w, G.degree w ≤ Δ)
    (hA : ∀ S ∈ A, r ∈ S ∧ S.card = n ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w) :
    A.card ≤ Δ ^ (2 * (n - 1)) := by
  classical
  let f : Finset V → G.Walk r r := fun S =>
    if h : r ∈ S ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w then
      (exists_spanning_closed_walk S h.1 h.2).choose else Walk.nil
  have hfspec : ∀ S, (hP : r ∈ S ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w) →
      (f S).support.toFinset = S ∧ (f S).length = 2 * (S.card - 1) := by
    intro S hP
    have hch := (exists_spanning_closed_walk S hP.1 hP.2).choose_spec
    simp only [f, dif_pos hP]
    exact hch
  have hmem : ∀ S ∈ A, f S ∈ G.finsetWalkLength (2 * (n - 1)) r r := by
    intro S hS
    obtain ⟨hr', hSn, hconn⟩ := hA S hS
    rw [mem_finsetWalkLength_iff]
    have := (hfspec S ⟨hr', hconn⟩).2
    rw [hSn] at this
    exact this
  have hinj : Set.InjOn f A := by
    intro S₁ h₁ S₂ h₂ heq
    obtain ⟨hr1, _, hc1⟩ := hA S₁ h₁
    obtain ⟨hr2, _, hc2⟩ := hA S₂ h₂
    have e1 := (hfspec S₁ ⟨hr1, hc1⟩).1
    have e2 := (hfspec S₂ ⟨hr2, hc2⟩).1
    rw [← e1, ← e2, heq]
  calc A.card
      ≤ (G.finsetWalkLength (2 * (n - 1)) r r).card :=
        Finset.card_le_card_of_injOn f hmem hinj
    _ ≤ ∑ v, (G.finsetWalkLength (2 * (n - 1)) r v).card :=
        Finset.single_le_sum (f := fun v => (G.finsetWalkLength (2 * (n - 1)) r v).card)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ r)
    _ ≤ Δ ^ (2 * (n - 1)) := card_walks_length_le_degree_pow G hΔ (2 * (n - 1)) r

/-- The lattice animal count as an actual cardinal: the number of
`S`-connected size-`n` vertex sets containing the root `r` is `≤ Δ^{2(n−1)}`.
The `Fintype.card`/`Nat.card` shape consumed by
`polymer_weight_summability`'s `hcount` (branch C of `hRpoly`). -/
theorem rooted_connected_card_le [Fintype V] [DecidableRel G.Adj] {Δ n : ℕ}
    (hΔ : ∀ w, G.degree w ≤ Δ) :
    Nat.card {S : Finset V //
        r ∈ S ∧ S.card = n ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w}
      ≤ Δ ^ (2 * (n - 1)) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact animal_card_le _ hΔ (fun S hS => (Finset.mem_filter.mp hS).2)

/-- The animal count in the `c_n ≤ Cⁿ` form (`C = Δ²`), valid for `Δ ≥ 1` —
the exact input shape of `polymer_weight_summability`'s `hcount`. -/
theorem rooted_connected_card_le_pow [Fintype V] [DecidableRel G.Adj] {Δ n : ℕ}
    (hΔ : ∀ w, G.degree w ≤ Δ) (hΔ1 : 1 ≤ Δ) :
    Nat.card {S : Finset V //
        r ∈ S ∧ S.card = n ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w}
      ≤ (Δ ^ 2) ^ n := by
  refine le_trans (rooted_connected_card_le hΔ) ?_
  rw [← pow_mul]
  exact Nat.pow_le_pow_right hΔ1 (by omega)

/-- **Branch C of `hRpoly` closed**: the cluster-expansion geometric
summability `hwK`, discharged from the lattice animal count.  For a
bounded-degree graph (`Δ ≥ 1`) and decay `q` with `Δ²·q < 1`, the size-graded
weight sum over all `S`-connected rooted sets converges with the explicit
Kotecký–Preiss bound `(1 − Δ²q)⁻¹`.  This composes `rooted_connected_card_le_pow`
(the animal count `c_n ≤ (Δ²)ⁿ`) with `polymer_weight_summability`
(`RG/PolymerRemainder.lean`); the summability premise is free because the
polymer index type is finite.  This is the Dimock `∑_{X⊇□} e^{−κ₀ d(X)} ≤ K₀`
estimate with `q = e^{−κ₀}`, `K₀ = (1−Δ²q)⁻¹` — reduced to pure graph
combinatorics. -/
theorem rooted_connected_weight_summable [Fintype V] [DecidableRel G.Adj]
    {Δ : ℕ} {q : ℝ} (hΔ : ∀ w, G.degree w ≤ Δ) (hΔ1 : 1 ≤ Δ) (hq0 : 0 ≤ q)
    (hCq : (Δ : ℝ) ^ 2 * q < 1) :
    ∑' Y : {S : Finset V // r ∈ S ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w},
        q ^ (Y : Finset V).card ≤ (1 - (Δ : ℝ) ^ 2 * q)⁻¹ := by
  classical
  haveI : ∀ n, Fintype {Y : {S : Finset V //
      r ∈ S ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w} // (Y : Finset V).card = n} :=
    fun n => Fintype.ofFinite _
  refine polymer_weight_summability
    (ι := {S : Finset V // r ∈ S ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w})
    (fun Y => (Y : Finset V).card)
    hq0 (by positivity) hCq ?_ Summable.of_finite
  intro n
  have hcard_eq : Fintype.card {Y : {S : Finset V //
        r ∈ S ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w} // (Y : Finset V).card = n}
      = Nat.card {S : Finset V //
          r ∈ S ∧ S.card = n ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w} := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_congr
    refine (Equiv.subtypeSubtypeEquivSubtypeInter
      (p := fun S : Finset V => r ∈ S ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w)
      (q := fun S => S.card = n)).trans ?_
    exact Equiv.subtypeEquivRight (fun S => by tauto)
  rw [hcard_eq]
  calc ((Nat.card {S : Finset V //
          r ∈ S ∧ S.card = n ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w} : ℕ) : ℝ)
      ≤ (((Δ ^ 2) ^ n : ℕ) : ℝ) := by exact_mod_cast rooted_connected_card_le_pow hΔ hΔ1
    _ = ((Δ : ℝ) ^ 2) ^ n := by push_cast; ring

end YangMills.RG
