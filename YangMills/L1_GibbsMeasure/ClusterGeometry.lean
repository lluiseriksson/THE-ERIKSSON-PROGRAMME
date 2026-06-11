/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.LatticePolymerSystem
import YangMills.L1_GibbsMeasure.ConnectedEntropy
import YangMills.KP.SharpShell
import YangMills.KP.ClusterTail

/-!
# Cluster geometry, step B3 — connecting clusters are large

Half B of `docs/CLUSTER-CORRELATION-PLAN.md`: the geometric input of
the correlation decay.  A cluster of the connected lattice gas whose
support meets two distant plaquettes must contain many plaquettes:

* `touchGraph` — the global plaquette-touching graph and its distance;
* `touchGraph_dist_lt_card_of_connected` (B3a) — within one connected
  polymer, touching-distance is bounded by the plaquette count;
* `exists_touching_of_not_disjoint` (B3b) — overlapping supports
  produce a touching pair (the crossing step between incompatible
  polymers).

The cluster-level bound (B3c: distance ≤ linear in total size along
incompatibility paths) composes these and feeds the size-tail bound
`connectedLattice_pinned_tail_volumeUniform` (Half A).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open KP

variable {d N : ℕ} [NeZero N]

/-- The **global plaquette-touching graph**. -/
def touchGraph (d N : ℕ) [NeZero N] :
    SimpleGraph (ConcretePlaquette d N) :=
  SimpleGraph.fromRel plaquetteTouches

open Classical in
/-- **B3a: within-polymer distances are bounded by the size** —
a connected polymer realizes touching-paths between its members. -/
lemma touchGraph_dist_lt_card_of_connected
    {c : Finset (ConcretePlaquette d N)} (hc : IsConnectedPolymer c)
    {p q : ConcretePlaquette d N} (hp : p ∈ c) (hq : q ∈ c) :
    (touchGraph d N).dist p q < c.card := by
  classical
  have hadj : ∀ {x y : ↥c},
      (SimpleGraph.fromRel
        (fun p q : ↥c => plaquetteTouches p.1 q.1)).Adj x y →
      (touchGraph d N).Adj x.1 y.1 := by
    intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    show (SimpleGraph.fromRel plaquetteTouches).Adj x.1 y.1
    rw [SimpleGraph.fromRel_adj]
    exact ⟨fun h => hxy.1 (Subtype.ext h), hxy.2⟩
  have hdist : (SimpleGraph.fromRel
      (fun p q : ↥c => plaquetteTouches p.1 q.1)).dist
        ⟨p, hp⟩ ⟨q, hq⟩ < Fintype.card ↥c :=
    connected_dist_lt_card hc _ _
  obtain ⟨w, hw⟩ :=
    (hc.preconnected ⟨p, hp⟩ ⟨q, hq⟩).exists_walk_length_eq_dist
  have h1 : (touchGraph d N).dist p q
      ≤ (w.map ⟨Subtype.val, hadj⟩).length :=
    SimpleGraph.dist_le _
  rw [SimpleGraph.Walk.length_map, hw] at h1
  calc (touchGraph d N).dist p q
      ≤ (SimpleGraph.fromRel
          (fun p q : ↥c => plaquetteTouches p.1 q.1)).dist
            ⟨p, hp⟩ ⟨q, hq⟩ := h1
    _ < Fintype.card ↥c := hdist
    _ = c.card := Fintype.card_coe c

open Classical in
/-- **B3b: the crossing** — overlapping edge supports produce a
touching pair of plaquettes. -/
lemma exists_touching_of_not_disjoint
    {c c' : Finset (ConcretePlaquette d N)}
    (h : ¬ Disjoint (c.biUnion plaquetteSupport)
      (c'.biUnion plaquetteSupport)) :
    ∃ p ∈ c, ∃ q ∈ c', plaquetteTouches p q := by
  obtain ⟨e, he, he'⟩ := Finset.not_disjoint_iff.mp h
  obtain ⟨p, hp, hep⟩ := Finset.mem_biUnion.mp he
  obtain ⟨q, hq, heq⟩ := Finset.mem_biUnion.mp he'
  exact ⟨p, hp, q, hq,
    fun hd => (Finset.disjoint_left.mp hd hep) heq⟩

open Classical in
/-- B3a, walk form: connected polymers realize touching-walks of
length below their size. -/
lemma exists_touchWalk_of_connected
    {c : Finset (ConcretePlaquette d N)} (hc : IsConnectedPolymer c)
    {p q : ConcretePlaquette d N} (hp : p ∈ c) (hq : q ∈ c) :
    ∃ W : (touchGraph d N).Walk p q, W.length < c.card := by
  classical
  have hadj : ∀ {x y : ↥c},
      (SimpleGraph.fromRel
        (fun p q : ↥c => plaquetteTouches p.1 q.1)).Adj x y →
      (touchGraph d N).Adj x.1 y.1 := by
    intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    show (SimpleGraph.fromRel plaquetteTouches).Adj x.1 y.1
    rw [SimpleGraph.fromRel_adj]
    exact ⟨fun h => hxy.1 (Subtype.ext h), hxy.2⟩
  obtain ⟨w, hw⟩ :=
    (hc.preconnected ⟨p, hp⟩ ⟨q, hq⟩).exists_walk_length_eq_dist
  refine ⟨w.map ⟨Subtype.val, hadj⟩, ?_⟩
  rw [SimpleGraph.Walk.length_map, hw]
  calc (SimpleGraph.fromRel
      (fun p q : ↥c => plaquetteTouches p.1 q.1)).dist
        ⟨p, hp⟩ ⟨q, hq⟩
      < Fintype.card ↥c := connected_dist_lt_card hc _ _
    _ = c.card := Fintype.card_coe c

set_option maxHeartbeats 1600000 in
open Classical in
/-- **B3c, the walk construction:** along an incompatibility path
through a cluster of the connected gas, touching-walks thread the
polymers — with total length bounded by the visited sizes plus the
number of crossings. -/
lemma exists_walk_through_cluster {G : Type*} [Group G]
    [MeasurableSpace G] [NeZero d]
    (μ : MeasureTheory.Measure G) (pe : G → ℝ) (β : ℝ) {n : ℕ}
    {X : Fin n → (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β).Polymer} :
    ∀ {i j : Fin n}
      (w : (KP.incompGraph (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β) X).Walk i j),
      w.IsPath →
      ∀ p ∈ (X i).1, ∀ q ∈ (X j).1,
      ∃ W : (touchGraph d N).Walk p q,
        W.length ≤ (∑ i' ∈ w.support.toFinset, (X i').1.card)
          + w.length := by
  intro i j w
  induction w with
  | @nil u =>
      intro _ p hp q hq
      obtain ⟨W, hW⟩ :=
        exists_touchWalk_of_connected (X u).2.2 hp hq
      refine ⟨W, ?_⟩
      rw [SimpleGraph.Walk.support_nil, SimpleGraph.Walk.length_nil]
      simp only [List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq, Finset.sum_singleton]
      omega
  | @cons u v j' h w' ih =>
      intro hpath p hp q hq
      rw [SimpleGraph.Walk.cons_isPath_iff] at hpath
      obtain ⟨hw'path, hinotin⟩ := hpath
      have hinc : (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β).incomp (X u) (X v) :=
        ((KP.incompGraph_adj _ X u v).mp h).2
      obtain ⟨p', hp', q', hq', htouch⟩ :=
        exists_touching_of_not_disjoint hinc
      obtain ⟨W₁, hW₁⟩ :=
        exists_touchWalk_of_connected (X u).2.2 hp hp'
      have hop : ∃ W₂ : (touchGraph d N).Walk p' q',
          W₂.length ≤ 1 := by
        by_cases hpq : p' = q'
        · subst hpq
          exact ⟨SimpleGraph.Walk.nil, Nat.zero_le 1⟩
        · have hadj2 : (touchGraph d N).Adj p' q' := by
            show (SimpleGraph.fromRel plaquetteTouches).Adj p' q'
            rw [SimpleGraph.fromRel_adj]
            exact ⟨hpq, Or.inl htouch⟩
          refine ⟨SimpleGraph.Walk.cons hadj2 SimpleGraph.Walk.nil,
            ?_⟩
          rw [SimpleGraph.Walk.length_cons,
            SimpleGraph.Walk.length_nil]
      obtain ⟨W₂, hW₂⟩ := hop
      obtain ⟨W₃, hW₃⟩ := ih hw'path q' hq' q hq
      refine ⟨(W₁.append W₂).append W₃, ?_⟩
      rw [SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.support_cons]
      rw [List.toFinset_cons,
        Finset.sum_insert (fun hmem =>
          hinotin (List.mem_toFinset.mp hmem))]
      omega

open Classical in
/-- **B3c (the connecting bound):** plaquettes joined through a cluster
of the connected lattice gas are within touching-distance twice the
total plaquette count of the cluster. -/
theorem cluster_dist_le {G : Type*} [Group G]
    [MeasurableSpace G] [NeZero d]
    (μ : MeasureTheory.Measure G) (pe : G → ℝ) (β : ℝ) {n : ℕ}
    {X : Fin n → (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β).Polymer}
    (hX : KP.IsCluster (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β) X)
    {i₀ j₀ : Fin n} {p q : ConcretePlaquette d N}
    (hp : p ∈ (X i₀).1) (hq : q ∈ (X j₀).1) :
    (touchGraph d N).dist p q ≤ 2 * ∑ i, (X i).1.card := by
  classical
  obtain ⟨w⟩ := hX.preconnected i₀ j₀
  obtain ⟨W, hW⟩ := exists_walk_through_cluster μ pe β
    w.bypass (SimpleGraph.Walk.bypass_isPath w) p hp q hq
  refine le_trans (SimpleGraph.dist_le W) (le_trans hW ?_)
  have h1 : ∑ i' ∈ w.bypass.support.toFinset, (X i').1.card
      ≤ ∑ i', (X i').1.card :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h2 : w.bypass.length < n := by
    have := (SimpleGraph.Walk.bypass_isPath w).length_lt
    rwa [Fintype.card_fin] at this
  have h3 : n ≤ ∑ i', (X i').1.card := by
    calc n = ∑ _i' : Fin n, 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_univ, Fintype.card_fin]
      _ ≤ ∑ i', (X i').1.card :=
          Finset.sum_le_sum fun i' _ =>
            Finset.card_pos.mpr (X i').2.1
  omega

set_option maxHeartbeats 800000 in
open Classical in
/-- **The connecting-sum domination:** pinned cluster sums restricted
to clusters touching a distant plaquette are dominated by the
size-restricted pinned weights — B3's geometry feeds Half A's tail. -/
lemma connecting_pinned_le_GE {G : Type*} [Group G]
    [MeasurableSpace G] [NeZero d]
    (μ : MeasureTheory.Measure G) (pe : G → ℝ) (β : ℝ)
    {p q : ConcretePlaquette d N}
    (c : (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β).Polymer)
    (hp : p ∈ c.1) (n : ℕ) :
    (((n + 1).factorial : ℝ))⁻¹ *
      ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
        (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β).Polymer)).filter
        (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
        |((KP.ursell (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β) X : ℤ) : ℝ)| *
          ∏ i, ‖(connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β).activity (X i)‖
    ≤ KP.pinnedClusterWeightGE (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β)
        (fun c' => c'.1.card) c ((touchGraph d N).dist p q / 2) n := by
  classical
  unfold KP.pinnedClusterWeightGE
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- restrict to genuine clusters (non-clusters contribute zero)
  rw [show ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
      (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β).Polymer)).filter
      (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
      |((KP.ursell (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β) X : ℤ) : ℝ)| *
        ∏ i, ‖(connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β).activity (X i)‖
    = ∑ X ∈ ((Finset.univ : Finset (Fin (n + 1) →
        (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β).Polymer)).filter
        (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1)).filter
        (fun X => KP.IsCluster (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β) X),
        |((KP.ursell (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β) X : ℤ) : ℝ)| *
          ∏ i, ‖(connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β).activity (X i)‖
    from (Finset.sum_filter_of_ne fun X _ hne => by
      by_contra hnc
      exact hne (by
        rw [KP.ursell_eq_zero_of_not_isCluster _ X hnc]
        simp)).symm]
  -- the cluster filter lands in the size-restricted filter
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun X _ _ =>
    mul_nonneg (abs_nonneg _)
      (Finset.prod_nonneg fun i _ => norm_nonneg _)
  intro X hX
  rw [Finset.mem_filter, Finset.mem_filter] at hX
  obtain ⟨⟨-, hX0, j, hqj⟩, hclus⟩ := hX
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hX0, ?_⟩
  have hp0 : p ∈ (X 0).1 := by rw [hX0]; exact hp
  have hdist := cluster_dist_le μ pe β hclus hp0 hqj
  have hsz : ∑ i, (fun c' : (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β).Polymer => c'.1.card) (X i)
      = ∑ i, (X i).1.card := rfl
  omega

set_option maxHeartbeats 1600000 in
open Classical in
/-- **THE CONNECTING-CLUSTER DECAY (volume-uniform):** the total pinned
cluster sum over polymers through `p`, restricted to clusters touching
`q`, decays exponentially in the touching-distance — with every
constant depending only on `d`, `B`, `β`, `t`, `ε`.  This is the IR
decay mechanism of the correlation chain, fully composed. -/
theorem connecting_cluster_decay {G : Type*} [Group G]
    [MeasurableSpace G] [NeZero d]
    (μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)))) ≤ t)
    (p q : ConcretePlaquette d N) :
    ∑ c ∈ (Finset.univ : Finset (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β).Polymer).filter
        (fun c => p ∈ c.1),
      ∑' n : ℕ, (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
          (connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β).Polymer)).filter
          (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
          |((KP.ursell (connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β) X : ℤ) : ℝ)| *
            ∏ i, ‖(connectedLatticePolymerSystem
              (d := d) (N := N) μ pe β).activity (X i)‖
    ≤ Real.exp (-(ε * (((touchGraph d N).dist p q / 2 : ℕ) : ℝ))) *
        (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)))) := by
  classical
  set L : ℕ := (touchGraph d N).dist p q / 2 with hL
  set x : ℝ := (Real.exp (|β| * B) - 1) * Real.exp (t + ε) with hxdef
  have hx : (0 : ℝ) ≤ x := by
    have h1 : (1 : ℝ) ≤ Real.exp (|β| * B) := by
      rw [← Real.exp_zero]
      refine Real.exp_le_exp.mpr ?_
      have hB : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hpe 1)
      positivity
    have : (0 : ℝ) ≤ Real.exp (|β| * B) - 1 := by linarith
    positivity
  have hcrit := connectedLatticePolymerSystem_tilt_kpCriterion_volumeUniform
    (d := d) (N := N) μ hpe β t ε ht0 hr hsmall
  -- per polymer through p: the connecting tail
  have hper : ∀ c ∈ (Finset.univ : Finset (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β).Polymer).filter (fun c => p ∈ c.1),
      (∑' n : ℕ, (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
          (connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β).Polymer)).filter
          (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
          |((KP.ursell (connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β) X : ℤ) : ℝ)| *
            ∏ i, ‖(connectedLatticePolymerSystem
              (d := d) (N := N) μ pe β).activity (X i)‖)
      ≤ Real.exp (-(ε * L)) *
          (Real.exp (ε * (c.1.card : ℝ)) *
            ‖(connectedLatticePolymerSystem
              (d := d) (N := N) μ pe β).activity c‖ *
            Real.exp (t * (c.1.card : ℝ))) := by
    intro c hc
    have hp := (Finset.mem_filter.mp hc).2
    have htail := KP.pinned_cluster_tail_summable
      (connectedLatticePolymerSystem (d := d) (N := N) μ pe β)
      (fun c' => c'.1.card) hε0 hcrit c L
    have hterm := fun n => connecting_pinned_le_GE
      (q := q) μ pe β c hp n
    have hnn : ∀ n : ℕ, 0 ≤ (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
          (connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β).Polymer)).filter
          (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
          |((KP.ursell (connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β) X : ℤ) : ℝ)| *
            ∏ i, ‖(connectedLatticePolymerSystem
              (d := d) (N := N) μ pe β).activity (X i)‖ := by
      intro n
      refine mul_nonneg (by positivity)
        (Finset.sum_nonneg fun X _ => mul_nonneg (abs_nonneg _)
          (Finset.prod_nonneg fun i _ => norm_nonneg _))
    have hsumm : Summable (fun n : ℕ =>
        (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
          (connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β).Polymer)).filter
          (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
          |((KP.ursell (connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β) X : ℤ) : ℝ)| *
            ∏ i, ‖(connectedLatticePolymerSystem
              (d := d) (N := N) μ pe β).activity (X i)‖) :=
      Summable.of_nonneg_of_le hnn hterm htail.1
    exact le_trans
      (Summable.tsum_le_tsum hterm hsumm htail.1) htail.2
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  -- the through-p sum is volume-free
  calc ∑ c ∈ (Finset.univ : Finset (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β).Polymer).filter
        (fun c => p ∈ c.1),
        Real.exp (ε * (c.1.card : ℝ)) *
          ‖(connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β).activity c‖ *
          Real.exp (t * (c.1.card : ℝ))
      ≤ ∑ c ∈ (Finset.univ : Finset (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β).Polymer).filter
          (fun c => p ∈ c.1),
          x ^ c.1.card := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 := norm_connectedLatticePolymerSystem_activity_le
          (d := d) (N := N) μ hpe β c
        have h2 : Real.exp ((t + ε) * (c.1.card : ℝ))
            = Real.exp (t + ε) ^ c.1.card := by
          rw [mul_comm, ← Real.exp_nat_mul]
        have hcomb : Real.exp (ε * (c.1.card : ℝ)) *
            Real.exp (t * (c.1.card : ℝ))
            = Real.exp ((t + ε) * (c.1.card : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc Real.exp (ε * (c.1.card : ℝ)) *
            ‖(connectedLatticePolymerSystem
              (d := d) (N := N) μ pe β).activity c‖ *
            Real.exp (t * (c.1.card : ℝ))
            = ‖(connectedLatticePolymerSystem
                (d := d) (N := N) μ pe β).activity c‖ *
              (Real.exp (ε * (c.1.card : ℝ)) *
                Real.exp (t * (c.1.card : ℝ))) := by ring
          _ = ‖(connectedLatticePolymerSystem
                (d := d) (N := N) μ pe β).activity c‖ *
              Real.exp (t + ε) ^ c.1.card := by rw [hcomb, h2]
          _ ≤ (Real.exp (|β| * B) - 1) ^ c.1.card *
              Real.exp (t + ε) ^ c.1.card :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = x ^ c.1.card := by rw [hxdef, mul_pow]
    _ ≤ x / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x) :=
        sum_connectedPolymers_through_le (d := d) (N := N) p x hx
          (by rw [hxdef] at *; exact hr)

/-! ### Touching components of plaquette sets (polymer representation,
step 2 — the `Z = Ξ` gate of `docs/CLUSTER-CORRELATION-PLAN.md` §2e) -/

open Classical in
/-- The **touching components** of a plaquette set: the parts of the
reachability partition of its internal touching graph, coerced back to
plaquette sets. -/
noncomputable def plaqComponents (S : Finset (ConcretePlaquette d N)) :
    Finset (Finset (ConcretePlaquette d N)) := by
  classical
  exact (Finpartition.ofSetoid
    (SimpleGraph.fromRel
      (fun p q : ↥S => plaquetteTouches p.1 q.1)).reachableSetoid).parts.image
    (fun B => B.image Subtype.val)

open Classical in
lemma plaqComponents_nonempty {S : Finset (ConcretePlaquette d N)}
    {c : Finset (ConcretePlaquette d N)} (hc : c ∈ plaqComponents S) :
    c.Nonempty := by
  classical
  unfold plaqComponents at hc
  rw [Finset.mem_image] at hc
  obtain ⟨B, hB, rfl⟩ := hc
  exact ((Finpartition.ofSetoid _).nonempty_of_mem_parts hB).image _

open Classical in
lemma plaqComponents_subset {S : Finset (ConcretePlaquette d N)}
    {c : Finset (ConcretePlaquette d N)} (hc : c ∈ plaqComponents S) :
    c ⊆ S := by
  classical
  unfold plaqComponents at hc
  rw [Finset.mem_image] at hc
  obtain ⟨B, _, rfl⟩ := hc
  intro p hp
  rw [Finset.mem_image] at hp
  obtain ⟨x, _, rfl⟩ := hp
  exact x.2

open Classical in
/-- The components cover the set. -/
lemma plaqComponents_biUnion (S : Finset (ConcretePlaquette d N)) :
    (plaqComponents S).biUnion id = S := by
  classical
  ext p
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hp⟩
    exact plaqComponents_subset hc hp
  · intro hp
    refine ⟨((Finpartition.ofSetoid
        (SimpleGraph.fromRel (fun p q : ↥S =>
          plaquetteTouches p.1 q.1)).reachableSetoid).part
            ⟨p, hp⟩).image Subtype.val, ?_, ?_⟩
    · unfold plaqComponents
      rw [Finset.mem_image]
      exact ⟨_, (Finpartition.ofSetoid _).part_mem.mpr
        (Finset.mem_univ _), rfl⟩
    · show p ∈ Finset.image _ _
      rw [Finset.mem_image]
      exact ⟨⟨p, hp⟩, (Finpartition.ofSetoid _).mem_part
        (Finset.mem_univ _), rfl⟩

open Classical in
/-- Distinct components never touch. -/
lemma plaqComponents_not_touching {S : Finset (ConcretePlaquette d N)}
    {c c' : Finset (ConcretePlaquette d N)}
    (hc : c ∈ plaqComponents S) (hc' : c' ∈ plaqComponents S)
    (hne : c ≠ c') :
    ∀ p ∈ c, ∀ q ∈ c', ¬ plaquetteTouches p q := by
  classical
  unfold plaqComponents at hc hc'
  rw [Finset.mem_image] at hc hc'
  obtain ⟨B, hB, rfl⟩ := hc
  obtain ⟨B', hB', rfl⟩ := hc'
  intro p hp q hq htouch
  rw [Finset.mem_image] at hp hq
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨y, hy, rfl⟩ := hq
  -- same reachability class
  have hreach : (SimpleGraph.fromRel (fun p q : ↥S =>
      plaquetteTouches p.1 q.1)).Reachable x y := by
    by_cases hxy : x = y
    · rw [hxy]
    · refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.fromRel_adj]
      exact ⟨hxy, Or.inl htouch⟩
  have hclass : B = B' := by
    have h1 := (Finpartition.ofSetoid _).part_eq_of_mem hB hx
    have h2 := (Finpartition.ofSetoid _).part_eq_of_mem hB' hy
    have h3 : y ∈ (Finpartition.ofSetoid
        (SimpleGraph.fromRel (fun p q : ↥S =>
          plaquetteTouches p.1 q.1)).reachableSetoid).part x :=
      Finpartition.mem_part_ofSetoid_iff_rel.mpr hreach
    have h4 := (Finpartition.ofSetoid _).part_eq_of_mem
      ((Finpartition.ofSetoid _).part_mem.mpr (Finset.mem_univ x)) h3
    rw [← h1, ← h2, ← h4]
  exact hne (by rw [hclass])

open Classical in
/-- Distinct components have disjoint edge supports — they are
compatible as polymers. -/
lemma plaqComponents_support_disjoint
    {S : Finset (ConcretePlaquette d N)}
    {c c' : Finset (ConcretePlaquette d N)}
    (hc : c ∈ plaqComponents S) (hc' : c' ∈ plaqComponents S)
    (hne : c ≠ c') :
    Disjoint (c.biUnion plaquetteSupport)
      (c'.biUnion plaquetteSupport) := by
  by_contra hnd
  obtain ⟨p, hp, q, hq, htouch⟩ := exists_touching_of_not_disjoint hnd
  exact plaqComponents_not_touching hc hc' hne p hp q hq htouch

end YangMills
