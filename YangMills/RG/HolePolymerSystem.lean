/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.KP.Basic
import YangMills.KP.Criterion
import YangMills.KP.SharpKP
import YangMills.KP.Ursell
import YangMills.RG.ModifiedMetric

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

/-- The **touching hard-core holes-respected polymer system** on the cube lattice.
    Polymers are nonempty, connected finsets of cubes that respect the hole family H.
    Two polymers are incompatible if they overlap or touch (share a boundary of any dimension).

    Audit note on the incompatibility relation:
    Adjacency/touching (sharing a boundary edge in `cubeAdj`) is mathematically required
    for the hard-core lattice-polymer system used by the existing local-KP consumers.
    It is deliberately stronger/geometric: disjoint but adjacent polymers are also
    incompatible.

    Dimock II Appendix F uses a different with-holes cluster relation: polymers are
    `Ω`-connected when their active parts intersect inside `Ω`
    (`X₁ ∩ X₂ ∩ Ω ≠ ∅`), and `Ω`-disjoint need not mean disjoint.  The parallel
    `omegaHolePolymerSystem` below records that source-facing relation without
    changing the already-verified touching-system consumers. -/
noncomputable def holePolymerSystem {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) :
    KP.PolymerSystem where
  Polymer := { X : Finset (Cube d L) // X.Nonempty ∧ cubeConnected X ∧ polymerWithHoles H X }
  incomp X Y := ¬ Disjoint X.val Y.val ∨ ∃ x ∈ X.val, ∃ y ∈ Y.val, (cubeAdj d L).Adj x y
  incomp_symm := by
    intro X Y h
    rcases h with hd | ⟨x, hx, y, hy, hadj⟩
    · left
      rwa [disjoint_comm]
    · right
      exact ⟨y, hy, x, hx, hadj.symm⟩
  incomp_self := by
    intro X
    left
    intro hd
    have hne := X.property.left
    obtain ⟨x, hx⟩ := hne
    have h_ne := Finset.disjoint_iff_ne.mp hd x hx x hx
    exact h_ne rfl
  activity X := z X.val

noncomputable instance {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) :
    Fintype (holePolymerSystem H z).Polymer :=
  inferInstanceAs (Fintype { X : Finset (Cube d L) // X.Nonempty ∧ cubeConnected X ∧ polymerWithHoles H X })

/-- The **source-facing active with-holes polymer system**.

This is the discrete form of Dimock II Appendix F's `Ω`-connected relation.
For a polymer `X`, `skeleton H X = X ∩ Ω` is its active part outside the
large-field holes.  Two active polymers are incompatible exactly when these
active parts intersect.  We restrict the polymer type to nonempty skeletons so
that hard-core self-incompatibility is true in `KP.PolymerSystem`; the Appendix
F sums of interest are likewise pinned to polymers meeting the active region.

This definition is intentionally separate from `holePolymerSystem`: the latter
is the already-verified touching hard-core system, while this one is the
source-shaped target for future Appendix-F consumers. -/
noncomputable def omegaHolePolymerSystem {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) : KP.PolymerSystem where
  Polymer := { X : Finset (Cube d L) //
    X.Nonempty ∧ cubeConnected X ∧ polymerWithHoles H X ∧ (skeleton H X).Nonempty }
  incomp X Y := ¬ Disjoint (skeleton H X.val) (skeleton H Y.val)
  incomp_symm := by
    intro X Y h
    rwa [disjoint_comm]
  incomp_self := by
    intro X hd
    obtain ⟨x, hx⟩ := X.property.right.right.right
    have h_ne := Finset.disjoint_iff_ne.mp hd x hx x hx
    exact h_ne rfl
  activity X := z X.val

noncomputable instance {d L : ℕ} [NeZero L] (H : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ) :
    Fintype (omegaHolePolymerSystem H z).Polymer :=
  inferInstanceAs (Fintype { X : Finset (Cube d L) //
    X.Nonempty ∧ cubeConnected X ∧ polymerWithHoles H X ∧ (skeleton H X).Nonempty })

/-- The `omegaHolePolymerSystem` incompatibility is precisely intersection of
the active skeletons. -/
theorem omegaHolePolymerSystem_incomp_iff {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (X Y : (omegaHolePolymerSystem H z).Polymer) :
    (omegaHolePolymerSystem H z).incomp X Y ↔
      ¬ Disjoint (skeleton H X.val) (skeleton H Y.val) :=
  Iff.rfl

/-- Elementwise form of Appendix F's `Ω`-connected relation:
two active hole-polymers are incompatible iff their skeletons share a cube. -/
theorem omegaHolePolymerSystem_incomp_iff_exists {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (X Y : (omegaHolePolymerSystem H z).Polymer) :
    (omegaHolePolymerSystem H z).incomp X Y ↔
      ∃ s, s ∈ skeleton H X.val ∧ s ∈ skeleton H Y.val := by
  constructor
  · intro h
    rw [omegaHolePolymerSystem_incomp_iff] at h
    rw [Finset.disjoint_iff_inter_eq_empty] at h
    obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr h
    rw [Finset.mem_inter] at hs
    exact ⟨s, hs.1, hs.2⟩
  · rintro ⟨s, hsX, hsY⟩
    rw [omegaHolePolymerSystem_incomp_iff]
    intro hd
    have h_ne := Finset.disjoint_iff_ne.mp hd s hsX s hsY
    exact h_ne rfl

/-- The activity sum of all connected, hole-respecting polymers containing a fixed root r in their skeleton. -/
noncomputable def rootedHolePolymerSum {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (r : Cube d L) : ℂ :=
  ∑' X : { P : (holePolymerSystem H z).Polymer // r ∈ skeleton H P.1 }, (holePolymerSystem H z).activity X.1

/-- **Discrete modified-metric polymer activity sum bound:**
    If the activity of each polymer is bounded exponentially by the modified metric,
    then the total activity sum of polymers containing r in their skeleton converges volume-uniformly. -/
theorem rootedHolePolymerSum_bound {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (r : Cube d L)
    (q : ℝ) (h_bound : ∀ X : (holePolymerSystem H z).Polymer, ‖(holePolymerSystem H z).activity X‖ ≤ q ^ (discreteModifiedMetric H X.1 + 1))
    (hdisj : ∀ H₁ ∈ H.holes, ∀ H₂ ∈ H.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) H.holes)
    (hholes_ne : ∀ H₀ ∈ H.holes, H₀.Nonempty)
    (hq0 : 0 ≤ q)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)) < 1) :
    ‖rootedHolePolymerSum H z r‖
      ≤ (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)))⁻¹ := by
  classical
  unfold rootedHolePolymerSum
  have h_norm : ‖∑' X : { P : (holePolymerSystem H z).Polymer // r ∈ skeleton H P.1 }, (holePolymerSystem H z).activity X.1‖
      ≤ ∑' X : { P : (holePolymerSystem H z).Polymer // r ∈ skeleton H P.1 }, ‖(holePolymerSystem H z).activity X.1‖ := by
    have h_summ : Summable (fun X : { P : (holePolymerSystem H z).Polymer // r ∈ skeleton H P.1 } => ‖(holePolymerSystem H z).activity X.1‖) :=
      Summable.of_finite
    have h_norm_le := norm_tsum_le_tsum_norm (f := fun X : { P : (holePolymerSystem H z).Polymer // r ∈ skeleton H P.1 } => (holePolymerSystem H z).activity X.1)
    exact h_norm_le h_summ
  have h_le : (∑' X : { P : (holePolymerSystem H z).Polymer // r ∈ skeleton H P.1 }, ‖(holePolymerSystem H z).activity X.1‖)
      ≤ ∑' X : { X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X },
        q ^ (discreteModifiedMetric H X.val + 1) := by
    rw [tsum_fintype, tsum_fintype]
    let f1 := fun X : { P : (holePolymerSystem H z).Polymer // r ∈ skeleton H P.1 } =>
      (⟨X.1.1, ⟨X.2, X.1.2.right.left, X.1.2.right.right⟩⟩ : { X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X })
    have hf1_inj : Function.Injective f1 := by
      intro a b h
      have h_eq : a.1.1 = b.1.1 := congrArg (fun x => x.val) h
      have h_val_eq : a.1 = b.1 := Subtype.ext h_eq
      exact Subtype.ext h_val_eq
    have hf1_surj : Function.Surjective f1 := by
      intro b
      refine ⟨⟨⟨b.val, ⟨?_, b.property.right.left, b.property.right.right⟩⟩, b.property.left⟩, rfl⟩
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have hr : r ∈ skeleton H b.val := b.property.left
      have hr_sub := skeleton_subset H b.val hr
      rw [he] at hr_sub
      cases hr_sub
    have h_sum_eq : ∑ x : { P : (holePolymerSystem H z).Polymer // r ∈ skeleton H P.1 }, q ^ (discreteModifiedMetric H (f1 x).val + 1) =
        ∑ y : { X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X }, q ^ (discreteModifiedMetric H y.val + 1) := by
      refine Fintype.sum_equiv (Equiv.ofBijective f1 ⟨hf1_inj, hf1_surj⟩) _ _ ?_
      intro x
      rfl
    rw [← h_sum_eq]
    apply Finset.sum_le_sum
    intro x _
    exact h_bound x.1
  have h_summable : ∑' X : { X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X },
      q ^ (discreteModifiedMetric H X.val + 1) ≤ (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)))⁻¹ :=
    discreteModifiedMetric_weight_summable H r q hdisj hnoedges hholes_ne hq0 hCq
  exact h_norm.trans (h_le.trans h_summable)

/-- **Holes-Respected Polymer System KP Criterion Satisfiability:**
    Under the modified-metric bound, the holes-respected polymer system satisfies the Kotecký–Preiss criterion
    for sufficiently small `q`. -/
theorem holePolymerSystem_KPCriterion {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (q : ℝ) (h_bound : ∀ X : (holePolymerSystem H z).Polymer, ‖(holePolymerSystem H z).activity X‖ ≤ q ^ (discreteModifiedMetric H X.1 + 1))
    (hq0 : 0 ≤ q)
    [h_nonempty : Nonempty (holePolymerSystem H z).Polymer]
    (hq_small : q * (Fintype.card (holePolymerSystem H z).Polymer : ℝ) * Real.exp 1 ≤ 1) :
    KP.KPCriterion (holePolymerSystem H z) (fun _ => 1) := by
  constructor
  · intro X
    norm_num
  · intro X
    have h_q1 : q ≤ 1 := by
      have h_card_ge : (1 : ℝ) ≤ (Fintype.card (holePolymerSystem H z).Polymer : ℝ) := by
        exact_mod_cast Fintype.card_pos
      have h_exp_ge : Real.exp 1 ≥ 1 := by
        rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
      have h_mul_ge : (1 : ℝ) ≤ (Fintype.card (holePolymerSystem H z).Polymer : ℝ) * Real.exp 1 := by
        calc (1 : ℝ) = 1 * 1 := by norm_num
          _ ≤ (Fintype.card (holePolymerSystem H z).Polymer : ℝ) * Real.exp 1 := by gcongr
      have h_q_mul : q * 1 ≤ q * ((Fintype.card (holePolymerSystem H z).Polymer : ℝ) * Real.exp 1) := by
        gcongr
      rw [mul_one, ← mul_assoc] at h_q_mul
      exact h_q_mul.trans hq_small
    have h_sum_le : ∑ Y ∈ Finset.univ.filter (fun Y => (holePolymerSystem H z).incomp X Y),
        ‖(holePolymerSystem H z).activity Y‖ * Real.exp ((fun _ : (holePolymerSystem H z).Polymer => (1 : ℝ)) Y)
        ≤ ∑ Y ∈ Finset.univ.filter (fun Y => (holePolymerSystem H z).incomp X Y), q * Real.exp 1 := by
      apply Finset.sum_le_sum
      intro Y _
      have h_act := h_bound Y
      have h_qn_le : q ^ (discreteModifiedMetric H Y.1) ≤ 1 := by
        calc q ^ (discreteModifiedMetric H Y.1) ≤ 1 ^ (discreteModifiedMetric H Y.1) := by gcongr
          _ = 1 := by simp
      have h_pow_eq : q ^ (discreteModifiedMetric H Y.1 + 1) = q * q ^ (discreteModifiedMetric H Y.1) := by
        rw [pow_succ', mul_comm]
      have h_mul_le : q * q ^ (discreteModifiedMetric H Y.1) ≤ q * 1 := by
        gcongr
      have h_q_le : q ^ (discreteModifiedMetric H Y.1 + 1) ≤ q := by
        rw [h_pow_eq]
        exact h_mul_le.trans (by rw [mul_one])
      have h_act_le : ‖(holePolymerSystem H z).activity Y‖ ≤ q := h_act.trans h_q_le
      gcongr
    have h_sum_const : ∑ Y ∈ Finset.univ.filter (fun Y => (holePolymerSystem H z).incomp X Y), q * Real.exp 1
        = ((Finset.univ.filter (fun Y => (holePolymerSystem H z).incomp X Y)).card : ℝ) * (q * Real.exp 1) := by
      simp
    have h_card_le : ((Finset.univ.filter (fun Y => (holePolymerSystem H z).incomp X Y)).card : ℝ)
        ≤ (Fintype.card (holePolymerSystem H z).Polymer : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have h_bound_final : ((Finset.univ.filter (fun Y => (holePolymerSystem H z).incomp X Y)).card : ℝ) * (q * Real.exp 1) ≤ 1 := by
      have : ((Finset.univ.filter (fun Y => (holePolymerSystem H z).incomp X Y)).card : ℝ) * (q * Real.exp 1)
          = q * ((Finset.univ.filter (fun Y => (holePolymerSystem H z).incomp X Y)).card : ℝ) * Real.exp 1 := by ring
      rw [this]
      have : q * ((Finset.univ.filter (fun Y => (holePolymerSystem H z).incomp X Y)).card : ℝ) * Real.exp 1
          ≤ q * (Fintype.card (holePolymerSystem H z).Polymer : ℝ) * Real.exp 1 := by gcongr
      exact this.trans hq_small
    exact h_sum_le.trans (h_sum_const.trans_le h_bound_final)

/-- **Holes-Respected Polymer System KP Convergence:**
    For any activity z satisfying the modified-metric bound with q sufficiently small
    (dependent on the total number of polymers), the cluster expansion converges. -/
theorem holePolymerSystem_converges {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (q : ℝ) (h_bound : ∀ X : (holePolymerSystem H z).Polymer, ‖(holePolymerSystem H z).activity X‖ ≤ q ^ (discreteModifiedMetric H X.1 + 1))
    (hq0 : 0 ≤ q)
    [h_nonempty : Nonempty (holePolymerSystem H z).Polymer]
    (hq_small : q * (Fintype.card (holePolymerSystem H z).Polymer : ℝ) * Real.exp 1 ≤ 1) :
    Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (holePolymerSystem H z).Polymer,
        (KP.ursell (holePolymerSystem H z) X : ℂ) * ∏ i, (holePolymerSystem H z).activity (X i)) :=
  KP.kp_convergence_sharp (holePolymerSystem H z) (holePolymerSystem_KPCriterion H z q h_bound hq0 hq_small)

/-- **Holes-Respected Polymer System Quantitative Cluster Sum Bound:**
    The cluster sum is bounded in norm by the total weighted activity of the polymers. -/
theorem holePolymerSystem_norm_clusterSum_le {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (q : ℝ) (h_bound : ∀ X : (holePolymerSystem H z).Polymer, ‖(holePolymerSystem H z).activity X‖ ≤ q ^ (discreteModifiedMetric H X.1 + 1))
    (hq0 : 0 ≤ q)
    [h_nonempty : Nonempty (holePolymerSystem H z).Polymer]
    (hq_small : q * (Fintype.card (holePolymerSystem H z).Polymer : ℝ) * Real.exp 1 ≤ 1) :
    ‖KP.clusterSum (holePolymerSystem H z)‖
      ≤ ∑ c : (holePolymerSystem H z).Polymer, ‖(holePolymerSystem H z).activity c‖ * Real.exp 1 :=
  KP.kp_norm_clusterSum_le_sharp (holePolymerSystem H z) (holePolymerSystem_KPCriterion H z q h_bound hq0 hq_small)

end YangMills.RG
