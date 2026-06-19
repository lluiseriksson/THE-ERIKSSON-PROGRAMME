/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.HolePolymerSystem
import YangMills.KP.Restriction

attribute [local instance] Classical.propDecidable

open Finset

namespace YangMills.RG

/-- Abbreviation for the polymer subtype to assist Lean's unification. -/
abbrev PolymerType {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) :=
  (holePolymerSystem H z).Polymer

/-- Abbreviation for the source-facing active-polymer subtype. -/
abbrev OmegaPolymerType {d L : ℕ} [NeZero L] (H : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ) :=
  (omegaHolePolymerSystem H z).Polymer

/-- The closed neighborhood of a finset of cubes on the lattice. -/
def closedNeigh {d L : ℕ} [NeZero L] (X : Finset (Cube d L)) : Finset (Cube d L) :=
  X ∪ X.biUnion (fun x => (cubeAdj d L).neighborFinset x)

lemma closedNeigh_subset_biUnion {d L : ℕ} [NeZero L] (X : Finset (Cube d L)) :
    closedNeigh X ⊆ X.biUnion (fun x => insert x ((cubeAdj d L).neighborFinset x)) := by
  unfold closedNeigh
  intro y hy
  rw [mem_union] at hy
  rw [mem_biUnion]
  rcases hy with hyX | hy_neigh
  · refine ⟨y, hyX, ?_⟩
    simp
  · rw [mem_biUnion] at hy_neigh
    rcases hy_neigh with ⟨x, hx, hyx⟩
    refine ⟨x, hx, ?_⟩
    simp [hyx]

lemma insert_neighbor_card_le {d L : ℕ} [NeZero L] (x : Cube d L) :
    (insert x ((cubeAdj d L).neighborFinset x)).card ≤ 3 ^ d + 1 := by
  classical
  have h_not : x ∉ (cubeAdj d L).neighborFinset x := by
    rw [SimpleGraph.mem_neighborFinset]
    exact (cubeAdj d L).loopless.irrefl x
  rw [Finset.card_insert_of_notMem h_not]
  rw [SimpleGraph.card_neighborFinset_eq_degree]
  have h_deg : (cubeAdj d L).degree x ≤ 3 ^ d := by
    exact cubeAdj_degree_le d L x
  omega

lemma closedNeigh_card_le {d L : ℕ} [NeZero L] (X : Finset (Cube d L)) :
    (closedNeigh X).card ≤ (3 ^ d + 1) * X.card := by
  classical
  have h_sub := closedNeigh_subset_biUnion X
  have h_card_le := card_le_card h_sub
  have h_biunion_card : (X.biUnion (fun x => insert x ((cubeAdj d L).neighborFinset x))).card ≤
      ∑ x ∈ X, (insert x ((cubeAdj d L).neighborFinset x)).card := card_biUnion_le
  have h_sum_le : ∑ x ∈ X, (insert x ((cubeAdj d L).neighborFinset x)).card ≤ ∑ x ∈ X, (3 ^ d + 1) := by
    apply Finset.sum_le_sum
    intro x _
    exact insert_neighbor_card_le x
  have h_sum_const : ∑ x ∈ X, (3 ^ d + 1) = X.card * (3 ^ d + 1) := sum_const _
  have h_mul_comm : X.card * (3 ^ d + 1) = (3 ^ d + 1) * X.card := by ring
  exact h_card_le.trans (h_biunion_card.trans (h_sum_le.trans (h_sum_const ▸ h_mul_comm ▸ le_refl _)))

lemma incomp_imp_intersect {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (X Y : PolymerType H z) (h : (holePolymerSystem H z).incomp X Y) :
    (Y.val ∩ closedNeigh X.val).Nonempty := by
  unfold closedNeigh
  rcases h with hd | ⟨x, hx, y, hy, hadj⟩
  · rw [Finset.disjoint_iff_inter_eq_empty] at hd
    have hne : Y.val ∩ X.val ≠ ∅ := by
      intro he
      have h_eq : X.val ∩ Y.val = Y.val ∩ X.val := Finset.inter_comm _ _
      rw [he] at h_eq
      exact hd h_eq
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    rw [mem_inter] at hx
    refine ⟨x, ?_⟩
    rw [mem_inter, mem_union]
    exact ⟨hx.1, Or.inl hx.2⟩
  · refine ⟨y, ?_⟩
    rw [mem_inter, mem_union]
    refine ⟨hy, Or.inr ?_⟩
    rw [mem_biUnion]
    refine ⟨x, hx, ?_⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact hadj

lemma filter_incomp_subset {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (X : PolymerType H z) :
    Finset.filter (fun Y : PolymerType H z => (holePolymerSystem H z).incomp X Y) Finset.univ ⊆
    Finset.filter (fun Y : PolymerType H z => ∃ s ∈ closedNeigh X.val, s ∈ Y.val) Finset.univ := by
  intro Y hY
  rw [mem_filter] at hY ⊢
  refine ⟨mem_univ _, ?_⟩
  obtain ⟨s, hs⟩ := incomp_imp_intersect H z X Y hY.2
  rw [mem_inter] at hs
  exact ⟨s, hs.2, hs.1⟩

lemma sum_union_le {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (s₁ ∪ s₂).sum f ≤ s₁.sum f + s₂.sum f := by
  have h_eq : s₁ ∪ s₂ = s₁ ∪ (s₂ \ s₁) := by
    ext x
    simp only [mem_union, mem_sdiff]
    tauto
  rw [h_eq]
  have h_disj : Disjoint s₁ (s₂ \ s₁) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy h_eq
    rw [Finset.mem_sdiff] at hy
    rw [h_eq] at hx
    exact hy.2 hx
  rw [Finset.sum_union h_disj]
  have h_sub : s₂ \ s₁ ⊆ s₂ := sdiff_subset
  have h_sum_le := Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun x _ _ => hf x)
  linarith

lemma sum_biUnion_le {α β : Type*} [DecidableEq α] [DecidableEq β] (S : Finset α) (F : α → Finset β) (g : β → ℝ) (hg : ∀ x, 0 ≤ g x) :
    (S.biUnion F).sum g ≤ ∑ a ∈ S, (F a).sum g := by
  induction S using Finset.induction_on with
  | empty =>
    simp
  | insert ha ih has =>
    rw [biUnion_insert, sum_insert has]
    have h_le := sum_union_le (F ha) (ih.biUnion F) g hg
    linarith

/-- **Volume-Uniform Kotecký-Preiss Criterion under Local Summability:**
    If the sum of activities of all polymers containing a fixed cube is bounded locally,
    then the polymer system satisfies the KP criterion with weight function `a(X) = |X|`. -/
theorem holePolymerSystem_KPCriterion_volumeUniform {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (h_local : ∀ s : Cube d L, ∑ Y ∈ Finset.univ.filter (fun Y : PolymerType H z => s ∈ Y.val),
        ‖(holePolymerSystem H z).activity Y‖ * Real.exp (Y.val.card : ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ)⁻¹) :
    KP.KPCriterion (holePolymerSystem H z) (fun X => (X.val.card : ℝ)) := by
  constructor
  · intro X
    positivity
  · intro X
    have h_sub := filter_incomp_subset H z X
    have h_sum_le := Finset.sum_le_sum_of_subset_of_nonneg (f := fun Y => ‖(holePolymerSystem H z).activity Y‖ * Real.exp (Y.val.card : ℝ))
        h_sub (fun Y _ _ => by positivity)
    have h_biunion : Finset.filter (fun Y : PolymerType H z => ∃ s ∈ closedNeigh X.val, s ∈ Y.val) Finset.univ ⊆
        (closedNeigh X.val).biUnion (fun s => Finset.filter (fun Y : PolymerType H z => s ∈ Y.val) Finset.univ) := by
      intro Y hY
      rw [mem_filter] at hY
      rcases hY.2 with ⟨s, hs_S, hs_m⟩
      rw [mem_biUnion]
      refine ⟨s, hs_S, ?_⟩
      rw [mem_filter]
      exact ⟨mem_univ Y, hs_m⟩
    have h_biunion_sum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun Y => ‖(holePolymerSystem H z).activity Y‖ * Real.exp (Y.val.card : ℝ))
        h_biunion (fun Y _ _ => by positivity)
    have h_sum_biunion_le := sum_biUnion_le (closedNeigh X.val) (fun s => Finset.filter (fun Y => s ∈ Y.val) Finset.univ)
        (fun Y => ‖(holePolymerSystem H z).activity Y‖ * Real.exp (Y.val.card : ℝ)) (fun Y => by positivity)
    have h_sum_local_le : ∑ s ∈ closedNeigh X.val, ∑ Y ∈ Finset.filter (fun Y => s ∈ Y.val) Finset.univ,
        ‖(holePolymerSystem H z).activity Y‖ * Real.exp (Y.val.card : ℝ) ≤ ∑ s ∈ closedNeigh X.val, ((3 ^ d + 1 : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro s _
      exact h_local s
    have h_sum_const : ∑ s ∈ closedNeigh X.val, ((3 ^ d + 1 : ℕ) : ℝ)⁻¹ = ((closedNeigh X.val).card : ℝ) * ((3 ^ d + 1 : ℕ) : ℝ)⁻¹ := by
      rw [sum_const, nsmul_eq_mul]
    have h_card_le : ((closedNeigh X.val).card : ℝ) * ((3 ^ d + 1 : ℕ) : ℝ)⁻¹ ≤ ((3 ^ d + 1 : ℕ) : ℝ) * (X.val.card : ℝ) * ((3 ^ d + 1 : ℕ) : ℝ)⁻¹ := by
      have h_geom := closedNeigh_card_le X.val
      have h_cast : ((closedNeigh X.val).card : ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ) * (X.val.card : ℝ) := by
        exact_mod_cast h_geom
      gcongr
    have h_cancel : ((3 ^ d + 1 : ℕ) : ℝ) * (X.val.card : ℝ) * ((3 ^ d + 1 : ℕ) : ℝ)⁻¹ = (X.val.card : ℝ) := by
      have h3d : (3 ^ d : ℝ) + 1 ≠ 0 := by positivity
      exact calc ((3 ^ d + 1 : ℕ) : ℝ) * (X.val.card : ℝ) * ((3 ^ d + 1 : ℕ) : ℝ)⁻¹
        _ = (((3 ^ d + 1 : ℕ) : ℝ) * ((3 ^ d + 1 : ℕ) : ℝ)⁻¹) * (X.val.card : ℝ) := by ring
        _ = 1 * (X.val.card : ℝ) := by
          have h_eq : ((3 ^ d + 1 : ℕ) : ℝ) = (3 ^ d : ℝ) + 1 := by push_cast; rfl
          rw [h_eq, mul_inv_cancel₀ h3d]
        _ = (X.val.card : ℝ) := by ring
    exact h_sum_le.trans (h_biunion_sum.trans (h_sum_biunion_le.trans (h_sum_local_le.trans (by
      rw [h_sum_const]
      exact h_card_le.trans (by rw [h_cancel])
    ))))

/-- **Volume-uniform Kotecký-Preiss criterion for a scalar activity tilt.**

This is the form consumed by the cluster-tail estimates: the `e^t` tilt
multiplies every polymer activity by the same scalar, but the polymer type and
incompatibility relation are unchanged. -/
theorem holePolymerSystem_KPCriterion_volumeUniform_scaled {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (ρ : ℝ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter (fun Y : PolymerType H z => s ∈ Y.val),
        ‖(ρ : ℂ) * (holePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ)⁻¹) :
    KP.KPCriterion ((holePolymerSystem H z).scaleActivity ρ)
      (fun X => (X.val.card : ℝ)) := by
  constructor
  · intro X
    positivity
  · intro X
    have h_sub := filter_incomp_subset H z X
    have h_sum_le := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun Y => ‖(ρ : ℂ) * (holePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ))
        h_sub (fun Y _ _ => by positivity)
    have h_biunion : Finset.filter (fun Y : PolymerType H z =>
        ∃ s ∈ closedNeigh X.val, s ∈ Y.val) Finset.univ ⊆
        (closedNeigh X.val).biUnion
          (fun s => Finset.filter (fun Y => s ∈ Y.val) Finset.univ) := by
      intro Y hY
      rw [mem_filter] at hY
      rcases hY.2 with ⟨s, hs_S, hs_m⟩
      rw [mem_biUnion]
      refine ⟨s, hs_S, ?_⟩
      rw [mem_filter]
      exact ⟨mem_univ Y, hs_m⟩
    have h_biunion_sum := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun Y => ‖(ρ : ℂ) * (holePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ))
        h_biunion (fun Y _ _ => by positivity)
    have h_sum_biunion_le := sum_biUnion_le (closedNeigh X.val)
        (fun s => Finset.filter (fun Y => s ∈ Y.val) Finset.univ)
        (fun Y => ‖(ρ : ℂ) * (holePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ)) (fun Y => by positivity)
    have h_sum_local_le : ∑ s ∈ closedNeigh X.val,
        ∑ Y ∈ Finset.filter (fun Y => s ∈ Y.val) Finset.univ,
          ‖(ρ : ℂ) * (holePolymerSystem H z).activity Y‖ *
            Real.exp (Y.val.card : ℝ)
        ≤ ∑ s ∈ closedNeigh X.val, ((3 ^ d + 1 : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro s _
      exact h_local s
    have h_sum_const : ∑ s ∈ closedNeigh X.val, ((3 ^ d + 1 : ℕ) : ℝ)⁻¹ =
        ((closedNeigh X.val).card : ℝ) * ((3 ^ d + 1 : ℕ) : ℝ)⁻¹ := by
      rw [sum_const, nsmul_eq_mul]
    have h_card_le : ((closedNeigh X.val).card : ℝ) *
        ((3 ^ d + 1 : ℕ) : ℝ)⁻¹
        ≤ ((3 ^ d + 1 : ℕ) : ℝ) * (X.val.card : ℝ) *
          ((3 ^ d + 1 : ℕ) : ℝ)⁻¹ := by
      have h_geom := closedNeigh_card_le X.val
      have h_cast : ((closedNeigh X.val).card : ℝ)
          ≤ ((3 ^ d + 1 : ℕ) : ℝ) * (X.val.card : ℝ) := by
        exact_mod_cast h_geom
      gcongr
    have h_cancel : ((3 ^ d + 1 : ℕ) : ℝ) * (X.val.card : ℝ) *
        ((3 ^ d + 1 : ℕ) : ℝ)⁻¹ = (X.val.card : ℝ) := by
      have h3d : (3 ^ d : ℝ) + 1 ≠ 0 := by positivity
      exact calc ((3 ^ d + 1 : ℕ) : ℝ) * (X.val.card : ℝ) *
            ((3 ^ d + 1 : ℕ) : ℝ)⁻¹
          _ = (((3 ^ d + 1 : ℕ) : ℝ) *
              ((3 ^ d + 1 : ℕ) : ℝ)⁻¹) * (X.val.card : ℝ) := by ring
          _ = 1 * (X.val.card : ℝ) := by
            have h_eq : ((3 ^ d + 1 : ℕ) : ℝ) = (3 ^ d : ℝ) + 1 := by
              push_cast
              rfl
            rw [h_eq, mul_inv_cancel₀ h3d]
          _ = (X.val.card : ℝ) := by ring
    show ∑ Y ∈ Finset.univ.filter
        (fun Y => ((holePolymerSystem H z).scaleActivity ρ).incomp X Y),
        ‖((holePolymerSystem H z).scaleActivity ρ).activity Y‖ *
          Real.exp ((Y.val.card : ℝ)) ≤ (X.val.card : ℝ)
    exact h_sum_le.trans
      (h_biunion_sum.trans (h_sum_biunion_le.trans (h_sum_local_le.trans (by
        rw [h_sum_const]
        exact h_card_le.trans (by rw [h_cancel])))))

/-- **Volume-uniform KP criterion for the exponential activity tilt.**

This is the source-shaped form used by RG tail estimates: the local window is
written as `exp(t) * ‖z(Y)‖ * exp(|Y|)`, while the polymer system itself uses
the scalar activity tilt `scaleActivity (exp t)`. -/
theorem holePolymerSystem_KPCriterion_volumeUniform_exp {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (t : ℝ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter (fun Y : PolymerType H z => s ∈ Y.val),
        Real.exp t * ‖(holePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ)⁻¹) :
    KP.KPCriterion ((holePolymerSystem H z).scaleActivity (Real.exp t))
      (fun X => (X.val.card : ℝ)) := by
  refine holePolymerSystem_KPCriterion_volumeUniform_scaled H z (Real.exp t) ?_
  intro s
  refine (le_of_eq ?_).trans (h_local s)
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos t)]

/-- For the Appendix-F-facing `Ω`-active system, all polymers incompatible with
`X` are covered by the active skeleton roots of `X`. -/
lemma omega_filter_incomp_subset_skeleton {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (X : OmegaPolymerType H z) :
    Finset.filter (fun Y : OmegaPolymerType H z =>
        (omegaHolePolymerSystem H z).incomp X Y) Finset.univ ⊆
      (skeleton H X.val).biUnion
        (fun s => Finset.filter
          (fun Y : OmegaPolymerType H z => s ∈ skeleton H Y.val) Finset.univ) := by
  intro Y hY
  rw [mem_filter] at hY
  rw [mem_biUnion]
  obtain ⟨s, hsX, hsY⟩ :=
    (omegaHolePolymerSystem_incomp_iff_exists H z X Y).mp hY.2
  refine ⟨s, hsX, ?_⟩
  rw [mem_filter]
  exact ⟨mem_univ Y, hsY⟩

/-- **Source-facing `Ω`-active volume-uniform KP criterion.**

Dimock Appendix F connects polymers through intersections of their active parts
inside `Ω`, represented here by `skeleton H X`.  Thus a local activity window
pinned at each active cube, with total mass at most `1`, gives the KP criterion
with weight `a(X)=|X|`. -/
theorem omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton {d L : ℕ}
    [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter
          (fun Y : OmegaPolymerType H z => s ∈ skeleton H Y.val),
        ‖(omegaHolePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ 1) :
    KP.KPCriterion (omegaHolePolymerSystem H z)
      (fun X => (X.val.card : ℝ)) := by
  constructor
  · intro X
    positivity
  · intro X
    have h_sub := omega_filter_incomp_subset_skeleton H z X
    have h_sum_le := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun Y : OmegaPolymerType H z =>
          ‖(omegaHolePolymerSystem H z).activity Y‖ *
            Real.exp (Y.val.card : ℝ))
        h_sub (fun Y _ _ => by positivity)
    have h_sum_biunion_le := sum_biUnion_le (skeleton H X.val)
        (fun s => Finset.filter
          (fun Y : OmegaPolymerType H z => s ∈ skeleton H Y.val) Finset.univ)
        (fun Y : OmegaPolymerType H z =>
          ‖(omegaHolePolymerSystem H z).activity Y‖ *
            Real.exp (Y.val.card : ℝ)) (fun Y => by positivity)
    have h_sum_local_le :
        ∑ s ∈ skeleton H X.val,
          ∑ Y ∈ Finset.filter
              (fun Y : OmegaPolymerType H z => s ∈ skeleton H Y.val) Finset.univ,
            ‖(omegaHolePolymerSystem H z).activity Y‖ *
              Real.exp (Y.val.card : ℝ)
        ≤ ∑ s ∈ skeleton H X.val, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro s _
      exact h_local s
    have h_card :
        ∑ s ∈ skeleton H X.val, (1 : ℝ) ≤ (X.val.card : ℝ) := by
      rw [sum_const, nsmul_eq_mul]
      simp only [mul_one]
      exact_mod_cast Finset.card_le_card (skeleton_subset H X.val)
    exact h_sum_le.trans (h_sum_biunion_le.trans (h_sum_local_le.trans h_card))

/-- Scalar-tilted version of the source-facing `Ω`-active KP criterion. -/
theorem omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_scaled
    {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (ρ : ℝ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter
          (fun Y : OmegaPolymerType H z => s ∈ skeleton H Y.val),
        ‖(ρ : ℂ) * (omegaHolePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ 1) :
    KP.KPCriterion ((omegaHolePolymerSystem H z).scaleActivity ρ)
      (fun X => (X.val.card : ℝ)) := by
  constructor
  · intro X
    positivity
  · intro X
    have h_sub := omega_filter_incomp_subset_skeleton H z X
    have h_sum_le := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun Y : OmegaPolymerType H z =>
          ‖(ρ : ℂ) * (omegaHolePolymerSystem H z).activity Y‖ *
            Real.exp (Y.val.card : ℝ))
        h_sub (fun Y _ _ => by positivity)
    have h_sum_biunion_le := sum_biUnion_le (skeleton H X.val)
        (fun s => Finset.filter
          (fun Y : OmegaPolymerType H z => s ∈ skeleton H Y.val) Finset.univ)
        (fun Y : OmegaPolymerType H z =>
          ‖(ρ : ℂ) * (omegaHolePolymerSystem H z).activity Y‖ *
            Real.exp (Y.val.card : ℝ)) (fun Y => by positivity)
    have h_sum_local_le :
        ∑ s ∈ skeleton H X.val,
          ∑ Y ∈ Finset.filter
              (fun Y : OmegaPolymerType H z => s ∈ skeleton H Y.val) Finset.univ,
            ‖(ρ : ℂ) * (omegaHolePolymerSystem H z).activity Y‖ *
              Real.exp (Y.val.card : ℝ)
        ≤ ∑ s ∈ skeleton H X.val, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro s _
      exact h_local s
    have h_card :
        ∑ s ∈ skeleton H X.val, (1 : ℝ) ≤ (X.val.card : ℝ) := by
      rw [sum_const, nsmul_eq_mul]
      simp only [mul_one]
      exact_mod_cast Finset.card_le_card (skeleton_subset H X.val)
    show ∑ Y ∈ Finset.univ.filter
        (fun Y => ((omegaHolePolymerSystem H z).scaleActivity ρ).incomp X Y),
        ‖((omegaHolePolymerSystem H z).scaleActivity ρ).activity Y‖ *
          Real.exp ((Y.val.card : ℝ)) ≤ (X.val.card : ℝ)
    exact h_sum_le.trans (h_sum_biunion_le.trans (h_sum_local_le.trans h_card))

/-- Exponential-tilted version of the source-facing `Ω`-active KP criterion. -/
theorem omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp
    {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (t : ℝ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter
          (fun Y : OmegaPolymerType H z => s ∈ skeleton H Y.val),
        Real.exp t * ‖(omegaHolePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ 1) :
    KP.KPCriterion ((omegaHolePolymerSystem H z).scaleActivity (Real.exp t))
      (fun X => (X.val.card : ℝ)) := by
  refine omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_scaled H z
    (Real.exp t) ?_
  intro s
  refine (le_of_eq ?_).trans (h_local s)
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos t)]

/-- Source-facing `Ω`-active Mayer series convergence from the local active
skeleton window. -/
theorem omegaHolePolymerSystem_converges_volumeUniform_skeleton {d L : ℕ}
    [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter
          (fun Y : OmegaPolymerType H z => s ∈ skeleton H Y.val),
        ‖(omegaHolePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ 1) :
    Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (omegaHolePolymerSystem H z).Polymer,
        (KP.ursell (omegaHolePolymerSystem H z) X : ℂ) *
          ∏ i, (omegaHolePolymerSystem H z).activity (X i)) :=
  KP.kp_convergence_sharp (omegaHolePolymerSystem H z)
    (omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton H z h_local)

/-- Source-facing `Ω`-active cluster-sum norm bound from the local active
skeleton window. -/
theorem omegaHolePolymerSystem_norm_clusterSum_le_volumeUniform_skeleton
    {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter
          (fun Y : OmegaPolymerType H z => s ∈ skeleton H Y.val),
        ‖(omegaHolePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ 1) :
    ‖KP.clusterSum (omegaHolePolymerSystem H z)‖
      ≤ ∑ c : (omegaHolePolymerSystem H z).Polymer,
          ‖(omegaHolePolymerSystem H z).activity c‖ *
            Real.exp (c.val.card : ℝ) :=
  KP.kp_norm_clusterSum_le_sharp (omegaHolePolymerSystem H z)
    (omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton H z h_local)

/-- Exponential-tilted source-facing `Ω`-active Mayer series convergence. -/
theorem omegaHolePolymerSystem_converges_volumeUniform_skeleton_exp
    {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (t : ℝ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter
          (fun Y : OmegaPolymerType H z => s ∈ skeleton H Y.val),
        Real.exp t * ‖(omegaHolePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ 1) :
    Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) →
          ((omegaHolePolymerSystem H z).scaleActivity (Real.exp t)).Polymer,
        (KP.ursell ((omegaHolePolymerSystem H z).scaleActivity (Real.exp t)) X : ℂ) *
          ∏ i, ((omegaHolePolymerSystem H z).scaleActivity (Real.exp t)).activity (X i)) :=
  KP.kp_convergence_sharp ((omegaHolePolymerSystem H z).scaleActivity (Real.exp t))
    (omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp H z t h_local)

/-- Exponential-tilted source-facing `Ω`-active quantitative cluster-sum bound. -/
theorem omegaHolePolymerSystem_norm_clusterSum_le_volumeUniform_skeleton_exp
    {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (t : ℝ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter
          (fun Y : OmegaPolymerType H z => s ∈ skeleton H Y.val),
        Real.exp t * ‖(omegaHolePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ 1) :
    ‖KP.clusterSum ((omegaHolePolymerSystem H z).scaleActivity (Real.exp t))‖
      ≤ ∑ c : ((omegaHolePolymerSystem H z).scaleActivity (Real.exp t)).Polymer,
          ‖((omegaHolePolymerSystem H z).scaleActivity (Real.exp t)).activity c‖ *
            Real.exp (c.val.card : ℝ) :=
  KP.kp_norm_clusterSum_le_sharp ((omegaHolePolymerSystem H z).scaleActivity (Real.exp t))
    (omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp H z t h_local)

/-- **Volume-Uniform Mayer Cluster Series Convergence:**
    The cluster series converges absolutely and volume-uniformly under the local summability condition. -/
theorem holePolymerSystem_converges_volumeUniform {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (h_local : ∀ s : Cube d L, ∑ Y ∈ Finset.univ.filter (fun Y : PolymerType H z => s ∈ Y.val),
        ‖(holePolymerSystem H z).activity Y‖ * Real.exp (Y.val.card : ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ)⁻¹) :
    Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (holePolymerSystem H z).Polymer,
        (KP.ursell (holePolymerSystem H z) X : ℂ) * ∏ i, (holePolymerSystem H z).activity (X i)) :=
  KP.kp_convergence_sharp (holePolymerSystem H z) (holePolymerSystem_KPCriterion_volumeUniform H z h_local)

/-- **Volume-Uniform Quantitative Cluster Sum Bound:**
    The norm of the cluster sum is bounded volume-uniformly under the local summability condition. -/
theorem holePolymerSystem_norm_clusterSum_le_volumeUniform {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (h_local : ∀ s : Cube d L, ∑ Y ∈ Finset.univ.filter (fun Y : PolymerType H z => s ∈ Y.val),
        ‖(holePolymerSystem H z).activity Y‖ * Real.exp (Y.val.card : ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ)⁻¹) :
    ‖KP.clusterSum (holePolymerSystem H z)‖
      ≤ ∑ c : (holePolymerSystem H z).Polymer, ‖(holePolymerSystem H z).activity c‖ * Real.exp (c.val.card : ℝ) :=
  KP.kp_norm_clusterSum_le_sharp (holePolymerSystem H z) (holePolymerSystem_KPCriterion_volumeUniform H z h_local)

/-- **Scaled volume-uniform Mayer cluster series convergence.**

The same local criterion as `holePolymerSystem_KPCriterion_volumeUniform_scaled`
feeds the sharp KP convergence theorem for a scalar-tilted activity field. -/
theorem holePolymerSystem_converges_volumeUniform_scaled {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (ρ : ℝ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter (fun Y : PolymerType H z => s ∈ Y.val),
        ‖(ρ : ℂ) * (holePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ)⁻¹) :
    Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → ((holePolymerSystem H z).scaleActivity ρ).Polymer,
        (KP.ursell ((holePolymerSystem H z).scaleActivity ρ) X : ℂ) *
          ∏ i, ((holePolymerSystem H z).scaleActivity ρ).activity (X i)) :=
  KP.kp_convergence_sharp ((holePolymerSystem H z).scaleActivity ρ)
    (holePolymerSystem_KPCriterion_volumeUniform_scaled H z ρ h_local)

/-- **Scaled volume-uniform quantitative cluster-sum bound.**

This is the scalar-tilted analogue of
`holePolymerSystem_norm_clusterSum_le_volumeUniform`, with the same local
smallness criterion used by the RG cluster-tail estimates. -/
theorem holePolymerSystem_norm_clusterSum_le_volumeUniform_scaled {d L : ℕ}
    [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (ρ : ℝ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter (fun Y : PolymerType H z => s ∈ Y.val),
        ‖(ρ : ℂ) * (holePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ)⁻¹) :
    ‖KP.clusterSum ((holePolymerSystem H z).scaleActivity ρ)‖
      ≤ ∑ c : ((holePolymerSystem H z).scaleActivity ρ).Polymer,
          ‖((holePolymerSystem H z).scaleActivity ρ).activity c‖ *
            Real.exp (c.val.card : ℝ) :=
  KP.kp_norm_clusterSum_le_sharp ((holePolymerSystem H z).scaleActivity ρ)
    (holePolymerSystem_KPCriterion_volumeUniform_scaled H z ρ h_local)

/-- **Exponential-tilted volume-uniform Mayer cluster series convergence.** -/
theorem holePolymerSystem_converges_volumeUniform_exp {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (t : ℝ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter (fun Y : PolymerType H z => s ∈ Y.val),
        Real.exp t * ‖(holePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ)⁻¹) :
    Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → ((holePolymerSystem H z).scaleActivity (Real.exp t)).Polymer,
        (KP.ursell ((holePolymerSystem H z).scaleActivity (Real.exp t)) X : ℂ) *
          ∏ i, ((holePolymerSystem H z).scaleActivity (Real.exp t)).activity (X i)) :=
  KP.kp_convergence_sharp ((holePolymerSystem H z).scaleActivity (Real.exp t))
    (holePolymerSystem_KPCriterion_volumeUniform_exp H z t h_local)

/-- **Exponential-tilted volume-uniform quantitative cluster-sum bound.** -/
theorem holePolymerSystem_norm_clusterSum_le_volumeUniform_exp {d L : ℕ}
    [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (t : ℝ)
    (h_local : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter (fun Y : PolymerType H z => s ∈ Y.val),
        Real.exp t * ‖(holePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ)⁻¹) :
    ‖KP.clusterSum ((holePolymerSystem H z).scaleActivity (Real.exp t))‖
      ≤ ∑ c : ((holePolymerSystem H z).scaleActivity (Real.exp t)).Polymer,
          ‖((holePolymerSystem H z).scaleActivity (Real.exp t)).activity c‖ *
            Real.exp (c.val.card : ℝ) :=
  KP.kp_norm_clusterSum_le_sharp ((holePolymerSystem H z).scaleActivity (Real.exp t))
    (holePolymerSystem_KPCriterion_volumeUniform_exp H z t h_local)

end YangMills.RG
