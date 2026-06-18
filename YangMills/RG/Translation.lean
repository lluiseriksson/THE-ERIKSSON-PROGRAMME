/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.HolePolymerSystem

open Finset

namespace YangMills.RG

lemma add_right_cancel_cube {d L : ℕ} (v : Cube d L) (x y : Cube d L) :
    x + v = y + v ↔ x = y := by
  constructor
  · intro h
    have h1 : x + v - v = y + v - v := by rw [h]
    simpa using h1
  · intro h
    rw [h]

lemma cubeAdj_adj_translate {d L : ℕ} (v : Cube d L) (x y : Cube d L) :
    (cubeAdj d L).Adj (x + v) (y + v) ↔ (cubeAdj d L).Adj x y := by
  dsimp [cubeAdj]
  rw [add_right_cancel_cube v x y]
  congr! 2 with i
  have : y i + v i - (x i + v i) = y i - x i := by
    ring
  rw [this]

/-- Translate a finset of cubes by a vector `v`. -/
def translateFinset {d L : ℕ} (v : Cube d L) (S : Finset (Cube d L)) : Finset (Cube d L) :=
  S.map ⟨(· + v), fun x y h => (add_right_cancel_cube v x y).mp h⟩

lemma mem_translateFinset_iff {d L : ℕ} (v : Cube d L) (S : Finset (Cube d L)) (z : Cube d L) :
    z ∈ translateFinset v S ↔ z - v ∈ S := by
  dsimp [translateFinset]
  simp only [mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    refine ⟨z - v, h, by simp⟩

/-- Translating by 0 is the identity. -/
lemma translateFinset_zero {d L : ℕ} (S : Finset (Cube d L)) :
    translateFinset 0 S = S := by
  dsimp [translateFinset]
  ext x
  simp

/-- Sequential translations compose. -/
lemma translateFinset_compose {d L : ℕ} (v1 v2 : Cube d L) (S : Finset (Cube d L)) :
    translateFinset v2 (translateFinset v1 S) = translateFinset (v1 + v2) S := by
  dsimp [translateFinset]
  rw [Finset.map_map]
  congr 1
  ext x
  dsimp [Function.comp]
  rw [add_assoc]

/-- Translation is injective on finsets. -/
lemma translateFinset_inj {d L : ℕ} (v : Cube d L) {S1 S2 : Finset (Cube d L)}
    (h : translateFinset v S1 = translateFinset v S2) : S1 = S2 := by
  have h1 : translateFinset (-v) (translateFinset v S1) = translateFinset (-v) (translateFinset v S2) := by rw [h]
  rw [translateFinset_compose, translateFinset_compose] at h1
  simp [translateFinset_zero] at h1
  exact h1

/-- The translation embedding of a finset of cubes by a vector `v`. -/
def translateFinsetEmb {d L : ℕ} (v : Cube d L) : Finset (Cube d L) ↪ Finset (Cube d L) where
  toFun := translateFinset v
  inj' _ _ := translateFinset_inj v

/-- Translate a hole family by translating each of its hole components. -/
def translateHoleFamily {d L : ℕ} (H : HoleFamily d L) (v : Cube d L) : HoleFamily d L :=
  ⟨H.holes.map (translateFinsetEmb v)⟩

/-- Skeleton translation-invariance. -/
lemma skeleton_translate {d L : ℕ} (H : HoleFamily d L) (X : Finset (Cube d L)) (v : Cube d L) :
    skeleton (translateHoleFamily H v) (translateFinset v X) = translateFinset v (skeleton H X) := by
  ext z
  rw [mem_translateFinset_iff]
  unfold skeleton
  simp only [mem_filter, mem_translateFinset_iff]
  constructor
  · rintro ⟨hz, hnot⟩
    refine ⟨hz, ?_⟩
    rintro ⟨H₀, hH₀, hz_in⟩
    apply hnot
    refine ⟨translateFinset v H₀, ?_, ?_⟩
    · dsimp [translateHoleFamily]
      simp only [mem_map]
      refine ⟨H₀, hH₀, rfl⟩
    · rw [mem_translateFinset_iff]
      exact hz_in
  · rintro ⟨hz, hnot⟩
    refine ⟨hz, ?_⟩
    rintro ⟨H₀', hH₀', hz_in⟩
    dsimp [translateHoleFamily] at hH₀'
    simp only [mem_map] at hH₀'
    rcases hH₀' with ⟨H₀, hH₀, rfl⟩
    apply hnot
    refine ⟨H₀, hH₀, ?_⟩
    rwa [← mem_translateFinset_iff]

/-- Map a walk by translating every vertex along the walk. -/
def translateWalk {d L : ℕ} (v : Cube d L) {x y : Cube d L} :
    (cubeAdj d L).Walk x y → (cubeAdj d L).Walk (x + v) (y + v)
  | SimpleGraph.Walk.nil => SimpleGraph.Walk.nil
  | @SimpleGraph.Walk.cons _ _ _ z _ hadj w' =>
    have hadj_trans : (cubeAdj d L).Adj (x + v) (z + v) := by
      rw [cubeAdj_adj_translate]
      exact hadj
    SimpleGraph.Walk.cons hadj_trans (translateWalk v w')

/-- The support of a translated walk is the translated support of the original walk. -/
lemma support_translateWalk {d L : ℕ} (v : Cube d L) {x y : Cube d L} (w : (cubeAdj d L).Walk x y) :
    (translateWalk v w).support = w.support.map (fun z => z + v) := by
  induction w with
  | nil =>
    rfl
  | cons hadj w' ih =>
    dsimp [translateWalk]
    rw [ih]

lemma translateFinset_subset_iff {d L : ℕ} (v : Cube d L) (A B : Finset (Cube d L)) :
    translateFinset v A ⊆ translateFinset v B ↔ A ⊆ B := by
  simp [translateFinset]

lemma translateFinset_disjoint_iff {d L : ℕ} (v : Cube d L) (A B : Finset (Cube d L)) :
    Disjoint (translateFinset v A) (translateFinset v B) ↔ Disjoint A B := by
  rw [disjoint_iff_ne, disjoint_iff_ne]
  constructor
  · intro h x hx y hy h_eq
    have hx_trans : x + v ∈ translateFinset v A := by
      rw [mem_translateFinset_iff]
      simp [hx]
    have hy_trans : y + v ∈ translateFinset v B := by
      rw [mem_translateFinset_iff]
      simp [hy]
    have h_eq_trans : x + v = y + v := by rw [h_eq]
    exact h (x + v) hx_trans (y + v) hy_trans h_eq_trans
  · intro h x hx y hy h_eq
    rw [mem_translateFinset_iff] at hx hy
    apply h (x - v) hx (y - v) hy
    have h1 : x - v = y - v := by rw [h_eq]
    exact h1

/-- Connectivity translation-invariance. -/
lemma cubeConnected_translate {d L : ℕ} (S : Finset (Cube d L)) (v : Cube d L)
    (hS : cubeConnected S) : cubeConnected (translateFinset v S) := by
  intro x_trans hx y_trans hy
  rw [mem_translateFinset_iff] at hx hy
  obtain ⟨w, hw⟩ := hS (x_trans - v) hx (y_trans - v) hy
  have hx_eq : x_trans = x_trans - v + v := by simp
  have hy_eq : y_trans = y_trans - v + v := by simp
  rw [hx_eq, hy_eq]
  refine ⟨translateWalk v w, ?_⟩
  intro u hu
  rw [support_translateWalk] at hu
  simp only [List.mem_map] at hu
  rcases hu with ⟨z, hz, rfl⟩
  rw [mem_translateFinset_iff]
  have : z + v - v = z := by simp
  rw [this]
  exact hw z hz

lemma translateFinset_card {d L : ℕ} (v : Cube d L) (S : Finset (Cube d L)) :
    (translateFinset v S).card = S.card := by
  dsimp [translateFinset]
  rw [card_map]

/-- Discrete modified metric translation-invariance. -/
lemma discreteModifiedMetric_translate {d L : ℕ} (H : HoleFamily d L) (X : Finset (Cube d L)) (v : Cube d L) :
    discreteModifiedMetric (translateHoleFamily H v) (translateFinset v X) = discreteModifiedMetric H X := by
  classical
  unfold discreteModifiedMetric
  rw [skeleton_translate]
  have h_equiv : (∃ S : Finset (Cube d L), translateFinset v (skeleton H X) ⊆ S ∧ S ⊆ translateFinset v X ∧ cubeConnected S) ↔
      (∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S) := by
    constructor
    · rintro ⟨S, hS1, hS2, hS3⟩
      refine ⟨translateFinset (-v) S, ?_, ?_, ?_⟩
      · rw [← translateFinset_subset_iff v]
        have h_eq : translateFinset v (translateFinset (-v) S) = S := by
          rw [translateFinset_compose]
          simp [translateFinset_zero]
        rw [h_eq]
        exact hS1
      · rw [← translateFinset_subset_iff v]
        have h_eq : translateFinset v (translateFinset (-v) S) = S := by
          rw [translateFinset_compose]
          simp [translateFinset_zero]
        rw [h_eq]
        exact hS2
      · have := cubeConnected_translate S (-v) hS3
        have h_eq : translateFinset (-v) S = translateFinset (-v) S := rfl
        rwa [h_eq] at this
    · rintro ⟨S, hS1, hS2, hS3⟩
      refine ⟨translateFinset v S, ?_, ?_, ?_⟩
      · rw [translateFinset_subset_iff]
        exact hS1
      · rw [translateFinset_subset_iff]
        exact hS2
      · exact cubeConnected_translate S v hS3
  by_cases h_ex : ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S
  · have h_ex_trans : ∃ S : Finset (Cube d L), translateFinset v (skeleton H X) ⊆ S ∧ S ⊆ translateFinset v X ∧ cubeConnected S := by
      rwa [h_equiv]
    rw [dif_pos h_ex_trans, dif_pos h_ex]
    congr 1
    ext n
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨S', hS1, hS2, hS3, hS4⟩
      refine ⟨translateFinset (-v) S', ?_, ?_, ?_, ?_⟩
      · rw [← translateFinset_subset_iff v]
        have h_eq : translateFinset v (translateFinset (-v) S') = S' := by
          rw [translateFinset_compose]
          simp [translateFinset_zero]
        rw [h_eq]
        exact hS1
      · rw [← translateFinset_subset_iff v]
        have h_eq : translateFinset v (translateFinset (-v) S') = S' := by
          rw [translateFinset_compose]
          simp [translateFinset_zero]
        rw [h_eq]
        exact hS2
      · have := cubeConnected_translate S' (-v) hS3
        rwa [translateFinset] at this
      · rw [translateFinset_card]
        exact hS4
    · rintro ⟨S, hS1, hS2, hS3, hS4⟩
      refine ⟨translateFinset v S, ?_, ?_, ?_, ?_⟩
      · rw [translateFinset_subset_iff]
        exact hS1
      · rw [translateFinset_subset_iff]
        exact hS2
      · exact cubeConnected_translate S v hS3
      · rw [translateFinset_card, hS4]
  · have h_ex_trans : ¬ ∃ S : Finset (Cube d L), translateFinset v (skeleton H X) ⊆ S ∧ S ⊆ translateFinset v X ∧ cubeConnected S := by
      rwa [h_equiv]
    rw [dif_neg h_ex_trans, dif_neg h_ex]

/-- Polymer-with-holes translation-invariance. -/
lemma polymerWithHoles_translate {d L : ℕ} (H : HoleFamily d L) (X : Finset (Cube d L)) (v : Cube d L) :
    polymerWithHoles (translateHoleFamily H v) (translateFinset v X) ↔ polymerWithHoles H X := by
  unfold polymerWithHoles
  constructor
  · intro h H₀ hH₀
    have hH₀' : translateFinset v H₀ ∈ (translateHoleFamily H v).holes := by
      dsimp [translateHoleFamily]
      simp only [mem_map]
      refine ⟨H₀, hH₀, rfl⟩
    have h_spec := h (translateFinset v H₀) hH₀'
    change translateFinset v H₀ ⊆ translateFinset v X ∨ Disjoint (translateFinset v H₀) (translateFinset v X) at h_spec
    rw [translateFinset_subset_iff, translateFinset_disjoint_iff] at h_spec
    exact h_spec
  · intro h H₀' hH₀'
    dsimp [translateHoleFamily] at hH₀'
    simp only [mem_map] at hH₀'
    rcases hH₀' with ⟨H₀, hH₀, rfl⟩
    have h_spec := h H₀ hH₀
    change translateFinset v H₀ ⊆ translateFinset v X ∨ Disjoint (translateFinset v H₀) (translateFinset v X)
    rw [translateFinset_subset_iff, translateFinset_disjoint_iff]
    exact h_spec

/-- Translate a polymer. -/
def translatePolymer {d L : ℕ} (H : HoleFamily d L) (v : Cube d L)
    (X : { X : Finset (Cube d L) // X.Nonempty ∧ cubeConnected X ∧ polymerWithHoles H X }) :
    { X : Finset (Cube d L) // X.Nonempty ∧ cubeConnected X ∧ polymerWithHoles (translateHoleFamily H v) X } :=
  ⟨translateFinset v X.1, by
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := X.2.1
      exact ⟨x + v, by rw [mem_translateFinset_iff]; simpa using hx⟩
    · exact cubeConnected_translate X.1 v X.2.2.1
    · exact (polymerWithHoles_translate H X.1 v).mpr X.2.2.2⟩

lemma translatePolymer_injective {d L : ℕ} (H : HoleFamily d L) (v : Cube d L) :
    Function.Injective (translatePolymer H v) := by
  intro X Y h
  have h_eq : translateFinset v X.1 = translateFinset v Y.1 := by
    injection h
  have h_eq_val : X.1 = Y.1 := translateFinset_inj v h_eq
  exact Subtype.ext h_eq_val

lemma translatePolymer_surjective {d L : ℕ} (H : HoleFamily d L) (v : Cube d L) :
    Function.Surjective (translatePolymer H v) := by
  intro Y
  let X_val := translateFinset (-v) Y.1
  have h_nonempty : X_val.Nonempty := by
    obtain ⟨y, hy⟩ := Y.2.1
    refine ⟨y - v, ?_⟩
    dsimp [X_val]
    rw [mem_translateFinset_iff]
    simpa using hy
  have h_conn : cubeConnected X_val := by
    exact cubeConnected_translate Y.1 (-v) Y.2.2.1
  have h_pwh : polymerWithHoles H X_val := by
    have h1 := (polymerWithHoles_translate H X_val v).symm
    have h_trans : translateFinset v X_val = Y.1 := by
      dsimp [X_val]
      rw [translateFinset_compose]
      simp [translateFinset_zero]
    rw [h_trans] at h1
    exact h1.mpr Y.property.right.right
  refine ⟨⟨X_val, h_nonempty, h_conn, h_pwh⟩, ?_⟩
  ext1
  dsimp [translatePolymer, X_val]
  rw [translateFinset_compose]
  simp [translateFinset_zero]

lemma holePolymerSystem_incomp_translate {d L : ℕ} [NeZero L] (H : HoleFamily d L) (v : Cube d L)
    (X Y : { X : Finset (Cube d L) // X.Nonempty ∧ cubeConnected X ∧ polymerWithHoles H X }) :
    (¬ Disjoint (translateFinset v X.1) (translateFinset v Y.1) ∨
      ∃ x ∈ translateFinset v X.1, ∃ y ∈ translateFinset v Y.1, (cubeAdj d L).Adj x y) ↔
    (¬ Disjoint X.1 Y.1 ∨ ∃ x ∈ X.1, ∃ y ∈ Y.1, (cubeAdj d L).Adj x y) := by
  rw [translateFinset_disjoint_iff]
  constructor
  · rintro (hd | ⟨x_trans, hx, y_trans, hy, hadj⟩)
    · left; exact hd
    · right
      rw [mem_translateFinset_iff] at hx hy
      refine ⟨x_trans - v, hx, y_trans - v, hy, ?_⟩
      have h_eq : (cubeAdj d L).Adj (x_trans - v + v) (y_trans - v + v) := by
        simpa using hadj
      rwa [cubeAdj_adj_translate] at h_eq
  · rintro (hd | ⟨x, hx, y, hy, hadj⟩)
    · left; exact hd
    · right
      refine ⟨x + v, ?_, y + v, ?_, ?_⟩
      · rw [mem_translateFinset_iff]; simp [hx]
      · rw [mem_translateFinset_iff]; simp [hy]
      · rwa [cubeAdj_adj_translate]

/-- Translate a polymer activity function. -/
def translateActivity {d L : ℕ} (z : Finset (Cube d L) → ℂ) (v : Cube d L) : Finset (Cube d L) → ℂ :=
  fun S => z (translateFinset (-v) S)

lemma translateActivity_apply {d L : ℕ} (z : Finset (Cube d L) → ℂ) (v : Cube d L)
    (X : Finset (Cube d L)) :
    translateActivity z v (translateFinset v X) = z X := by
  dsimp [translateActivity]
  rw [translateFinset_compose]
  simp [translateFinset_zero]

/-- Rooted activity sum translation-invariance. -/
theorem rootedHolePolymerSum_translate {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (r : Cube d L) (v : Cube d L) :
    rootedHolePolymerSum (translateHoleFamily H v) (translateActivity z v) (r + v) = rootedHolePolymerSum H z r := by
  classical
  unfold rootedHolePolymerSum
  rw [tsum_fintype, tsum_fintype]
  let dom1 := { P : (holePolymerSystem (translateHoleFamily H v) (translateActivity z v)).Polymer // r + v ∈ skeleton (translateHoleFamily H v) P.1 }
  let dom2 := { P : (holePolymerSystem H z).Polymer // r ∈ skeleton H P.1 }
  let g : dom2 → dom1 := fun X =>
    ⟨translatePolymer H v X.1, by
      have hr : r ∈ skeleton H X.1.1 := X.property
      have h_trans : skeleton (translateHoleFamily H v) (translatePolymer H v X.1).1 = translateFinset v (skeleton H X.1.1) := by
        dsimp [translatePolymer]
        rw [skeleton_translate]
      rw [h_trans, mem_translateFinset_iff]
      simpa using hr⟩
  have h_inj : Function.Injective g := by
    intro a b hab
    have h_val_eq : (g a).1 = (g b).1 := congrArg Subtype.val hab
    have h_val_val_eq : (g a).1.1 = (g b).1.1 := congrArg Subtype.val h_val_eq
    have h_eq : translateFinset v a.1.1 = translateFinset v b.1.1 := h_val_val_eq
    have h_eq_val : a.1.1 = b.1.1 := translateFinset_inj v h_eq
    have h_p_eq : a.1 = b.1 := Subtype.ext h_eq_val
    exact Subtype.ext h_p_eq
  have h_surj : Function.Surjective g := by
    intro Y
    obtain ⟨X_poly, h_trans_poly⟩ := translatePolymer_surjective H v Y.1
    have hr : r ∈ skeleton H X_poly.1 := by
      have hr_trans : r + v ∈ skeleton (translateHoleFamily H v) Y.1.1 := Y.property
      rw [← h_trans_poly] at hr_trans
      have h_skel : skeleton (translateHoleFamily H v) (translatePolymer H v X_poly).1 = translateFinset v (skeleton H X_poly.1) := by
        dsimp [translatePolymer]
        rw [skeleton_translate]
      rw [h_skel, mem_translateFinset_iff] at hr_trans
      simpa using hr_trans
    let X_dom2 : dom2 := ⟨X_poly, hr⟩
    refine ⟨X_dom2, ?_⟩
    ext1
    exact h_trans_poly
  have h_sum_equiv : ∑ x : dom2, (holePolymerSystem (translateHoleFamily H v) (translateActivity z v)).activity (g x).1
      = ∑ y : dom1, (holePolymerSystem (translateHoleFamily H v) (translateActivity z v)).activity y.1 := by
    refine Fintype.sum_equiv (Equiv.ofBijective g ⟨h_inj, h_surj⟩) _ _ ?_
    intro x
    rfl
  rw [← h_sum_equiv]
  refine Finset.sum_congr rfl ?_
  intro x _
  dsimp [g, translatePolymer, holePolymerSystem]
  rw [translateActivity_apply]

end YangMills.RG
