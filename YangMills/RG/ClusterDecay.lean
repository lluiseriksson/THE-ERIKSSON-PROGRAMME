/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.HolePolymerSystem
import YangMills.RG.ModifiedMetric
import YangMills.RG.LocalKP
import YangMills.KP.Cluster
import YangMills.KP.Ursell

attribute [local instance] Classical.propDecidable

open Finset

namespace YangMills.RG

/-- The union of all polymers in a cluster. -/
def clusterUnion {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    {n : ℕ} (X : Fin n → (holePolymerSystem H z).Polymer) : Finset (Cube d L) :=
  univ.biUnion (fun i => (X i).val)

/-- The modified metric of a cluster, defined as the modified metric of its union. -/
noncomputable def clusterModifiedMetric {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    {n : ℕ} (X : Fin n → (holePolymerSystem H z).Polymer) : ℕ :=
  discreteModifiedMetric H (clusterUnion H z X)

lemma skeleton_biUnion {d L : ℕ} {α : Type*} [DecidableEq α] (H : HoleFamily d L) (S : Finset α) (F : α → Finset (Cube d L)) :
    skeleton H (S.biUnion F) = S.biUnion (fun a => skeleton H (F a)) := by
  unfold skeleton
  ext x
  simp only [mem_filter, mem_biUnion]
  constructor
  · rintro ⟨⟨a, ha, hx⟩, hnot⟩
    exact ⟨a, ha, hx, hnot⟩
  · rintro ⟨a, ha, hx, hnot⟩
    exact ⟨⟨a, ha, hx⟩, hnot⟩

lemma clusterUnion_skeleton {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    {n : ℕ} (X : Fin n → (holePolymerSystem H z).Polymer) :
    skeleton H (clusterUnion H z X) = univ.biUnion (fun i => skeleton H (X i).val) := by
  dsimp [clusterUnion]
  exact skeleton_biUnion H univ (fun i => (X i).val)

lemma clusterUnion_fin_one {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (X : Fin 1 → (holePolymerSystem H z).Polymer) :
    clusterUnion H z X = (X 0).val := by
  dsimp [clusterUnion]
  ext x
  simp only [mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hx⟩
    have : i = 0 := Subsingleton.elim i 0
    rw [this] at hx
    exact hx
  · intro hx
    exact ⟨0, hx⟩

lemma clusterModifiedMetric_fin_one {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (X : Fin 1 → (holePolymerSystem H z).Polymer) :
    clusterModifiedMetric H z X = discreteModifiedMetric H (X 0).val := by
  dsimp [clusterModifiedMetric]
  rw [clusterUnion_fin_one]

/-- The decay weight function of a cluster under the modified metric. -/
noncomputable def clusterDecayWeight {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (q : ℝ) {n : ℕ} (X : Fin n → (holePolymerSystem H z).Polymer) : ℝ :=
  q ^ (clusterModifiedMetric H z X + 1)

lemma clusterDecayWeight_fin_one {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (q : ℝ) (X : Fin 1 → (holePolymerSystem H z).Polymer) :
    clusterDecayWeight H z q X = q ^ (discreteModifiedMetric H (X 0).val + 1) := by
  dsimp [clusterDecayWeight]
  rw [clusterModifiedMetric_fin_one]

end YangMills.RG
