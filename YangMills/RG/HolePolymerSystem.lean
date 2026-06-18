/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.KP.Basic
import YangMills.RG.ModifiedMetric

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

/-- The **holes-respected polymer system** on the cube lattice.
    Polymers are nonempty, connected finsets of cubes that respect the hole family H.
    Two polymers are incompatible if they overlap or touch (share a boundary of any dimension). -/
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

end YangMills.RG
