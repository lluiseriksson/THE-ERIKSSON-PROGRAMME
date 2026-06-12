/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Basic
import YangMills.KP.MayerInversion

/-!
# Restriction of a polymer system to a sub-volume (VU campaign, R1)

`docs/AREA-LAW-VU-PLAN.md` brick R1: the finite-volume partition
function `partition P Λ` is the FULL-volume partition function of the
restricted system `P.restrict Λ` (polymers = `↥Λ`, inherited
incompatibility and activities).  This reduces the volume-restricted
Mayer inversion — the engine of the `Z`-ratio bound — to the banked
`univ`-version applied to `P.restrict Λ`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped Classical BigOperators

/-- The **restriction** of a polymer system to a sub-volume `Λ`:
polymers are the elements of `Λ`, incompatibility and activities are
inherited. -/
noncomputable def PolymerSystem.restrict (P : PolymerSystem)
    (Λ : Finset P.Polymer) : PolymerSystem where
  Polymer := ↥Λ
  incomp X Y := P.incomp X.1 Y.1
  incomp_symm X Y h := P.incomp_symm _ _ h
  incomp_self X := P.incomp_self _
  activity X := P.activity X.1

noncomputable instance (P : PolymerSystem) (Λ : Finset P.Polymer) :
    Fintype (P.restrict Λ).Polymer := by
  classical
  exact inferInstanceAs (Fintype ↥Λ)

open Classical in
/-- **R1 transfer:** the finite-volume partition function is the
full-volume partition function of the restricted system. -/
theorem partition_restrict (P : PolymerSystem) (Λ : Finset P.Polymer) :
    partition P Λ
      = partition (P.restrict Λ)
          (Finset.univ : Finset (P.restrict Λ).Polymer) := by
  classical
  unfold partition
  refine Finset.sum_nbij'
    (i := fun S => S.subtype (· ∈ Λ))
    (j := fun S' => S'.map (Function.Embedding.subtype (· ∈ Λ)))
    ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro S hS
    have hS' := Finset.mem_filter.mp hS
    have hSΛ := Finset.mem_powerset.mp hS'.1
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    intro X hX Y hY hne
    exact hS'.2 X.1 (Finset.mem_subtype.mp hX) Y.1
      (Finset.mem_subtype.mp hY) (fun hval => hne (Subtype.ext hval))
  · -- backward membership
    intro S' hS'
    have h2 := (Finset.mem_filter.mp hS').2
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hx
      exact a.2
    · intro x hx y hy hne
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
      exact h2 a ha b hb (fun hab => hne (congrArg _ hab))
  · -- left inverse
    intro S hS
    have hSΛ := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    show (S.subtype (· ∈ Λ)).map
      (Function.Embedding.subtype (· ∈ Λ)) = S
    rw [Finset.subtype_map]
    exact Finset.filter_true_of_mem fun x hx => hSΛ hx
  · -- right inverse
    intro S' _
    refine Finset.ext fun X => ?_
    refine Iff.trans Finset.mem_subtype ?_
    refine Iff.trans Finset.mem_map ?_
    constructor
    · rintro ⟨a, ha, hval⟩
      rwa [show a = X from Subtype.ext hval] at ha
    · intro hX
      exact ⟨X, hX, rfl⟩
  · -- value transfer
    intro S hS
    have hSΛ := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hrec : S = (S.subtype (· ∈ Λ)).map
        (Function.Embedding.subtype (· ∈ Λ)) := by
      rw [Finset.subtype_map]
      exact (Finset.filter_true_of_mem fun x hx => hSΛ hx).symm
    calc ∏ X ∈ S, P.activity X
        = ∏ X ∈ (S.subtype (· ∈ Λ)).map
            (Function.Embedding.subtype (· ∈ Λ)), P.activity X := by
          rw [← hrec]
      _ = ∏ X ∈ S.subtype (· ∈ Λ),
            P.activity ((Function.Embedding.subtype (· ∈ Λ)) X) :=
          Finset.prod_map _ _ _
      _ = ∏ X ∈ S.subtype (· ∈ Λ), (P.restrict Λ).activity X := rfl

open Classical in
/-- **The KP criterion restricts:** the restricted system inherits the
criterion with the restricted weight — its criterion sums are sub-sums
of the ambient ones. -/
theorem KPCriterion.restrict {P : PolymerSystem} [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (h : KPCriterion P a) (Λ : Finset P.Polymer) :
    KPCriterion (P.restrict Λ) (fun X => a X.1) := by
  classical
  refine ⟨fun X => h.1 X.1, fun X => ?_⟩
  have hsub : ((Finset.univ : Finset (P.restrict Λ).Polymer).filter
      (fun Y => (P.restrict Λ).incomp X Y)).map
        (Function.Embedding.subtype (· ∈ Λ))
      ⊆ (Finset.univ : Finset P.Polymer).filter
        (fun Y => P.incomp X.1 Y) := by
    intro y hy
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_map.mp hy
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hY).2⟩
  calc ∑ Y ∈ (Finset.univ : Finset (P.restrict Λ).Polymer).filter
        (fun Y => (P.restrict Λ).incomp X Y),
        ‖(P.restrict Λ).activity Y‖ * Real.exp (a Y.1)
      = ∑ y ∈ ((Finset.univ : Finset (P.restrict Λ).Polymer).filter
          (fun Y => (P.restrict Λ).incomp X Y)).map
            (Function.Embedding.subtype (· ∈ Λ)),
          ‖P.activity y‖ * Real.exp (a y) :=
        (Finset.sum_map
          ((Finset.univ : Finset (P.restrict Λ).Polymer).filter
            (fun Y => (P.restrict Λ).incomp X Y))
          (Function.Embedding.subtype (· ∈ Λ))
          (fun y => ‖P.activity y‖ * Real.exp (a y))).symm
    _ ≤ ∑ y ∈ (Finset.univ : Finset P.Polymer).filter
          (fun Y => P.incomp X.1 Y),
          ‖P.activity y‖ * Real.exp (a y) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun y _ _ => by positivity)
    _ ≤ a X.1 := h.2 X.1

open Classical in
/-- **The volume-restricted Mayer–Ursell inversion (R1 complete):**
under the ambient KP criterion, EVERY finite-volume partition function
is the exponential of its restricted system's cluster sum.  The
`Z`-ratio of two volumes is therefore the exponential of a DIFFERENCE
of cluster sums — the object the volume-uniform bound (R2) controls. -/
theorem partition_eq_exp_clusterSum_restrict {P : PolymerSystem}
    [Fintype P.Polymer] {a : P.Polymer → ℝ} (h : KPCriterion P a)
    (Λ : Finset P.Polymer) :
    partition P Λ = Complex.exp (clusterSum (P.restrict Λ)) := by
  rw [partition_restrict P Λ]
  exact partition_eq_exp_clusterSum_of_kp _ (h.restrict Λ)

end YangMills.KP
