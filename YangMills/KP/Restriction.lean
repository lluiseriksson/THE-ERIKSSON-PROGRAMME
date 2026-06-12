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

/-! ## R2 substrate: cluster data transports along the restriction -/

/-- The incompatibility graph of a restricted tuple is the ambient
incompatibility graph of its value tuple. -/
theorem incompGraph_restrict {P : PolymerSystem} (Λ : Finset P.Polymer)
    {n : ℕ} (X : Fin n → (P.restrict Λ).Polymer) :
    incompGraph (P.restrict Λ) X = incompGraph P (fun i => (X i).1) := rfl

/-- Ursell coefficients transport along the restriction (they read
only the incompatibility graph). -/
theorem ursell_restrict {P : PolymerSystem} (Λ : Finset P.Polymer)
    {n : ℕ} (X : Fin n → (P.restrict Λ).Polymer) :
    ursell (P.restrict Λ) X = ursell P (fun i => (X i).1) := rfl

/-- Activity products transport along the restriction. -/
theorem prod_activity_restrict {P : PolymerSystem} (Λ : Finset P.Polymer)
    {n : ℕ} (X : Fin n → (P.restrict Λ).Polymer) :
    ∏ i, (P.restrict Λ).activity (X i)
      = ∏ i, P.activity (X i).1 := rfl

open Classical in
/-- The `n`-th restricted cluster term in ambient terms: the tuple sum
over `↥Λ` is the ambient tuple sum filtered to tuples valued in `Λ`. -/
theorem clusterTerm_restrict {P : PolymerSystem} [Fintype P.Polymer]
    (Λ : Finset P.Polymer) (n : ℕ) :
    (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X : Fin (n + 1) → (P.restrict Λ).Polymer,
          (ursell (P.restrict Λ) X : ℂ) *
            ∏ i, (P.restrict Λ).activity (X i)
      = (((n + 1).factorial : ℂ))⁻¹ *
          ∑ X ∈ (Finset.univ :
              Finset (Fin (n + 1) → P.Polymer)).filter
              (fun X => ∀ i, X i ∈ Λ),
            (ursell P X : ℂ) * ∏ i, P.activity (X i) := by
  classical
  congr 1
  refine Finset.sum_bij'
    (fun X _ => fun k => (X k).1)
    (fun X hX => fun k => ⟨X k, (Finset.mem_filter.mp hX).2 k⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro X _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k => (X k).2⟩
  · intro X _
    exact Finset.mem_univ _
  · intro X _
    funext k
    exact Subtype.ext rfl
  · intro X _
    funext k
    rfl
  · intro X _
    rfl

open Classical in
/-- **The restricted cluster sum in ambient terms.** -/
theorem clusterSum_restrict {P : PolymerSystem} [Fintype P.Polymer]
    (Λ : Finset P.Polymer) :
    clusterSum (P.restrict Λ)
      = ∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
          ∑ X ∈ (Finset.univ :
              Finset (Fin (n + 1) → P.Polymer)).filter
              (fun X => ∀ i, X i ∈ Λ),
            (ursell P X : ℂ) * ∏ i, P.activity (X i) := by
  unfold clusterSum
  exact tsum_congr fun n => clusterTerm_restrict Λ n

open Classical in
/-- **R2(a) — the difference identity:** under the KP criterion, the
cluster sums of the full and restricted systems differ exactly by the
tuple sums MEETING `Λᶜ` — the object the pinned tail bounds. -/
theorem clusterSum_sub_restrict {P : PolymerSystem} [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (h : KPCriterion P a) (Λ : Finset P.Polymer) :
    clusterSum P - clusterSum (P.restrict Λ)
      = ∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
          ∑ X ∈ (Finset.univ :
              Finset (Fin (n + 1) → P.Polymer)).filter
              (fun X => ¬ ∀ i, X i ∈ Λ),
            (ursell P X : ℂ) * ∏ i, P.activity (X i) := by
  classical
  have hsum1 : Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → P.Polymer,
        (ursell P X : ℂ) * ∏ i, P.activity (X i)) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_clusterTerm_le P n)
      (kp_clusterWeight_summable_sharp P h))
  have hsum2R : Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → (P.restrict Λ).Polymer,
        (ursell (P.restrict Λ) X : ℂ) *
          ∏ i, (P.restrict Λ).activity (X i)) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_clusterTerm_le (P.restrict Λ) n)
      (kp_clusterWeight_summable_sharp (P.restrict Λ) (h.restrict Λ)))
  have hsum2 : Summable (fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => ∀ i, X i ∈ Λ),
        (ursell P X : ℂ) * ∏ i, P.activity (X i)) :=
    hsum2R.congr fun n => clusterTerm_restrict Λ n
  rw [clusterSum_restrict,
    show clusterSum P = ∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X : Fin (n + 1) → P.Polymer,
        (ursell P X : ℂ) * ∏ i, P.activity (X i) from rfl,
    ← hsum1.tsum_sub hsum2]
  refine tsum_congr fun n => ?_
  rw [← mul_sub]
  congr 1
  have hpart := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (n + 1) → P.Polymer))
    (fun X => ∀ i, X i ∈ Λ)
    (fun X => (ursell P X : ℂ) * ∏ i, P.activity (X i))
  rw [← hpart]
  ring

open Classical in
/-- The **off-region cluster weight**: the part of the per-size weight
`clusterWeight P n` carried by tuples MEETING `Λᶜ` — the majorant of
the R2 difference series. -/
noncomputable def offRegionClusterWeight (P : PolymerSystem)
    [Fintype P.Polymer] (Λ : Finset P.Polymer) (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X => ¬ ∀ i, X i ∈ Λ),
      |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖

open Classical in
theorem offRegionClusterWeight_nonneg (P : PolymerSystem)
    [Fintype P.Polymer] (Λ : Finset P.Polymer) (n : ℕ) :
    0 ≤ offRegionClusterWeight P Λ n := by
  unfold offRegionClusterWeight
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun X _ => ?_)
  exact mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)

open Classical in
/-- The off-region weight is dominated by the total per-size weight. -/
theorem offRegionClusterWeight_le_clusterWeight (P : PolymerSystem)
    [Fintype P.Polymer] (Λ : Finset P.Polymer) (n : ℕ) :
    offRegionClusterWeight P Λ n ≤ clusterWeight P n := by
  unfold offRegionClusterWeight clusterWeight
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) fun X _ _ => ?_
  exact mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)

open Classical in
/-- **R2(b1) — term-wise norm bound for the difference series:** the
`n`-th term of the R2 difference is bounded by the off-region weight. -/
theorem norm_diffTerm_le (P : PolymerSystem) [Fintype P.Polymer]
    (Λ : Finset P.Polymer) (n : ℕ) :
    ‖(((n + 1).factorial : ℂ))⁻¹ *
        ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun X => ¬ ∀ i, X i ∈ Λ),
          (ursell P X : ℂ) * ∏ i, P.activity (X i)‖
      ≤ offRegionClusterWeight P Λ n := by
  unfold offRegionClusterWeight
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun X _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_right (le_of_eq ?_)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  rw [show ((ursell P X : ℤ) : ℂ)
      = (((ursell P X : ℤ) : ℝ) : ℂ) from by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

open Classical in
/-- **R2(b2) — the `Z`-ratio exponent bound:** under the KP criterion,
the difference of cluster sums is bounded by the off-region tail.
Combined with R1, `‖log(Z_Λ/Z)‖ ≤ ∑' n, offRegionClusterWeight P Λ n`
— the quantity the pinned decomposition renders volume-free. -/
theorem norm_clusterSum_sub_restrict_le (P : PolymerSystem)
    [Fintype P.Polymer] {a : P.Polymer → ℝ} (h : KPCriterion P a)
    (Λ : Finset P.Polymer) :
    ‖clusterSum P - clusterSum (P.restrict Λ)‖
      ≤ ∑' n : ℕ, offRegionClusterWeight P Λ n := by
  classical
  have hOff : Summable (fun n => offRegionClusterWeight P Λ n) :=
    Summable.of_nonneg_of_le
      (fun n => offRegionClusterWeight_nonneg P Λ n)
      (fun n => offRegionClusterWeight_le_clusterWeight P Λ n)
      (kp_clusterWeight_summable_sharp P h)
  have hnorm : Summable (fun n : ℕ =>
      ‖(((n + 1).factorial : ℂ))⁻¹ *
        ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun X => ¬ ∀ i, X i ∈ Λ),
          (ursell P X : ℂ) * ∏ i, P.activity (X i)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_diffTerm_le P Λ n) hOff
  rw [clusterSum_sub_restrict h Λ]
  refine le_trans (norm_tsum_le_tsum_norm hnorm) ?_
  exact hnorm.tsum_le_tsum (fun n => norm_diffTerm_le P Λ n) hOff

open Classical in
/-- **R2(b3) — the index union bound:** the off-region weight is
controlled by the pinned weights at the polymers OUTSIDE `Λ`: swap any
escaping index to position 0 (`ursell` is permutation-invariant), then
fiber over the pinned polymer. -/
theorem offRegionClusterWeight_le_pinned (P : PolymerSystem)
    [Fintype P.Polymer] (Λ : Finset P.Polymer) (n : ℕ) :
    offRegionClusterWeight P Λ n
      ≤ ((n : ℝ) + 1) * ∑ c ∈ Λᶜ, pinnedClusterWeight P c n := by
  classical
  unfold offRegionClusterWeight pinnedClusterWeight
  set f : (Fin (n + 1) → P.Polymer) → ℝ :=
    fun X => |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖ with hf
  have hf0 : ∀ X, 0 ≤ f X := fun X =>
    mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hfswap : ∀ (σ : Equiv.Perm (Fin (n + 1)))
      (X : Fin (n + 1) → P.Polymer), f (X ∘ σ) = f X := by
    intro σ X
    rw [hf]
    simp only
    rw [ursell_comp_equiv P X σ]
    congr 1
    exact Equiv.prod_comp σ (fun k => ‖P.activity (X k)‖)
  have hidx : ∀ i : Fin (n + 1),
      ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
        (fun X => X i ∉ Λ), f X
      = ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
          (fun Y => Y 0 ∉ Λ), f Y := by
    intro i
    refine Finset.sum_nbij' (i := fun X => X ∘ Equiv.swap 0 i)
      (j := fun Y => Y ∘ Equiv.swap 0 i) ?_ ?_ ?_ ?_ ?_
    · intro X hX
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show (X ∘ Equiv.swap 0 i) 0 ∉ Λ
      have h0 : (X ∘ Equiv.swap 0 i) 0 = X i := by
        simp [Function.comp, Equiv.swap_apply_left]
      rw [h0]
      exact (Finset.mem_filter.mp hX).2
    · intro Y hY
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show (Y ∘ Equiv.swap 0 i) i ∉ Λ
      have h0 : (Y ∘ Equiv.swap 0 i) i = Y 0 := by
        simp [Function.comp, Equiv.swap_apply_right]
      rw [h0]
      exact (Finset.mem_filter.mp hY).2
    · intro X _
      funext k
      simp [Function.comp, Equiv.swap_apply_self]
    · intro Y _
      funext k
      simp [Function.comp, Equiv.swap_apply_self]
    · intro X _
      exact (hfswap _ X).symm
  have hmain : ∑ X ∈ (Finset.univ :
      Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X => ¬ ∀ i, X i ∈ Λ), f X
      ≤ ((n : ℝ) + 1) * ∑ c ∈ Λᶜ,
          ∑ Y ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun Y => Y 0 = c), f Y := by
    calc ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => ¬ ∀ i, X i ∈ Λ), f X
        ≤ ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun X => ¬ ∀ i, X i ∈ Λ),
            ∑ i : Fin (n + 1), if X i ∉ Λ then f X else 0 := by
          refine Finset.sum_le_sum fun X hX => ?_
          obtain ⟨i₀, hi₀⟩ : ∃ i, X i ∉ Λ := by
            have hm := (Finset.mem_filter.mp hX).2
            push_neg at hm
            exact hm
          have hX0 : f X = if X i₀ ∉ Λ then f X else 0 := by
            rw [if_pos hi₀]
          refine le_trans (le_of_eq hX0) ?_
          refine Finset.single_le_sum
            (f := fun i => if X i ∉ Λ then f X else 0)
            (fun i _ => ?_) (Finset.mem_univ i₀)
          show (0 : ℝ) ≤ if X i ∉ Λ then f X else 0
          split_ifs
          · exact le_rfl
          · exact hf0 X
      _ ≤ ∑ X : Fin (n + 1) → P.Polymer,
            ∑ i : Fin (n + 1), if X i ∉ Λ then f X else 0 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun X _ _ => ?_
          refine Finset.sum_nonneg fun i _ => ?_
          show (0 : ℝ) ≤ if X i ∉ Λ then f X else 0
          split_ifs
          · exact le_rfl
          · exact hf0 X
      _ = ∑ i : Fin (n + 1), ∑ X : Fin (n + 1) → P.Polymer,
            if X i ∉ Λ then f X else 0 := Finset.sum_comm
      _ = ∑ i : Fin (n + 1), ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun X => X i ∉ Λ), f X := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (Finset.sum_filter _ _).symm
      _ = ∑ _i : Fin (n + 1), ∑ Y ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun Y => Y 0 ∉ Λ), f Y :=
          Finset.sum_congr rfl fun i _ => hidx i
      _ = ((n : ℝ) + 1) * ∑ Y ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun Y => Y 0 ∉ Λ), f Y := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
      _ = ((n : ℝ) + 1) * ∑ c ∈ Λᶜ,
            ∑ Y ∈ (Finset.univ :
              Finset (Fin (n + 1) → P.Polymer)).filter
              (fun Y => Y 0 = c), f Y := by
          congr 1
          rw [← Finset.sum_fiberwise_of_maps_to (g := fun Y => Y 0)
            (fun Y hY => Finset.mem_compl.mpr
              (Finset.mem_filter.mp hY).2) f]
          refine Finset.sum_congr rfl fun c hc => ?_
          rw [Finset.filter_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          refine Finset.filter_congr fun Y _ => ?_
          constructor
          · exact fun h => h.2
          · refine fun h => ⟨?_, h⟩
            show Y 0 ∉ Λ
            have h' : Y 0 = c := h
            rw [h']
            exact Finset.mem_compl.mp hc
  calc (((n + 1).factorial : ℝ))⁻¹ * ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter
        (fun X => ¬ ∀ i, X i ∈ Λ), f X
      ≤ (((n + 1).factorial : ℝ))⁻¹ * (((n : ℝ) + 1) * ∑ c ∈ Λᶜ,
          ∑ Y ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun Y => Y 0 = c), f Y) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = ((n : ℝ) + 1) * ((((n + 1).factorial : ℝ))⁻¹ * ∑ c ∈ Λᶜ,
          ∑ Y ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun Y => Y 0 = c), f Y) := by ring
    _ = ((n : ℝ) + 1) * ∑ c ∈ Λᶜ, (((n + 1).factorial : ℝ))⁻¹ *
          ∑ Y ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun Y => Y 0 = c), f Y := by
        rw [Finset.mul_sum]

/-! ## R2(b4) substrate: the scalar activity tilt -/

/-- The **scalar activity tilt**: multiply every activity by `r`
(same polymers, same incompatibility).  Each size-`(n+1)` tuple picks
up `|r|^(n+1)`, which absorbs polynomial factors in `n`. -/
noncomputable def PolymerSystem.scaleActivity (P : PolymerSystem)
    (r : ℝ) : PolymerSystem where
  Polymer := P.Polymer
  incomp := P.incomp
  incomp_symm := P.incomp_symm
  incomp_self := P.incomp_self
  activity X := (r : ℂ) * P.activity X

noncomputable instance (P : PolymerSystem) [Fintype P.Polymer] (r : ℝ) :
    Fintype (P.scaleActivity r).Polymer :=
  inferInstanceAs (Fintype P.Polymer)

open Classical in
/-- Pinned weights of the tilted system: each tuple of size `n+1`
carries `|r|^(n+1)`. -/
theorem pinnedClusterWeight_scale (P : PolymerSystem)
    [Fintype P.Polymer] (r : ℝ) (c : P.Polymer) (n : ℕ) :
    pinnedClusterWeight (P.scaleActivity r) c n
      = |r| ^ (n + 1) * pinnedClusterWeight P c n := by
  unfold pinnedClusterWeight
  have hsum : ∑ X ∈ (Finset.univ :
      Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
      |((ursell (P.scaleActivity r) X : ℤ) : ℝ)| *
        ∏ i, ‖(P.scaleActivity r).activity (X i)‖
      = |r| ^ (n + 1) * ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter (fun X => X 0 = c),
          |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun X _ => ?_
    show |((ursell P X : ℤ) : ℝ)| *
        ∏ i, ‖(r : ℂ) * P.activity (X i)‖ = _
    have hprod : ∏ i : Fin (n + 1), ‖(r : ℂ) * P.activity (X i)‖
        = |r| ^ (n + 1) * ∏ i, ‖P.activity (X i)‖ := by
      calc ∏ i : Fin (n + 1), ‖(r : ℂ) * P.activity (X i)‖
          = ∏ i : Fin (n + 1), |r| * ‖P.activity (X i)‖ := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ = |r| ^ (n + 1) * ∏ i, ‖P.activity (X i)‖ := by
            rw [Finset.prod_mul_distrib, Finset.prod_const,
              Finset.card_univ, Fintype.card_fin]
    rw [hprod]
    ring
  exact (congrArg (fun s => (((n + 1).factorial : ℝ))⁻¹ * s) hsum).trans
    (by ring)

open Classical in
/-- **R2(b4) — THE VOLUME-FREE `Z`-RATIO EXPONENT BOUND:** under the
`e^t`-tilted KP criterion (exactly what the lattice gas verifies), the
off-region tail — hence `‖log(Z_Λ/Z)‖` — is bounded by a sum over the
polymers OUTSIDE `Λ` only. -/
theorem tsum_offRegionClusterWeight_le (P : PolymerSystem)
    [Fintype P.Polymer] {a : P.Polymer → ℝ} (t : ℝ) (ht : 0 < t)
    (hkp : KPCriterion (P.scaleActivity (Real.exp t)) a)
    (Λ : Finset P.Polymer) :
    ∑' n : ℕ, offRegionClusterWeight P Λ n
      ≤ t⁻¹ * ∑ c ∈ Λᶜ,
          Real.exp t * ‖P.activity c‖ * Real.exp (a c) := by
  classical
  have hle : ∀ n, offRegionClusterWeight P Λ n
      ≤ t⁻¹ * ∑ c ∈ Λᶜ,
          pinnedClusterWeight (P.scaleActivity (Real.exp t)) c n := by
    intro n
    refine le_trans (offRegionClusterWeight_le_pinned P Λ n) ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have hfac : ((n : ℝ) + 1) ≤ t⁻¹ * Real.exp t ^ (n + 1) := by
      have h1 : t * ((n : ℝ) + 1) ≤ Real.exp (t * ((n : ℝ) + 1)) := by
        have h2 := Real.add_one_le_exp (t * ((n : ℝ) + 1))
        linarith
      have h3 : (Real.exp t : ℝ) ^ (n + 1)
          = Real.exp (t * ((n : ℝ) + 1)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [h3]
      exact (le_inv_mul_iff₀ ht).mpr h1
    calc ((n : ℝ) + 1) * pinnedClusterWeight P c n
        ≤ (t⁻¹ * Real.exp t ^ (n + 1)) * pinnedClusterWeight P c n :=
          mul_le_mul_of_nonneg_right hfac
            (pinnedClusterWeight_nonneg P c n)
      _ = t⁻¹ * pinnedClusterWeight
            (P.scaleActivity (Real.exp t)) c n := by
          rw [pinnedClusterWeight_scale,
            abs_of_pos (Real.exp_pos t)]
          ring
  have hgsum : Summable (fun n => t⁻¹ * ∑ c ∈ Λᶜ,
      pinnedClusterWeight (P.scaleActivity (Real.exp t)) c n) := by
    refine Summable.mul_left _ ?_
    exact summable_sum fun c _ =>
      (pinned_cluster_summable_sharp _ hkp c).1
  have hOffSum : Summable (fun n => offRegionClusterWeight P Λ n) :=
    Summable.of_nonneg_of_le
      (fun n => offRegionClusterWeight_nonneg P Λ n) hle hgsum
  refine le_trans (hOffSum.tsum_le_tsum hle hgsum) ?_
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr ht.le)
  have hswap := Summable.tsum_finsetSum
    (s := Λᶜ)
    (f := fun c n => pinnedClusterWeight
      (P.scaleActivity (Real.exp t)) c n)
    (fun c _ => (pinned_cluster_summable_sharp _ hkp c).1)
  refine le_trans (le_of_eq hswap) ?_
  refine Finset.sum_le_sum fun c _ => ?_
  refine le_trans (pinned_cluster_summable_sharp _ hkp c).2 (le_of_eq ?_)
  show ‖((Real.exp t : ℝ) : ℂ) * P.activity c‖ * Real.exp (a c) = _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos t)]

open Classical in
/-- **Vanishing activities drop from the partition function:** if the
activities vanish off `Λ`, the full-volume partition function IS the
`Λ`-restricted one.  This is the R3 truncation device: the
region-restricted lattice `Z` is the FULL weighted partition of the
truncated weight `w·1_F`, and this lemma collapses the truncated gas
to the `F`-polymers. -/
theorem partition_eq_of_activity_eq_zero (P : PolymerSystem)
    [Fintype P.Polymer] (Λ : Finset P.Polymer)
    (hz : ∀ X, X ∉ Λ → P.activity X = 0) :
    partition P (Finset.univ : Finset P.Polymer) = partition P Λ := by
  classical
  unfold partition
  refine (Finset.sum_subset ?_ ?_).symm
  · intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hS.2⟩
  · intro S hS hSnot
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    have hns : ¬ S ⊆ Λ := fun hsub =>
      hSnot (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsub, hS.2⟩)
    obtain ⟨X, hXS, hXΛ⟩ := Finset.not_subset.mp hns
    exact Finset.prod_eq_zero hXS (hz X hXΛ)

open Classical in
/-- **The KP criterion is monotone in activity norms** (same polymers,
same incompatibility): dominated activities inherit the criterion.
This bridges the banked size-tilted lattice criteria to the uniform
`scaleActivity` tilt that `tsum_offRegionClusterWeight_le` consumes. -/
theorem KPCriterion.of_activity_norm_le {P : PolymerSystem}
    [Fintype P.Polymer] {z₁ z₂ : P.Polymer → ℂ} {a : P.Polymer → ℝ}
    (hz : ∀ c, ‖z₁ c‖ ≤ ‖z₂ c‖)
    (h : KPCriterion { P with activity := z₂ } a) :
    KPCriterion { P with activity := z₁ } a := by
  refine ⟨h.1, fun X => ?_⟩
  refine le_trans (Finset.sum_le_sum fun Y _ => ?_) (h.2 X)
  exact mul_le_mul_of_nonneg_right (hz Y) (Real.exp_pos _).le

/-- **The exponential-ratio bound (V2-3 substrate):** partition
functions given as `exp(clusterSum)` never vanish, and their norm
ratios are controlled by the cluster-sum difference — the form in
which the `Z`-ratio enters the pinned sum. -/
theorem norm_exp_div_norm_exp_le (a b : ℂ) {C : ℝ}
    (h : ‖a - b‖ ≤ C) :
    ‖Complex.exp b‖ / ‖Complex.exp a‖ ≤ Real.exp C := by
  rw [Complex.norm_exp, Complex.norm_exp, ← Real.exp_sub]
  refine Real.exp_le_exp.mpr ?_
  have h1 : b.re - a.re ≤ |(b - a).re| := by
    rw [Complex.sub_re]
    exact le_abs_self _
  refine le_trans h1 (le_trans (Complex.abs_re_le_norm _) ?_)
  rw [show b - a = -(a - b) from by ring, norm_neg]
  exact h

end YangMills.KP
