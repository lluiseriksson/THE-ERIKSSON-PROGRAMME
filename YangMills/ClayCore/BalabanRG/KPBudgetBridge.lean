import Mathlib
import YangMills.ClayCore.BalabanRG.KPFiniteTailBound
import YangMills.ClayCore.BalabanRG.PolymerPartitionFunction

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPBudgetBridge -- Layer 3B

Bridge: KPOnGamma -> SmallActivityBudget.
This file: base cases + singleton + insert-split lemma skeleton.
-/

noncomputable section

def CompatibleFamilyMajorant {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (B : ℝ) : Prop :=
  ∑ S ∈ (compatibleSubfamilies Gamma).erase ∅, ∏ X ∈ S, |K X| ≤ B

theorem compatibleFamilyMajorant_implies_smallActivityBudget {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (B : ℝ)
    (h : CompatibleFamilyMajorant Gamma K B) :
    SmallActivityBudget Gamma K B := h

theorem abs_Z_sub_one_le_of_majorant {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (B : ℝ)
    (h : CompatibleFamilyMajorant Gamma K B) :
    |polymerPartitionFunction Gamma K - 1| ≤ B :=
  abs_polymerPartitionFunction_sub_one_le Gamma K B h

/-! ## Base cases -/

-- L39 fix: unfold CompatibleFamilyMajorant, then show erase gives empty sum
theorem compatibleFamilyMajorant_empty {d : ℕ} {L : ℤ} (K : Activity d L) :
    CompatibleFamilyMajorant (∅ : Finset (Polymer d L)) K 0 := by
  unfold CompatibleFamilyMajorant
  have h : compatibleSubfamilies (∅ : Finset (Polymer d L)) = {∅} := by
    ext S
    constructor
    · intro hS
      rw [mem_compatibleSubfamilies_iff] at hS
      have hEq : S = ∅ := Finset.subset_empty.mp hS.1
      simp [hEq]
    · intro hS
      simp only [Finset.mem_singleton] at hS
      subst hS
      exact empty_mem_compatibleSubfamilies ∅
  rw [h, Finset.erase_singleton, Finset.sum_empty]

theorem smallActivityBudget_empty {d : ℕ} {L : ℤ} (K : Activity d L) :
    SmallActivityBudget (∅ : Finset (Polymer d L)) K 0 :=
  compatibleFamilyMajorant_empty K

/-! ## Singleton case -/

theorem compatibleSubfamilies_singleton_erase_empty {d : ℕ} {L : ℤ}
    (X : Polymer d L) :
    (compatibleSubfamilies ({X} : Finset (Polymer d L))).erase ∅ = {{X}} := by
  ext S
  simp only [Finset.mem_erase, mem_compatibleSubfamilies_iff, Finset.mem_singleton]
  constructor
  · intro ⟨hne, hsub, _⟩
    rcases Finset.subset_singleton_iff.mp hsub with rfl | rfl
    · exact absurd rfl hne
    · rfl
  · intro h
    subst h
    refine ⟨Finset.singleton_ne_empty X, ?_, compatibleSubfamily_singleton X⟩
    intro Y hY; exact hY

theorem singleton_activity_bound_implies_majorant {d : ℕ} {L : ℤ}
    (K : Activity d L) (X : Polymer d L) (B : ℝ) (hB : |K X| ≤ B) :
    CompatibleFamilyMajorant ({X} : Finset (Polymer d L)) K B := by
  unfold CompatibleFamilyMajorant
  rw [compatibleSubfamilies_singleton_erase_empty]
  simp [partitionWeight, hB]

theorem kpOnGamma_singleton_budget {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ) (X : Polymer d L)
    (hKP : KPOnGamma ({X} : Finset (Polymer d L)) K a) :
    CompatibleFamilyMajorant ({X} : Finset (Polymer d L)) K
      (a * Real.exp (-a * (X.size : ℝ))) := by
  apply singleton_activity_bound_implies_majorant
  obtain ⟨x, hx⟩ := X.nonEmpty
  -- L92 fix: build hsingle without constructor (simp already closes both directions)
  have hsingle : touchingPolymers ({X} : Finset (Polymer d L)) x =
      ({X} : Finset (Polymer d L)) := by
    ext Y
    simp only [mem_touchingPolymers_iff, Finset.mem_singleton, Polymer.Touches]
    exact ⟨fun h => h.1, fun h => by subst h; exact ⟨rfl, hx⟩⟩
  have hbound := kpOnGamma_singleton_touching_bound hKP hsingle
  simp only [weightedActivity] at hbound
  have hexp : 0 < Real.exp (a * (X.size : ℝ)) := Real.exp_pos _
  calc |K X|
      ≤ a / Real.exp (a * (X.size : ℝ)) :=
          (le_div_iff₀ hexp).mpr (by linarith)
    _ = a * (Real.exp (a * (X.size : ℝ)))⁻¹ := by rw [div_eq_mul_inv]
    _ = a * Real.exp (-(a * (X.size : ℝ))) := by rw [← Real.exp_neg]
    _ = a * Real.exp (-a * (X.size : ℝ)) := by congr 1; ring

end

/-!
## Next: compatibleSubfamilies_insert_split

Key combinatorial lemma for the full induction:

  theorem compatibleSubfamilies_insert_split (X : Polymer d L)
      (hX : X ∉ Gamma) :
      (compatibleSubfamilies (insert X Gamma)).erase ∅ =
      -- subfamilies NOT containing X (= compatibleSubfamilies Gamma erase empty)
      (compatibleSubfamilies Gamma).erase ∅
      -- subfamilies containing X (= {insert X S | S compatible in Gamma, S disjoint from {X}})
      ∪ Finset.image (insert X) (compatibleSubfamilies Gamma)

This split + Finset.sum_union (disjoint) + IH closes the induction.
-/



/-! ## Insert-split: key combinatorial lemma for induction -/

/-- Subfamilies of Gamma that do NOT contain X.
    These are exactly the subfamilies that can be extended by inserting X. -/
noncomputable def compatibleSubfamiliesAvoidingX {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (X : Polymer d L) :
    Finset (Finset (Polymer d L)) :=
  (compatibleSubfamilies Gamma).filter
    (fun S => X ∉ S ∧ ∀ Y ∈ S, Polymer.Compatible X Y)

theorem mem_compatibleSubfamiliesAvoidingX_iff {d : ℕ} {L : ℤ}
    {Gamma : Finset (Polymer d L)} {X : Polymer d L}
    {S : Finset (Polymer d L)} :
    S ∈ compatibleSubfamiliesAvoidingX Gamma X ↔
    S ∈ compatibleSubfamilies Gamma ∧ X ∉ S ∧ ∀ Y ∈ S, Polymer.Compatible X Y := by
  simp [compatibleSubfamiliesAvoidingX, Finset.mem_filter]

/-- A compatible subfamily of insert X Gamma that avoids X
    is also a compatible subfamily of Gamma. -/
theorem compatibleSubfamilies_insert_avoiding {d : ℕ} {L : ℤ}
    {Gamma : Finset (Polymer d L)} {X : Polymer d L}
    {S : Finset (Polymer d L)}
    (hS : S ∈ compatibleSubfamilies (insert X Gamma)) (hXS : X ∉ S) :
    S ∈ compatibleSubfamilies Gamma := by
  rw [mem_compatibleSubfamilies_iff] at hS ⊢
  refine ⟨?_, hS.2⟩
  intro Y hY
  have hYins := hS.1 hY
  simp only [Finset.mem_insert] at hYins
  exact hYins.resolve_left (fun h => hXS (h ▸ hY))

/-- A compatible subfamily of Gamma is also compatible in insert X Gamma. -/
theorem compatibleSubfamilies_mono {d : ℕ} {L : ℤ}
    {Gamma : Finset (Polymer d L)} {X : Polymer d L}
    {S : Finset (Polymer d L)}
    (hS : S ∈ compatibleSubfamilies Gamma) :
    S ∈ compatibleSubfamilies (insert X Gamma) := by
  rw [mem_compatibleSubfamilies_iff] at hS ⊢
  exact ⟨hS.1.trans (Finset.subset_insert X Gamma), hS.2⟩

/-!
## Target: insert-split as sum decomposition

The key recurrence for the induction:

∑ S ∈ (compatibleSubfamilies (insert X Gamma)).erase ∅, ∏ Y ∈ S, |K Y|
= ∑ S ∈ (compatibleSubfamilies Gamma).erase ∅, ∏ Y ∈ S, |K Y|
+ |K X| * ∑ S ∈ compatibleSubfamiliesAvoidingX Gamma X, ∏ Y ∈ S, |K Y|

This follows from partitioning compatible subfamilies of insert X Gamma into:
  A) those NOT containing X  (= compatibleSubfamilies Gamma)
  B) those containing X      (= {insert X S | S ∈ compatibleSubfamiliesAvoidingX Gamma X})

Under KP: the second sum is controlled by the KP bound on X,
closing the induction Budget(insert X Gamma) <= Budget(Gamma) * (1 + |K X|).
-/




/-! ## Sum decomposition and induction infrastructure -/

-- partitionWeight uses K X (not |K X|), so the insert lemma is:
theorem partitionWeight_insert {d : ℕ} {L : ℤ}
    (K : Activity d L) (X : Polymer d L) (S : Finset (Polymer d L))
    (hX : X ∉ S) :
    partitionWeight K (insert X S) = K X * partitionWeight K S := by
  simp [partitionWeight, Finset.prod_insert hX]

-- For the recurrence, the budget uses |K X|, so define separately:
noncomputable def absFamilyWeight {d : ℕ} {L : ℤ}
    (K : Activity d L) (S : Finset (Polymer d L)) : ℝ :=
  ∏ X ∈ S, |K X|

theorem absFamilyWeight_insert {d : ℕ} {L : ℤ}
    (K : Activity d L) (X : Polymer d L) (S : Finset (Polymer d L))
    (hX : X ∉ S) :
    absFamilyWeight K (insert X S) = |K X| * absFamilyWeight K S := by
  simp [absFamilyWeight, Finset.prod_insert hX]

theorem absFamilyWeight_eq_partitionWeight_abs {d : ℕ} {L : ℤ}
    (K : Activity d L) (S : Finset (Polymer d L)) :
    absFamilyWeight K S = |partitionWeight K S| := by
  simp [absFamilyWeight, partitionWeight, Finset.abs_prod]

-- noncomputable: sum over Prop-filtered set
noncomputable def InductionBudget {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) : ℝ :=
  ∑ S ∈ (compatibleSubfamilies Gamma).erase ∅, absFamilyWeight K S

theorem inductionBudget_is_majorant {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) :
    CompatibleFamilyMajorant Gamma K (InductionBudget Gamma K a) := by
  unfold CompatibleFamilyMajorant InductionBudget absFamilyWeight
  exact le_refl _

-- explicit proof: same pattern as compatibleFamilyMajorant_empty
theorem inductionBudget_empty {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ) :
    InductionBudget (∅ : Finset (Polymer d L)) K a = 0 := by
  unfold InductionBudget
  have h : compatibleSubfamilies (∅ : Finset (Polymer d L)) = {∅} := by
    ext S
    constructor
    · intro hS
      rw [mem_compatibleSubfamilies_iff] at hS
      simp [Finset.subset_empty.mp hS.1]
    · intro hS
      simp only [Finset.mem_singleton] at hS
      subst hS
      exact empty_mem_compatibleSubfamilies ∅
  rw [h, Finset.erase_singleton, Finset.sum_empty]

theorem compatibleFamilyMajorant_mono {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (B C : ℝ)
    (h : CompatibleFamilyMajorant Gamma K B) (hBC : B ≤ C) :
    CompatibleFamilyMajorant Gamma K C := h.trans hBC

/-!
## Full induction target (next session)

theorem kpOnGamma_implies_compatibleFamilyMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a) :
    CompatibleFamilyMajorant Gamma K (Real.exp (theoreticalBudget Gamma K a) - 1)

Proof: Finset.induction_on Gamma
  Base: empty -> InductionBudget = 0 = exp(0)-1
  Step: insert X Gamma' ->
    Split sum via compatibleSubfamiliesAvoidingX
    Use absFamilyWeight_insert for containing-X subfamilies
    Apply KP bound: |K X| * exp(a * |X|) <= a
    Apply 1 + x <= exp(x) to close exponential form
-/



/-! ## Opening lemmas for the induction (Layer 3B continuation) -/

/-- absFamilyWeight is nonneg (needed for sum monotonicity). -/
theorem absFamilyWeight_nonneg {d : ℕ} {L : ℤ}
    (K : Activity d L) (S : Finset (Polymer d L)) :
    0 ≤ absFamilyWeight K S :=
  Finset.prod_nonneg (fun X _ => abs_nonneg (K X))

/-- theoreticalBudget splits under insert. -/
theorem theoreticalBudget_insert {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (X : Polymer d L)
    (K : Activity d L) (a : ℝ) (hX : X ∉ Gamma) :
    theoreticalBudget (insert X Gamma) K a
      = theoreticalBudget Gamma K a + weightedActivity K a X := by
  simp [theoreticalBudget, Finset.sum_insert hX, add_comm]

/-- 1 + x ≤ exp(x) for all real x. Needed to close the exponential recurrence. -/
theorem one_add_le_exp (x : ℝ) : 1 + x ≤ Real.exp x := by
  simpa [add_comm] using Real.add_one_le_exp x

/-!
## Next session targets

Step 1: inductionBudget_insert_avoiding_le
  -- compatible subfamilies of insert X Gamma avoiding X
  -- ⊆ compatible subfamilies of Gamma
  -- -> sum over subset <= InductionBudget Gamma

Step 2: inductionBudget_insert_containing_le
  -- compatible subfamilies of insert X Gamma containing X
  -- = {insert X S | S ∈ compatibleSubfamiliesAvoidingX Gamma X}
  -- -> sum = |K X| * (sum over avoiding subfamilies)

Step 3: inductionBudget_insert_le (the recurrence)
  InductionBudget (insert X Gamma) ≤ IB(Gamma) + |K X| * IB(Gamma)
                                    = IB(Gamma) * (1 + |K X|)

Step 4: kpOnGamma_implies_compatibleFamilyMajorant
  by Finset.induction_on:
  - base: exp(0) - 1 = 0 = InductionBudget ∅
  - step: use theoreticalBudget_insert + inductionBudget_insert_le
          + one_add_le_exp to close exp form
-/





/-! ## Layer 3B: KP Induction Steps -/

/-- Step 1: avoiding-X subfamilies bounded by InductionBudget Gamma. -/
theorem inductionBudget_insert_avoiding_le {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (X : Polymer d L)
    (K : Activity d L) (a : ℝ) :
    ∑ S ∈ ((compatibleSubfamilies (insert X Gamma)).erase ∅).filter (fun S => X ∉ S),
      absFamilyWeight K S
    ≤ InductionBudget Gamma K a := by
  classical
  unfold InductionBudget
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_erase] at hS
    simp only [Finset.mem_erase]
    exact ⟨hS.1.1, compatibleSubfamilies_insert_avoiding hS.1.2 hS.2⟩
  · intro S _ _; exact absFamilyWeight_nonneg K S

/-- If S is compatible in insert X Gamma and contains X, then S.erase X is in avoidingX. -/
theorem erase_mem_avoidingX {d : ℕ} {L : ℤ}
    {Gamma : Finset (Polymer d L)} {X : Polymer d L} {S : Finset (Polymer d L)}
    (hS : S ∈ compatibleSubfamilies (insert X Gamma)) (hXS : X ∈ S) :
    S.erase X ∈ compatibleSubfamiliesAvoidingX Gamma X := by
  rw [mem_compatibleSubfamiliesAvoidingX_iff]
  rw [mem_compatibleSubfamilies_iff] at hS
  refine ⟨?_, by simp, ?_⟩
  · rw [mem_compatibleSubfamilies_iff]
    refine ⟨?_, fun A hA B hB hAB =>
      hS.2 A (Finset.mem_of_mem_erase hA) B (Finset.mem_of_mem_erase hB) hAB⟩
    intro Y hY
    have hYins := hS.1 (Finset.mem_of_mem_erase hY)
    simp only [Finset.mem_insert] at hYins
    exact hYins.resolve_left (by
      intro hYX; subst hYX
      exact (Finset.mem_erase.mp hY).1 rfl)
  · intro Y hY
    exact hS.2 X hXS Y (Finset.mem_of_mem_erase hY) (by
      intro hYX; exact (Finset.mem_erase.mp hY).1 hYX.symm)

/-- If T is in avoidingX Gamma X, then insert X T is compatible in insert X Gamma. -/
theorem insert_mem_of_avoidingX {d : ℕ} {L : ℤ}
    {Gamma : Finset (Polymer d L)} {X : Polymer d L} {T : Finset (Polymer d L)}
    (hT : T ∈ compatibleSubfamiliesAvoidingX Gamma X) :
    insert X T ∈ compatibleSubfamilies (insert X Gamma) := by
  rw [mem_compatibleSubfamiliesAvoidingX_iff] at hT
  obtain ⟨hTcomp, hTXnot, hTXcompat⟩ := hT
  rw [mem_compatibleSubfamilies_iff] at hTcomp ⊢
  refine ⟨?_, ?_⟩
  · intro Y hY
    simp only [Finset.mem_insert] at hY ⊢
    rcases hY with rfl | hY
    · exact Or.inl rfl
    · exact Or.inr (hTcomp.1 hY)
  · intro A hA B hB hAB
    simp only [Finset.mem_insert] at hA hB
    rcases hA with rfl | hA <;> rcases hB with rfl | hB
    · exact (hAB rfl).elim
    · exact hTXcompat B hB
    · exact Polymer.compatible_symm (hTXcompat A hA)
    · exact hTcomp.2 A hA B hB hAB




/-- The containing-X branch equals the image of insert X over avoidingX families. -/
theorem containingFamilies_eq_image {d : ℕ} {L : ℤ}
    {Gamma : Finset (Polymer d L)} {X : Polymer d L} :
    ((compatibleSubfamilies (insert X Gamma)).erase ∅).filter (fun S => X ∈ S)
      = (compatibleSubfamiliesAvoidingX Gamma X).image (insert X) := by
  classical
  ext S
  constructor
  · intro hS
    simp only [Finset.mem_filter, Finset.mem_erase] at hS
    exact Finset.mem_image.mpr
      ⟨S.erase X, erase_mem_avoidingX hS.1.2 hS.2, Finset.insert_erase hS.2⟩
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
    have hcomp : insert X T ∈ compatibleSubfamilies (insert X Gamma) :=
      insert_mem_of_avoidingX hT
    have hne : insert X T ≠ ∅ := by simp
    simp only [Finset.mem_filter, Finset.mem_erase]
    refine ⟨?_, by simp⟩
    exact ⟨hne, hcomp⟩


/-- Step 2 (igualdad exacta): las familias que contienen X factorizan |K X| exactamente. -/
theorem inductionBudget_insert_containing_eq {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (X : Polymer d L) (K : Activity d L) (a : ℝ) :
    ∑ S ∈ ((compatibleSubfamilies (insert X Gamma)).erase ∅).filter (fun S => X ∈ S),
      absFamilyWeight K S
    =
      |K X| * ∑ S ∈ compatibleSubfamiliesAvoidingX Gamma X, absFamilyWeight K S := by
  classical
  rw [containingFamilies_eq_image]
  rw [Finset.sum_image]
  · calc
      ∑ S ∈ compatibleSubfamiliesAvoidingX Gamma X, absFamilyWeight K (insert X S)
          = ∑ S ∈ compatibleSubfamiliesAvoidingX Gamma X,
              |K X| * absFamilyWeight K S := by
              apply Finset.sum_congr rfl
              intro S hS
              exact absFamilyWeight_insert K X S
                (mem_compatibleSubfamiliesAvoidingX_iff.mp hS).2.1
      _ = |K X| * ∑ S ∈ compatibleSubfamiliesAvoidingX Gamma X,
              absFamilyWeight K S := by
              rw [Finset.mul_sum]
  · -- Inyectividad de (insert X ·) en avoidingX:
    --   insert X A = insert X B  →  A = B   (porque X ∉ A y X ∉ B)
    intro A hA B hB hEq
    have hAX : X ∉ A := (mem_compatibleSubfamiliesAvoidingX_iff.mp hA).2.1
    have hBX : X ∉ B := (mem_compatibleSubfamiliesAvoidingX_iff.mp hB).2.1
    have hErase := congrArg (fun S => S.erase X) hEq
    simpa [Finset.erase_insert, hAX, hBX] using hErase

/-- Step 2 (corolario ≤): derivado trivialmente de la igualdad anterior. -/
theorem inductionBudget_insert_containing_le {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (X : Polymer d L) (K : Activity d L) (a : ℝ) :
    ∑ S ∈ ((compatibleSubfamilies (insert X Gamma)).erase ∅).filter (fun S => X ∈ S),
      absFamilyWeight K S
    ≤ |K X| * ∑ S ∈ compatibleSubfamiliesAvoidingX Gamma X, absFamilyWeight K S :=
  le_of_eq (inductionBudget_insert_containing_eq Gamma X K a)

/-- Step 3: Recurrencia principal — InductionBudget se parte bajo insert. -/
theorem inductionBudget_insert_le {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (X : Polymer d L) (K : Activity d L) (a : ℝ) :
    InductionBudget (insert X Gamma) K a
      ≤ InductionBudget Gamma K a
        + |K X| * ∑ S ∈ compatibleSubfamiliesAvoidingX Gamma X, absFamilyWeight K S := by
  classical
  unfold InductionBudget
  have hsplit :
      ∑ S ∈ (compatibleSubfamilies (insert X Gamma)).erase ∅, absFamilyWeight K S
        =
      ∑ S ∈ ((compatibleSubfamilies (insert X Gamma)).erase ∅).filter (fun S => X ∉ S),
          absFamilyWeight K S
        +
      ∑ S ∈ ((compatibleSubfamilies (insert X Gamma)).erase ∅).filter (fun S => X ∈ S),
          absFamilyWeight K S := by
    simpa [add_comm] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (compatibleSubfamilies (insert X Gamma)).erase ∅)
        (p := fun S => X ∈ S)
        (f := fun S => absFamilyWeight K S)).symm
  rw [hsplit]
  exact add_le_add
    (inductionBudget_insert_avoiding_le Gamma X K a)
    (inductionBudget_insert_containing_le Gamma X K a)


end YangMills.ClayCore
