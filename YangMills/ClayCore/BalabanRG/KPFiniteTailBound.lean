import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerPartitionFunction

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPFiniteTailBound -- Layer 3A (minimal, green)

Finite KP interface. kpOnGamma_mono deferred to Layer 3B.
-/

-- noncomputable: Real.exp is noncomputable
noncomputable def weightedActivity {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ) (X : Polymer d L) : ℝ :=
  |K X| * Real.exp (a * (X.size : ℝ))

theorem weightedActivity_nonneg {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ) (X : Polymer d L) :
    0 ≤ weightedActivity K a X :=
  mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

noncomputable def touchingPolymers {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (x : LatticeSite d) :
    Finset (Polymer d L) :=
  Gamma.filter (fun X => Polymer.Touches X x)

theorem mem_touchingPolymers_iff {d : ℕ} {L : ℤ}
    {Gamma : Finset (Polymer d L)} {x : LatticeSite d} {X : Polymer d L} :
    X ∈ touchingPolymers Gamma x ↔ X ∈ Gamma ∧ Polymer.Touches X x := by
  simp [touchingPolymers, Finset.mem_filter]

def KPOnGamma {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) : Prop :=
  ∀ x : LatticeSite d,
    ∑ X ∈ touchingPolymers Gamma x, weightedActivity K a X ≤ a

theorem kpOnGamma_of_kp {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ) (hKP : KoteckyPreiss K a)
    (Gamma : Finset (Polymer d L)) :
    KPOnGamma Gamma K a := by
  intro x
  apply le_trans _ (hKP x (touchingPolymers Gamma x) (by
    intro X hX; exact (mem_touchingPolymers_iff.mp hX).2))
  simp [weightedActivity, touchingPolymers]

theorem kpOnGamma_empty {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ) (ha : 0 ≤ a) :
    KPOnGamma (∅ : Finset (Polymer d L)) K a := by
  intro x
  simp [KPOnGamma, touchingPolymers]
  linarith

-- kpOnGamma_mono deferred: needs correct sum_le_sum_of_subset variant

theorem kpOnGamma_singleton_touching_bound {d : ℕ} {L : ℤ}
    {Gamma : Finset (Polymer d L)} {K : Activity d L} {a : ℝ}
    (hKP : KPOnGamma Gamma K a) {x : LatticeSite d} {X : Polymer d L}
    (hsingle : touchingPolymers Gamma x = ({X} : Finset (Polymer d L))) :
    weightedActivity K a X ≤ a := by
  have h := hKP x; rw [hsingle, Finset.sum_singleton] at h; exact h

noncomputable def theoreticalBudget {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) : ℝ :=
  ∑ X ∈ Gamma, weightedActivity K a X

theorem theoreticalBudget_nonneg {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) :
    0 ≤ theoreticalBudget Gamma K a :=
  Finset.sum_nonneg (fun X _ => weightedActivity_nonneg K a X)

theorem theoreticalBudget_empty {d : ℕ} {L : ℤ} (K : Activity d L) (a : ℝ) :
    theoreticalBudget (∅ : Finset (Polymer d L)) K a = 0 := by
  simp [theoreticalBudget]

/-!
## Layer 3B (next session)

Goal: KPOnGamma Gamma K a -> SmallActivityBudget Gamma K (exp(theoreticalBudget) - 1)
Strategy: induction on Gamma.card (KP induction)
-/

end YangMills.ClayCore
