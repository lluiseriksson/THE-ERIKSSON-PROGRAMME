import Mathlib
import YangMills.ClayCore.BalabanRG.BlockSpin

namespace YangMills.ClayCore

/-!
# PolymerCombinatorics — Layer 1: Polymer expansion

Abstract polymer combinatorics for Balaban RG.
No gauge theory needed: purely combinatorial.
Reference: E26 P89 (2602.0134); Kotecký-Preiss (1986).

Design: NO variable block for L — all methods use explicit {d : ℕ} {L : ℤ}
to prevent L from becoming an explicit method argument via the variable mechanism.
-/

open scoped BigOperators
open Classical

structure Polymer (d : ℕ) (L : ℤ) where
  sites : Finset (LatticeSite d)
  nonEmpty : sites.Nonempty

def Polymer.size {d : ℕ} {L : ℤ} (X : Polymer d L) : ℕ :=
  X.sites.card

def Polymer.Compatible {d : ℕ} {L : ℤ} (X Y : Polymer d L) : Prop :=
  Disjoint X.sites Y.sites

theorem Polymer.compatible_symm {d : ℕ} {L : ℤ} {X Y : Polymer d L}
    (h : Polymer.Compatible X Y) : Polymer.Compatible Y X :=
  h.symm

def MutuallyCompatible {d : ℕ} {L : ℤ} (polys : Finset (Polymer d L)) : Prop :=
  ∀ X ∈ polys, ∀ Y ∈ polys, X ≠ Y → Polymer.Compatible X Y

def Activity (d : ℕ) (L : ℤ) := Polymer d L → ℝ

def Polymer.Touches {d : ℕ} {L : ℤ} (X : Polymer d L) (x : LatticeSite d) : Prop :=
  x ∈ X.sites

/-- Kotecký-Preiss criterion. -/
def KoteckyPreiss {d : ℕ} {L : ℤ} (K : Activity d L) (a : ℝ) : Prop :=
  ∀ (x : LatticeSite d),
    ∀ (polys : Finset (Polymer d L)),
    (∀ X ∈ polys, Polymer.Touches X x) →
    (∑ X ∈ polys, |K X| * Real.exp (a * (X.size : ℝ))) ≤ a

def singletonPolymer {d : ℕ} {L : ℤ} (x : LatticeSite d) : Polymer d L :=
  ⟨{x}, Finset.singleton_nonempty x⟩

theorem singletonPolymer_size {d : ℕ} {L : ℤ} (x : LatticeSite d) :
    (singletonPolymer (L := L) x).size = 1 := by
  simp [Polymer.size, singletonPolymer]

theorem singletonPolymer_touches {d : ℕ} {L : ℤ} (x : LatticeSite d) :
    Polymer.Touches (singletonPolymer (L := L) x) x := by
  simp [Polymer.Touches, singletonPolymer]

/-- KP gives a pointwise activity bound. -/
theorem kp_activity_bound {d : ℕ} {L : ℤ} (K : Activity d L) (a : ℝ)
    (hKP : KoteckyPreiss K a) (X : Polymer d L) :
    |K X| ≤ a * Real.exp (-a * (X.size : ℝ)) := by
  obtain ⟨x, hx⟩ := X.nonEmpty
  -- Apply KP to singleton {X} touching x
  have hsingle := hKP x ({X} : Finset (Polymer d L)) (by
    intro Y hY
    simp only [Finset.mem_singleton] at hY
    subst hY
    exact hx)
  simp only [Finset.sum_singleton] at hsingle
  -- hsingle : |K X| * exp(a * |X|) ≤ a
  -- Divide by exp(a * |X|) > 0
  have hexp : 0 < Real.exp (a * (X.size : ℝ)) := Real.exp_pos _
  have hbound : |K X| ≤ a / Real.exp (a * (X.size : ℝ)) :=
    (le_div_iff₀ hexp).mpr (by linarith)
  calc |K X|
      ≤ a / Real.exp (a * (X.size : ℝ)) := hbound
    _ = a * (Real.exp (a * (X.size : ℝ)))⁻¹ := by
          rw [div_eq_mul_inv]
    _ = a * Real.exp (-(a * (X.size : ℝ))) := by
          rw [← Real.exp_neg]
    _ = a * Real.exp (-a * (X.size : ℝ)) := by
          congr 1; ring

end YangMills.ClayCore
