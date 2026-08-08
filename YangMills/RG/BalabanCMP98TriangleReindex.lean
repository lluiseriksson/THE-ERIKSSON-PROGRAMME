/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98GAdMonomial

/-!
# Finite triangular reindexing for the CMP98 exponential identity

The Cauchy layer of `exp(-L_Y)` times the ordered derivative is indexed by
`r + b ≤ N`.  This file proves that the two finite summation orders agree.
The result is purely finite and therefore introduces no convergence or
Fubini assumption.
-/

namespace YangMills.RG

open scoped BigOperators

/-- Interchange the order of summation over the finite natural-number
triangle `r + b ≤ N`. -/
theorem sum_range_triangle_comm {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) (N : ℕ) :
    (∑ r ∈ Finset.range (N + 1),
        ∑ b ∈ Finset.range (N - r + 1), f r b) =
      ∑ b ∈ Finset.range (N + 1),
        ∑ r ∈ Finset.range (N - b + 1), f r b := by
  classical
  let triangle : ℕ → ℕ → M := fun r b =>
    if r + b ≤ N then f r b else 0
  have hrow (r : ℕ) (hr : r ∈ Finset.range (N + 1)) :
      (∑ b ∈ Finset.range (N - r + 1), f r b) =
        ∑ b ∈ Finset.range (N + 1), triangle r b := by
    have hrlt := Finset.mem_range.mp hr
    have hfin : Finset.range (N - r + 1) =
        (Finset.range (N + 1)).filter (fun b => r + b ≤ N) := by
      ext b
      simp only [Finset.mem_range, Finset.mem_filter]
      constructor
      · intro hb
        constructor <;> omega
      · rintro ⟨_, hb⟩
        omega
    rw [hfin, Finset.sum_filter]
  have hcol (b : ℕ) (hb : b ∈ Finset.range (N + 1)) :
      (∑ r ∈ Finset.range (N + 1), triangle r b) =
        ∑ r ∈ Finset.range (N - b + 1), f r b := by
    have hblt := Finset.mem_range.mp hb
    have hfin : Finset.range (N - b + 1) =
        (Finset.range (N + 1)).filter (fun r => r + b ≤ N) := by
      ext r
      simp only [Finset.mem_range, Finset.mem_filter]
      constructor
      · intro hr
        constructor <;> omega
      · rintro ⟨_, hr⟩
        omega
    rw [hfin, Finset.sum_filter]
  calc
    (∑ r ∈ Finset.range (N + 1),
        ∑ b ∈ Finset.range (N - r + 1), f r b) =
        ∑ r ∈ Finset.range (N + 1),
          ∑ b ∈ Finset.range (N + 1), triangle r b := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hrow r hr
    _ = ∑ b ∈ Finset.range (N + 1),
          ∑ r ∈ Finset.range (N + 1), triangle r b := by
      rw [Finset.sum_comm]
    _ = ∑ b ∈ Finset.range (N + 1),
          ∑ r ∈ Finset.range (N - b + 1), f r b := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hcol b hb

end YangMills.RG
