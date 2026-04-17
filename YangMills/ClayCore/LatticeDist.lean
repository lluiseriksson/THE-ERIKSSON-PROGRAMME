/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Phase 9b: Lattice Euclidean Distance

A self-contained Euclidean distance on integer lattice vectors
`Fin d → ℤ`, used by the Clay–authentic mass-gap structure to
express uniform exponential clustering at separations that are
allowed to tend to infinity.

## Main results

* `latticeDist`                 — definition `√(∑ i, x i²)`.
* `latticeDist_nonneg`          — non-negativity.
* `latticeDist_zero`            — `latticeDist 0 = 0`.
* `latticeDist_eq_zero_iff`     — vanishing iff the vector is zero.
* `latticeDist_unbounded`       — arbitrarily large values exist
                                  whenever `d > 0`.
-/

namespace YangMills

open scoped BigOperators
open Finset

/-- Euclidean distance on the integer lattice `ℤ^d`:
    the square root of the sum of squares, taking values in `ℝ`. -/
noncomputable def latticeDist {d : ℕ} (x : Fin d → ℤ) : ℝ :=
  Real.sqrt (∑ i, ((x i : ℝ)) ^ 2)

/-- Non-negativity of the lattice distance. -/
theorem latticeDist_nonneg {d : ℕ} (x : Fin d → ℤ) : 0 ≤ latticeDist x :=
  Real.sqrt_nonneg _

/-- Lattice distance vanishes at the zero vector. -/
theorem latticeDist_zero (d : ℕ) : latticeDist (0 : Fin d → ℤ) = 0 := by
  unfold latticeDist
  simp

/-- Lattice distance vanishes iff the vector is zero. -/
theorem latticeDist_eq_zero_iff {d : ℕ} (x : Fin d → ℤ) :
    latticeDist x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, latticeDist_zero]⟩
  unfold latticeDist at h
  have hsum_nn :
      (0 : ℝ) ≤ ∑ i, ((x i : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hsum_zero : (∑ i, ((x i : ℝ)) ^ 2) = 0 := by
    have := (Real.sqrt_eq_zero hsum_nn).mp h
    exact this
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      ((x i : ℝ)) ^ 2 = 0 := by
    intro i hi
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hsum_zero i hi
    intros j _
    positivity
  funext i
  have h2 : ((x i : ℝ)) ^ 2 = 0 := hterm i (Finset.mem_univ _)
  have hreal : (x i : ℝ) = 0 := by
    have := sq_eq_zero_iff.mp h2
    exact this
  have : (x i : ℤ) = 0 := by exact_mod_cast hreal
  simpa using this

/-- For positive dimension, the lattice distance is unbounded:
    for every real `M`, there exists an integer lattice vector
    `x` with `M ≤ latticeDist x`. -/
theorem latticeDist_unbounded {d : ℕ} [NeZero d] (M : ℝ) :
    ∃ x : Fin d → ℤ, M ≤ latticeDist x := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M ≤ (n : ℝ) := exists_nat_ge M
  let i₀ : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  refine ⟨fun i => if i = i₀ then (n : ℤ) else 0, ?_⟩
  have hsum :
      (∑ i, ((if i = i₀ then (n : ℤ) else 0 : ℤ) : ℝ) ^ 2)
        = (n : ℝ) ^ 2 := by
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  unfold latticeDist
  rw [hsum]
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.zero_le
  rw [Real.sqrt_sq hn_nn]
  exact hn

end YangMills
