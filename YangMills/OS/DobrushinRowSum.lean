/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.DobrushinMatrix
import YangMills.OS.DobrushinCoefficient

/-!
# D-2b — the Dobrushin matrix of a bonded system, and the window as a theorem

Charter: `docs/DOBRUSHIN-CHARTER.md`.

## Why this module exists

D-1 (`YangMills/OS/DobrushinMatrix.lean`) proves a volume-free resolvent bound
for any nonnegative matrix of range one whose row sums are bounded by `α < 1`.
D-2a (`YangMills/OS/DobrushinCoefficient.lean`) proves that one bond of strength
`J` moves a two-state site's conditional by exactly `tanh |J|` at most, and that
this is the least upper bound.

Nothing so far connects them.  This module does: it assembles the bond
coefficients of D-2a into a matrix, discharges all three hypotheses of D-1 from
that construction, and leaves exactly one thing for the user to supply --- the
row-sum bound, which IS the coupling window.

**The window stops being prose.**  For a site carrying two bonds of strength `β`
and two of strength `γ` --- the anisotropic two-dimensional cell --- the row sum
is computed here and equals `2 tanh|β| + 2 tanh|γ|`.  That expression is
therefore no longer a sentence in a paper; it is the hypothesis of a theorem,
and `dobrushin_resolvent_bound` is what consumes it.

## What is still NOT here

The comparison estimate.  This module says what the Dobrushin matrix of a bonded
system is and what its resolvent obeys; it does not prove that correlations of a
Gibbs measure are controlled by that resolvent.  That is D-3, it is the
bottleneck of the lane, and no statement below hints otherwise.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1  The matrix -/

/-- The Dobrushin matrix of a bonded system: the single-site coefficient
`tanh |J i j|` of D-2a on pairs at distance at most one, zero on the diagonal and
beyond range one. -/
noncomputable def dobMatrix (J : ι → ι → ℝ) (d : ι → ι → ℕ) : Matrix ι ι ℝ :=
  fun i j => if i ≠ j ∧ d i j ≤ 1 then Real.tanh |J i j| else 0

theorem dobMatrix_nonneg (J : ι → ι → ℝ) (d : ι → ι → ℕ) (i j : ι) :
    0 ≤ dobMatrix J d i j := by
  unfold dobMatrix
  split
  · exact tanh_nonneg_of_nonneg (abs_nonneg _)
  · exact le_refl 0

theorem dobMatrix_supp (J : ι → ι → ℝ) (d : ι → ι → ℕ) (i j : ι)
    (h : 1 < d i j) : dobMatrix J d i j = 0 := by
  unfold dobMatrix
  rw [if_neg]
  rintro ⟨-, hle⟩
  exact absurd hle (Nat.not_le.mpr h)

theorem dobMatrix_diag (J : ι → ι → ℝ) (d : ι → ι → ℕ) (i : ι) :
    dobMatrix J d i i = 0 := by
  unfold dobMatrix
  rw [if_neg]
  rintro ⟨hne, -⟩
  exact hne rfl

/-! ## §2  The bridge: D-2a discharges the hypotheses of D-1 -/

/-- **D-2b.**  All three structural hypotheses of D-1 are discharged by the
construction; the only thing left is the row-sum bound, and that is the coupling
window.  The conclusion is free of the cardinality of `ι`. -/
theorem dobrushin_resolvent_bound
    (J : ι → ι → ℝ) (d : ι → ι → ℕ)
    (hself : ∀ i, d i i = 0) (htri : ∀ i j k, d i k ≤ d i j + d j k)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ j, dobMatrix J d i j ≤ α)
    (i j : ι) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((dobMatrix J d) ^ n) i j ≤ α ^ (d i j) / (1 - α) :=
  Matrix.sum_range_pow_apply_le (dobMatrix_nonneg J d) hα0 hα1 hrow hself htri
    (dobMatrix_supp J d) i j N

/-- The series form. -/
theorem dobrushin_resolvent_tsum
    (J : ι → ι → ℝ) (d : ι → ι → ℕ)
    (hself : ∀ i, d i i = 0) (htri : ∀ i j k, d i k ≤ d i j + d j k)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ j, dobMatrix J d i j ≤ α)
    (i j : ι) :
    ∑' n : ℕ, ((dobMatrix J d) ^ n) i j ≤ α ^ (d i j) / (1 - α) :=
  Matrix.tsum_pow_apply_le (dobMatrix_nonneg J d) hα0 hα1 hrow hself htri
    (dobMatrix_supp J d) i j

/-! ## §2b  From local geometry to the row-sum hypothesis, at every site of
every volume

The computation of §3 is about ONE site of ONE small graph.  What
`dobrushin_resolvent_bound` consumes is a bound at EVERY site, and a reader is
entitled to ask how one becomes the other without the size of the system
entering.  This is the bridge, and it is the statement that makes the window a
property of local geometry rather than of a particular volume. -/

/-- Every entry is at most the bond coefficient it is built from; off the
influence support it is zero, which is smaller still. -/
theorem dobMatrix_le_tanh (J : ι → ι → ℝ) (d : ι → ι → ℕ) (i j : ι) :
    dobMatrix J d i j ≤ Real.tanh |J i j| := by
  unfold dobMatrix
  split
  · exact le_refl _
  · exact tanh_nonneg_of_nonneg (abs_nonneg _)

/-- **The row sum is carried by any cover of the influence support.** -/
theorem rowSum_le_sum_cover (J : ι → ι → ℝ) (d : ι → ι → ℕ) (i : ι)
    (S : Finset ι) (hS : ∀ j, dobMatrix J d i j ≠ 0 → j ∈ S) :
    ∑ j, dobMatrix J d i j ≤ ∑ j ∈ S, Real.tanh |J i j| := by
  have hrestrict : ∑ j, dobMatrix J d i j = ∑ j ∈ S, dobMatrix J d i j := by
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro x _ hx
    by_contra hne
    exact hx (hS x hne)
  rw [hrestrict]
  exact Finset.sum_le_sum fun j _ => dobMatrix_le_tanh J d i j

/-- **The window, uniformly over sites and therefore over volumes.**  If at every
site the influence support is contained in a finite set whose bond coefficients
sum to at most `α`, then the row-sum hypothesis of `dobrushin_resolvent_bound`
holds at every site.  Neither the statement nor `α` mentions the cardinality of
`ι`: this is what turns a computation at one site into a hypothesis that a whole
family of finite volumes satisfies simultaneously. -/
theorem rowSum_bound_of_local_cover (J : ι → ι → ℝ) (d : ι → ι → ℕ) {α : ℝ}
    (S : ι → Finset ι)
    (hS : ∀ i j, dobMatrix J d i j ≠ 0 → j ∈ S i)
    (hα : ∀ i, ∑ j ∈ S i, Real.tanh |J i j| ≤ α) :
    ∀ i, ∑ j, dobMatrix J d i j ≤ α :=
  fun i => le_trans (rowSum_le_sum_cover J d i (S i) (hS i)) (hα i)

/-- The chain, assembled from local data alone: local covers whose coefficients
sum below one give the volume-free resolvent bound at every pair of sites. -/
theorem dobrushin_bound_of_local_cover (J : ι → ι → ℝ) (d : ι → ι → ℕ)
    (hself : ∀ i, d i i = 0) (htri : ∀ i j k, d i k ≤ d i j + d j k)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (S : ι → Finset ι)
    (hS : ∀ i j, dobMatrix J d i j ≠ 0 → j ∈ S i)
    (hα : ∀ i, ∑ j ∈ S i, Real.tanh |J i j| ≤ α)
    (i j : ι) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((dobMatrix J d) ^ n) i j ≤ α ^ (d i j) / (1 - α) :=
  dobrushin_resolvent_bound J d hself htri hα0 hα1
    (rowSum_bound_of_local_cover J d S hS hα) i j N

/-! ## §3  The window, computed

A site with four neighbours, two carrying `β` and two carrying `γ`.  The graph is
the star on five points, whose distance is the one below; the point of the
computation is that the row sum at the centre is exactly the expression the lane
carries as its window. -/

/-- Graph distance on the star with centre `0`. -/
def starDist (i j : Fin 5) : ℕ :=
  if i = j then 0 else if i = 0 ∨ j = 0 then 1 else 2

-- `decide` needs a closed proposition, so the variables are reverted first.
theorem starDist_self (i : Fin 5) : starDist i i = 0 := by
  revert i; decide

theorem starDist_triangle (i j k : Fin 5) :
    starDist i k ≤ starDist i j + starDist j k := by
  revert i j k; decide

/-- Two bonds of strength `β`, two of strength `γ`, from the centre. -/
noncomputable def starBond (β γ : ℝ) : Fin 5 → Fin 5 → ℝ :=
  fun i j => if i = 1 ∨ j = 1 ∨ i = 2 ∨ j = 2 then β else γ

/-- **The window, as a computation rather than a sentence.**  At the centre of a
site carrying two bonds of strength `β` and two of strength `γ`, the Dobrushin
row sum is exactly `2 tanh|β| + 2 tanh|γ|`. -/
theorem starDist_rowSum (β γ : ℝ) :
    ∑ j : Fin 5, dobMatrix (starBond β γ) starDist 0 j
      = 2 * Real.tanh |β| + 2 * Real.tanh |γ| := by
  -- the five entries, each with a CLOSED decidable side condition
  have b1 : starBond β γ 0 1 = β := by unfold starBond; rw [if_pos (by decide)]
  have b2 : starBond β γ 0 2 = β := by unfold starBond; rw [if_pos (by decide)]
  have b3 : starBond β γ 0 3 = γ := by unfold starBond; rw [if_neg (by decide)]
  have b4 : starBond β γ 0 4 = γ := by unfold starBond; rw [if_neg (by decide)]
  have e0 : dobMatrix (starBond β γ) starDist 0 0 = 0 := dobMatrix_diag _ _ 0
  have e1 : dobMatrix (starBond β γ) starDist 0 1 = Real.tanh |β| := by
    unfold dobMatrix; rw [if_pos (by decide), b1]
  have e2 : dobMatrix (starBond β γ) starDist 0 2 = Real.tanh |β| := by
    unfold dobMatrix; rw [if_pos (by decide), b2]
  have e3 : dobMatrix (starBond β γ) starDist 0 3 = Real.tanh |γ| := by
    unfold dobMatrix; rw [if_pos (by decide), b3]
  have e4 : dobMatrix (starBond β γ) starDist 0 4 = Real.tanh |γ| := by
    unfold dobMatrix; rw [if_pos (by decide), b4]
  rw [Fin.sum_univ_five, e0, e1, e2, e3, e4]
  ring

end Dobrushin

end YangMills.OS
