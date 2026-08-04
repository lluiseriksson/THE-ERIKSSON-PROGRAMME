/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.KP.RootedCatalanExact

/-!
# Catalan majorant partial sums

This module starts the algebra-only phase-2 Catalan majorant lane.  The sharp
cluster-expansion improvement by exact tree counting is due to
R. Fernandez and A. Procacci, *Cluster Expansion for Abstract Polymer Models.
New Bounds from an Old Approach*, Comm. Math. Phys. 274 (2007), 123-140.

The contribution here is narrower: formalize the finite Catalan majorant
partial sums inside the Yang-Mills KP namespace and connect them to the
machine-checked exact Catalan identity
`rootedChildFactorialCatalanIdentity_holds`.  This file does not recable any
Appendix-F consumer, prove a heat-kernel statement, or claim any raw activity,
`hRpoly`, mass-gap, or Clay result.
-/

open Nat Finset
open scoped BigOperators

namespace YangMills.KP

/-- Finite Catalan majorant partial sum
`sum_{n < N} C_n M^{2n+1} epsilon^{n+1}`.

Fernandez--Procacci (CMP 274, 2007, 123-140) is the source of the sharp
tree-counting/KP improvement; this definition is the repo-local finite algebraic
object fed by `rootedChildFactorialCatalanIdentity_holds`. -/
noncomputable def catalanMajorantPartial (M ε : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (catalan n : ℝ) * M ^ (2 * n + 1) * ε ^ (n + 1)

/-- The Catalan majorant has no zero-step contribution. -/
theorem catalanMajorantPartial_zero (M ε : ℝ) :
    catalanMajorantPartial M ε 0 = 0 := by
  simp [catalanMajorantPartial]

/-- Exposing the last term of a finite Catalan majorant truncation. -/
theorem catalanMajorantPartial_succ (M ε : ℝ) (N : ℕ) :
    catalanMajorantPartial M ε (N + 1) =
      catalanMajorantPartial M ε N +
        (catalan N : ℝ) * M ^ (2 * N + 1) * ε ^ (N + 1) := by
  simp [catalanMajorantPartial, Finset.sum_range_succ]

/-- Nonnegativity of the finite Catalan majorant partial sums. -/
theorem catalanMajorantPartial_nonneg {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (N : ℕ) :
    0 ≤ catalanMajorantPartial M ε N := by
  unfold catalanMajorantPartial
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg
      (mul_nonneg (Nat.cast_nonneg (catalan n)) (pow_nonneg hM (2 * n + 1)))
      (pow_nonneg hε (n + 1))

/--
The next Catalan majorant increment is governed by the finite antidiagonal
Catalan convolution.  This is the scalar Cauchy-product substrate for later
closed-form majorants; it is still a finite polynomial identity, not an analytic
convergence or kernel statement.
-/
theorem catalanMajorantPartial_succ_succ_eq_catalanConvolution (M ε : ℝ) (N : ℕ) :
    catalanMajorantPartial M ε (N + 2) =
      catalanMajorantPartial M ε (N + 1) +
        (∑ ij ∈ Finset.antidiagonal N,
            ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ)) *
          M ^ (2 * N + 3) * ε ^ (N + 2) := by
  rw [catalanMajorantPartial_succ]
  congr 1
  rw [catalan_succ']
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul]
  ring_nf

/--
Finite convolution form of the Catalan majorant recursion, truncated before
degree `N`.  The `M * ε` term is the `C_0` contribution; the remaining terms are
the Catalan antidiagonal recursion terms.
-/
noncomputable def catalanMajorantConvolutionPartial (M ε : ℝ) (N : ℕ) : ℝ :=
  M * ε +
    ∑ k ∈ Finset.range N,
      (∑ ij ∈ Finset.antidiagonal k,
          ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ)) *
        M ^ (2 * k + 3) * ε ^ (k + 2)

/-- The zero-length convolution truncation recovers the `C_0` monomial. -/
theorem catalanMajorantConvolutionPartial_zero (M ε : ℝ) :
    catalanMajorantConvolutionPartial M ε 0 = M * ε := by
  simp [catalanMajorantConvolutionPartial]

/-- Expose the last antidiagonal term in the finite convolution truncation. -/
theorem catalanMajorantConvolutionPartial_succ (M ε : ℝ) (N : ℕ) :
    catalanMajorantConvolutionPartial M ε (N + 1) =
      catalanMajorantConvolutionPartial M ε N +
        (∑ ij ∈ Finset.antidiagonal N,
            ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ)) *
          M ^ (2 * N + 3) * ε ^ (N + 2) := by
  simp [catalanMajorantConvolutionPartial, Finset.sum_range_succ, add_assoc]

/--
The finite Catalan majorant partial sums are exactly the finite convolution
recursion partial sums.  This packages the scalar Cauchy-product recurrence
before any closed-form square-root estimate is attempted.
-/
theorem catalanMajorantPartial_eq_convolutionPartial (M ε : ℝ) (N : ℕ) :
    catalanMajorantPartial M ε (N + 1) =
      catalanMajorantConvolutionPartial M ε N := by
  induction N with
  | zero =>
      rw [catalanMajorantPartial_succ, catalanMajorantPartial_zero,
        catalanMajorantConvolutionPartial_zero]
      simp
  | succ N ih =>
      rw [catalanMajorantPartial_succ_succ_eq_catalanConvolution,
        catalanMajorantConvolutionPartial_succ, ih]

/-- Nonnegativity of the finite Catalan convolution partial sums. -/
theorem catalanMajorantConvolutionPartial_nonneg {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (N : ℕ) :
    0 ≤ catalanMajorantConvolutionPartial M ε N := by
  rw [← catalanMajorantPartial_eq_convolutionPartial]
  exact catalanMajorantPartial_nonneg hM hε (N + 1)

/-- Finite Catalan convolution partial sums are monotone in the truncation length. -/
theorem catalanMajorantConvolutionPartial_le_succ {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (N : ℕ) :
    catalanMajorantConvolutionPartial M ε N ≤
      catalanMajorantConvolutionPartial M ε (N + 1) := by
  rw [catalanMajorantConvolutionPartial_succ]
  exact le_add_of_nonneg_right <|
    mul_nonneg
      (mul_nonneg
        (Finset.sum_nonneg fun ij _ => Nat.cast_nonneg (catalan ij.1 * catalan ij.2))
        (pow_nonneg hM (2 * N + 3)))
      (pow_nonneg hε (N + 2))

/--
Finite Cauchy-product expansion of the square of the Catalan majorant partial
sum.  This keeps the quadratic-majorant comparison at the explicit finite-sum
level before any antidiagonal embedding or closed-form bound is attempted.
-/
theorem catalanMajorantPartial_sq_eq_double_sum (M ε : ℝ) (N : ℕ) :
    (catalanMajorantPartial M ε N) ^ 2 =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ((catalan i : ℝ) * M ^ (2 * i + 1) * ε ^ (i + 1)) *
          ((catalan j : ℝ) * M ^ (2 * j + 1) * ε ^ (j + 1)) := by
  rw [pow_two, catalanMajorantPartial, Finset.sum_mul]
  simp only [Finset.mul_sum]

/--
The quadratic Catalan majorant term as a normalized finite double sum.  This is
the monomial form that will compare termwise with the truncated Catalan
convolution antidiagonals.
-/
theorem mul_catalanMajorantPartial_sq_eq_double_sum (M ε : ℝ) (N : ℕ) :
    M * (catalanMajorantPartial M ε N) ^ 2 =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ((catalan i * catalan j : ℕ) : ℝ) *
          M ^ (2 * (i + j) + 3) * ε ^ (i + j + 2) := by
  rw [catalanMajorantPartial_sq_eq_double_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hMexp : ((2 * i + 1) + (2 * j + 1)) + 1 = 2 * (i + j) + 3 := by omega
  have hεexp : (i + 1) + (j + 1) = i + j + 2 := by omega
  calc
    M * (((catalan i : ℝ) * M ^ (2 * i + 1) * ε ^ (i + 1)) *
        ((catalan j : ℝ) * M ^ (2 * j + 1) * ε ^ (j + 1))) =
        ((catalan i : ℝ) * (catalan j : ℝ)) *
          ((M ^ (2 * i + 1) * M ^ (2 * j + 1)) * M) *
          (ε ^ (i + 1) * ε ^ (j + 1)) := by ring
    _ = ((catalan i * catalan j : ℕ) : ℝ) *
          M ^ (2 * (i + j) + 3) * ε ^ (i + j + 2) := by
        rw [← pow_add, ← pow_succ, hMexp, ← pow_add, hεexp]
        norm_num [Nat.cast_mul]

/--
Every Catalan antidiagonal strictly below the truncation cutoff lands inside
the full square-index rectangle.  This is the finite support inclusion needed
to compare the convolution partial sum with the Cauchy-product square.
-/
theorem antidiagonal_subset_range_product {N k : ℕ} (hk : k < N) :
    Finset.antidiagonal k ⊆ (Finset.range N).product (Finset.range N) := by
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  exact Finset.mem_product.mpr
    ⟨by rw [Finset.mem_range]; omega, by rw [Finset.mem_range]; omega⟩

/-- The finite support of all Catalan convolution antidiagonals below `N`. -/
def catalanConvolutionSupport (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range N).product (Finset.range N)).filter fun ij => ij.1 + ij.2 < N

/-- Membership in the finite Catalan convolution support. -/
theorem mem_catalanConvolutionSupport {N : ℕ} {ij : ℕ × ℕ} :
    ij ∈ catalanConvolutionSupport N ↔ ij.1 < N ∧ ij.2 < N ∧ ij.1 + ij.2 < N := by
  simp [catalanConvolutionSupport, Finset.mem_product, and_assoc]

/-- Each antidiagonal below the cutoff is contained in the finite convolution support. -/
theorem antidiagonal_subset_catalanConvolutionSupport {N k : ℕ} (hk : k < N) :
    Finset.antidiagonal k ⊆ catalanConvolutionSupport N := by
  intro ij hij
  rw [mem_catalanConvolutionSupport]
  rw [Finset.mem_antidiagonal] at hij
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Distinct Catalan antidiagonals have disjoint finite supports. -/
theorem disjoint_antidiagonal_of_ne {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (Finset.antidiagonal k) (Finset.antidiagonal l) := by
  rw [Finset.disjoint_left]
  intro ij hik hil
  rw [Finset.mem_antidiagonal] at hik hil
  exact hkl (hik.symm.trans hil)

/--
The filtered convolution support is exactly the finite union of Catalan
antidiagonals below the cutoff.
-/
theorem catalanConvolutionSupport_eq_biUnion_antidiagonal (N : ℕ) :
    catalanConvolutionSupport N =
      (Finset.range N).biUnion fun k => Finset.antidiagonal k := by
  ext ij
  rw [mem_catalanConvolutionSupport]
  constructor
  · intro hij
    rw [Finset.mem_biUnion]
    exact ⟨ij.1 + ij.2, by rw [Finset.mem_range]; exact hij.2.2,
      by rw [Finset.mem_antidiagonal]⟩
  · intro hij
    rw [Finset.mem_biUnion] at hij
    rcases hij with ⟨k, hkN, hijk⟩
    rw [Finset.mem_range] at hkN
    rw [Finset.mem_antidiagonal] at hijk
    constructor
    · omega
    constructor
    · omega
    · omega

/--
Flatten a sum over the filtered Catalan convolution support into the nested
sum over its disjoint antidiagonal decomposition.
-/
theorem sum_catalanConvolutionSupport_eq_sum_antidiagonal {α : Type*} [AddCommMonoid α]
    (N : ℕ) (f : ℕ × ℕ → α) :
    (∑ ij ∈ catalanConvolutionSupport N, f ij) =
      ∑ k ∈ Finset.range N, ∑ ij ∈ Finset.antidiagonal k, f ij := by
  rw [catalanConvolutionSupport_eq_biUnion_antidiagonal]
  rw [Finset.sum_biUnion]
  intro k _ l _ hkl
  exact disjoint_antidiagonal_of_ne hkl

/--
The `N`th Catalan convolution increment is bounded by the quadratic
Cauchy-product square at truncation `N+1`.
-/
theorem catalanConvolution_increment_le_mul_sq {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (N : ℕ) :
    (∑ ij ∈ Finset.antidiagonal N,
        ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ)) *
      M ^ (2 * N + 3) * ε ^ (N + 2) ≤
        M * (catalanMajorantPartial M ε (N + 1)) ^ 2 := by
  rw [mul_catalanMajorantPartial_sq_eq_double_sum]
  have hrect :
      (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ((catalan i * catalan j : ℕ) : ℝ) *
          M ^ (2 * (i + j) + 3) * ε ^ (i + j + 2)) =
      ∑ ij ∈ (Finset.range (N + 1)).product (Finset.range (N + 1)),
        ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ) *
          M ^ (2 * (ij.1 + ij.2) + 3) * ε ^ (ij.1 + ij.2 + 2) := by
    exact (Finset.sum_product (Finset.range (N + 1)) (Finset.range (N + 1))
      (fun ij : ℕ × ℕ =>
        ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ) *
          M ^ (2 * (ij.1 + ij.2) + 3) * ε ^ (ij.1 + ij.2 + 2))).symm
  rw [hrect]
  have hlhs :
      (∑ ij ∈ Finset.antidiagonal N,
          ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ)) *
        M ^ (2 * N + 3) * ε ^ (N + 2) =
      ∑ ij ∈ Finset.antidiagonal N,
        ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ) *
          M ^ (2 * (ij.1 + ij.2) + 3) * ε ^ (ij.1 + ij.2 + 2) := by
    calc
      (∑ ij ∈ Finset.antidiagonal N,
          ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ)) *
        M ^ (2 * N + 3) * ε ^ (N + 2) =
          ∑ ij ∈ Finset.antidiagonal N,
            (((catalan ij.1 * catalan ij.2 : ℕ) : ℝ) * M ^ (2 * N + 3)) *
              ε ^ (N + 2) := by
            rw [Finset.sum_mul]
            rw [Finset.sum_mul]
      _ = ∑ ij ∈ Finset.antidiagonal N,
          ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ) *
            M ^ (2 * (ij.1 + ij.2) + 3) * ε ^ (ij.1 + ij.2 + 2) := by
            refine Finset.sum_congr rfl ?_
            intro ij hij
            rw [Finset.mem_antidiagonal] at hij
            have hMexp : 2 * N + 3 = 2 * (ij.1 + ij.2) + 3 := by omega
            have hεexp : N + 2 = ij.1 + ij.2 + 2 := by omega
            rw [← hMexp, ← hεexp]
  rw [hlhs]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (antidiagonal_subset_range_product (Nat.lt_succ_self N)) ?_
  intro ij hij hnot
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg (catalan ij.1 * catalan ij.2))
      (pow_nonneg hM (2 * (ij.1 + ij.2) + 3)))
    (pow_nonneg hε (ij.1 + ij.2 + 2))

/--
The truncated Catalan convolution tail is bounded by the quadratic
Cauchy-product square at the same cutoff.
-/
theorem catalanConvolutionPartial_tail_le_mul_sq {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (∑ ij ∈ Finset.antidiagonal k,
          ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ)) *
        M ^ (2 * k + 3) * ε ^ (k + 2)) ≤
      M * (catalanMajorantPartial M ε N) ^ 2 := by
  rw [mul_catalanMajorantPartial_sq_eq_double_sum]
  have hrect :
      (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ((catalan i * catalan j : ℕ) : ℝ) *
          M ^ (2 * (i + j) + 3) * ε ^ (i + j + 2)) =
      ∑ ij ∈ (Finset.range N).product (Finset.range N),
        ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ) *
          M ^ (2 * (ij.1 + ij.2) + 3) * ε ^ (ij.1 + ij.2 + 2) := by
    exact (Finset.sum_product (Finset.range N) (Finset.range N)
      (fun ij : ℕ × ℕ =>
        ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ) *
          M ^ (2 * (ij.1 + ij.2) + 3) * ε ^ (ij.1 + ij.2 + 2))).symm
  rw [hrect]
  have htail :
      (∑ k ∈ Finset.range N,
        (∑ ij ∈ Finset.antidiagonal k,
            ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ)) *
          M ^ (2 * k + 3) * ε ^ (k + 2)) =
      ∑ ij ∈ catalanConvolutionSupport N,
        ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ) *
          M ^ (2 * (ij.1 + ij.2) + 3) * ε ^ (ij.1 + ij.2 + 2) := by
    rw [sum_catalanConvolutionSupport_eq_sum_antidiagonal]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_range] at hk
    calc
      (∑ ij ∈ Finset.antidiagonal k,
          ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ)) *
        M ^ (2 * k + 3) * ε ^ (k + 2) =
          ∑ ij ∈ Finset.antidiagonal k,
            (((catalan ij.1 * catalan ij.2 : ℕ) : ℝ) * M ^ (2 * k + 3)) *
              ε ^ (k + 2) := by
            rw [Finset.sum_mul]
            rw [Finset.sum_mul]
      _ = ∑ ij ∈ Finset.antidiagonal k,
          ((catalan ij.1 * catalan ij.2 : ℕ) : ℝ) *
            M ^ (2 * (ij.1 + ij.2) + 3) * ε ^ (ij.1 + ij.2 + 2) := by
            refine Finset.sum_congr rfl ?_
            intro ij hij
            rw [Finset.mem_antidiagonal] at hij
            have hMexp : 2 * k + 3 = 2 * (ij.1 + ij.2) + 3 := by omega
            have hεexp : k + 2 = ij.1 + ij.2 + 2 := by omega
            rw [← hMexp, ← hεexp]
  rw [htail]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
  · intro ij hij
    rw [mem_catalanConvolutionSupport] at hij
    exact Finset.mem_product.mpr
      ⟨by rw [Finset.mem_range]; exact hij.1,
        by rw [Finset.mem_range]; exact hij.2.1⟩
  · intro ij hij hnot
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg (catalan ij.1 * catalan ij.2))
        (pow_nonneg hM (2 * (ij.1 + ij.2) + 3)))
      (pow_nonneg hε (ij.1 + ij.2 + 2))

/--
Finite quadratic recursion inequality for the Catalan majorant truncations.
This is still a finite algebraic estimate, preceding the closed square-root
majorant.
-/
theorem catalanMajorantPartial_succ_succ_le_quadratic {M ε : ℝ} (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (N : ℕ) :
    catalanMajorantPartial M ε (N + 2) ≤
      catalanMajorantPartial M ε (N + 1) +
        M * (catalanMajorantPartial M ε (N + 1)) ^ 2 := by
  rw [catalanMajorantPartial_succ_succ_eq_catalanConvolution]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left (catalanConvolution_increment_le_mul_sq hM hε N)
      (catalanMajorantPartial M ε (N + 1))

/--
Reset-form finite quadratic recursion for the Catalan majorant truncations.
This is the finite barrier form used before introducing the closed square-root
majorant.
-/
theorem catalanMajorantPartial_succ_le_base_add_quadratic {M ε : ℝ} (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (N : ℕ) :
    catalanMajorantPartial M ε (N + 1) ≤
      M * ε + M * (catalanMajorantPartial M ε N) ^ 2 := by
  rw [catalanMajorantPartial_eq_convolutionPartial, catalanMajorantConvolutionPartial]
  simpa [add_comm] using
    add_le_add_left (catalanConvolutionPartial_tail_le_mul_sq hM hε N) (M * ε)

/--
The scaled closed Catalan majorant.  This avoids division by `M`: the intended
unscaled closed form is recovered by dividing by `M` only when that is
appropriate.
-/
noncomputable def catalanScaledClosedMajorant (M ε : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - 4 * M ^ 2 * ε)) / 2

/-- The scaled closed majorant is the small fixed point of `z ↦ M^2 ε + z^2`. -/
theorem catalanScaledClosedMajorant_fixed {M ε : ℝ} (hrad : 0 ≤ 1 - 4 * M ^ 2 * ε) :
    catalanScaledClosedMajorant M ε =
      M ^ 2 * ε + (catalanScaledClosedMajorant M ε) ^ 2 := by
  unfold catalanScaledClosedMajorant
  have hs : (Real.sqrt (1 - 4 * M ^ 2 * ε)) ^ 2 = 1 - 4 * M ^ 2 * ε :=
    Real.sq_sqrt hrad
  nlinarith [hs]

/-- Nonnegativity of the scaled closed Catalan majorant for nonnegative `ε`. -/
theorem catalanScaledClosedMajorant_nonneg {M ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ catalanScaledClosedMajorant M ε := by
  unfold catalanScaledClosedMajorant
  have hprod_nonneg : 0 ≤ 4 * M ^ 2 * ε := by nlinarith [sq_nonneg M]
  have hsqrt_le_one : Real.sqrt (1 - 4 * M ^ 2 * ε) ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith
  nlinarith

/--
The fixed-point barrier for the scaled closed Catalan majorant: any
nonnegative `x` below the closed majorant is sent below it by
`x ↦ M^2 ε + x^2`.
-/
theorem catalanScaledClosedMajorant_barrier {M ε x : ℝ} (hx : 0 ≤ x)
    (hxle : x ≤ catalanScaledClosedMajorant M ε)
    (hrad : 0 ≤ 1 - 4 * M ^ 2 * ε) :
    M ^ 2 * ε + x ^ 2 ≤ catalanScaledClosedMajorant M ε := by
  have hfix := catalanScaledClosedMajorant_fixed (M := M) (ε := ε) hrad
  have hsq : x ^ 2 ≤ (catalanScaledClosedMajorant M ε) ^ 2 := by
    nlinarith [sq_nonneg (catalanScaledClosedMajorant M ε - x)]
  nlinarith

/--
Closed square-root bound for the finite Catalan majorant, in scaled form:
`M * partial_N` is bounded by the small root of `z = M^2 ε + z^2`.
-/
theorem mul_catalanMajorantPartial_le_scaledClosed {M ε : ℝ} (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (hsmall : 4 * M ^ 2 * ε ≤ 1) (N : ℕ) :
    M * catalanMajorantPartial M ε N ≤ catalanScaledClosedMajorant M ε := by
  have hrad : 0 ≤ 1 - 4 * M ^ 2 * ε := by linarith
  induction N with
  | zero =>
      rw [catalanMajorantPartial_zero]
      simpa using catalanScaledClosedMajorant_nonneg (M := M) (ε := ε) hε
  | succ N ih =>
      have hpartial_nonneg := catalanMajorantPartial_nonneg hM hε N
      have hrec := catalanMajorantPartial_succ_le_base_add_quadratic hM hε N
      have hscaled :
          M * catalanMajorantPartial M ε (N + 1) ≤
            M * (M * ε + M * (catalanMajorantPartial M ε N) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hrec hM
      have hscaled_simplified :
          M * catalanMajorantPartial M ε (N + 1) ≤
            M ^ 2 * ε + (M * catalanMajorantPartial M ε N) ^ 2 := by
        calc
          M * catalanMajorantPartial M ε (N + 1) ≤
              M * (M * ε + M * (catalanMajorantPartial M ε N) ^ 2) := hscaled
          _ = M ^ 2 * ε + (M * catalanMajorantPartial M ε N) ^ 2 := by ring
      exact hscaled_simplified.trans
        (catalanScaledClosedMajorant_barrier (M := M) (ε := ε)
          (x := M * catalanMajorantPartial M ε N)
          (mul_nonneg hM hpartial_nonneg) ih hrad)

end YangMills.KP
