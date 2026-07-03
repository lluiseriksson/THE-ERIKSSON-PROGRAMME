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

end YangMills.KP
