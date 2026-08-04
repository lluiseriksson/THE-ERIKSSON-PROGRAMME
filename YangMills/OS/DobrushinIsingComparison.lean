/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinIsing
import YangMills.OS.DobrushinMeasureComparison

/-!
# D-7 — boundary comparison for two Ising Hamiltonians

This module instantiates the abstract two-specification comparison theorem.
The two Ising coupling matrices live on the same finite chart.  Away from an
explicit defect predicate their complete rows agree, hence their heat-bath
kernels agree exactly.  On a defect row total variation is bounded by one.

If every defect row is at distance at least `R` from every coordinate on
which the observable really depends, the expectation difference is bounded
by

```
α^R / (1 - α) * ∑ j, δ_j f.
```

The Dobrushin window and the finite-range hypotheses are imposed only on the
first Hamiltonian.  No Cauchy property, limiting state, or boundary-tail
estimate occurs among the inputs.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Equal coupling rows give equal Ising heat-bath kernels at that site. -/
theorem heatBath_ising_eq_of_row_eq
    (J K : ι → ι → ℝ)
    (hJdiag : ∀ a, J a a = 0) (hJsim : ∀ a b, J a b = J b a)
    (hKdiag : ∀ a, K a a = 0) (hKsim : ∀ a b, K a b = K b a)
    (i : ι) (hroweq : ∀ k, J i k = K i k) (η : ι → Fin 2) :
    heatBath (isingWeight J) i η = heatBath (isingWeight K) i η := by
  funext s
  rw [heatBath_ising J hJdiag hJsim i η s,
    heatBath_ising K hKdiag hKsim i η s]
  have hfield : localField J η i = localField K η i := by
    unfold localField
    exact Finset.sum_congr rfl fun k _ => by rw [hroweq k]
  rw [hfield]

/-- **Ising boundary-perturbation comparison.**  `D i` says that row `i` of
the Hamiltonian was modified.  The bound is uniform in the cardinality of
the common finite chart. -/
theorem ising_boundary_comparison
    (J K : ι → ι → ℝ)
    (hJdiag : ∀ a, J a a = 0) (hJsim : ∀ a b, J a b = J b a)
    (hKdiag : ∀ a, K a a = 0) (hKsim : ∀ a b, K a b = K b a)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, Real.tanh |J i k| ≤ α)
    (d : ι → ι → ℕ) (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hJsupp : ∀ i j, 1 < d i j → J i j = 0)
    (D : ι → Prop)
    (hsame : ∀ i, ¬ D i → ∀ k, J i k = K i k)
    (f : (ι → Fin 2) → ℝ) (R : ℕ)
    (hfar : ∀ i j, D i → deltaAt j f ≠ 0 → R ≤ d j i) :
    |expect (gibbsMu (isingWeight J)) f
        - expect (gibbsMu (isingWeight K)) f|
      ≤ (α ^ R / (1 - α)) * ∑ j, deltaAt j f := by
  classical
  let b : ι → ℝ := fun i => if D i then 1 else 0
  have hb0 : ∀ i, 0 ≤ b i := by
    intro i
    simp only [b]
    split <;> norm_num
  have hb1 : ∀ i, b i ≤ 1 := by
    intro i
    simp only [b]
    split <;> norm_num
  have hdefect : ∀ i η,
      TV (heatBath (isingWeight J) i η) (heatBath (isingWeight K) i η) ≤ b i := by
    intro i η
    by_cases hi : D i
    · rw [show b i = 1 by simp [b, hi]]
      exact TV_le_one_of_probability
        (heatBath_nonneg (fun ξ => isingWeight_pos J ξ) i η)
        (heatBath_sum_one (fun ξ => isingWeight_pos J ξ) i η)
        (heatBath_nonneg (fun ξ => isingWeight_pos K ξ) i η)
        (heatBath_sum_one (fun ξ => isingWeight_pos K ξ) i η)
    · have heq := heatBath_ising_eq_of_row_eq J K hJdiag hJsim hKdiag hKsim
        i (hsame i hi) η
      rw [show b i = 0 by simp [b, hi], heq, TV_self]
  let C : Matrix ι ι ℝ := dobMatrixOf (isingWeight J)
  refine measure_comparison_boundary_decay
    (gibbsMu_nonneg (fun η => isingWeight_pos J η))
    (gibbsMu_sum_one (fun η => isingWeight_pos J η))
    (gibbsMu_nonneg (fun η => isingWeight_pos K η))
    (gibbsMu_sum_one (fun η => isingWeight_pos K η))
    (heatBath_nonneg (fun η => isingWeight_pos J η))
    (heatBath_sum_one (fun η => isingWeight_pos J η))
    (heatBath_sum_one (fun η => isingWeight_pos K η))
    (heatBath_local (isingWeight J))
    (fun i F => expect_heatBath (fun η => isingWeight_pos J η) i F)
    (fun i F => expect_heatBath (fun η => isingWeight_pos K η) i F)
    (C := C) ?_ ?_ hα0 hα1 ?_ d hself htri ?_
    hb0 hb1 hdefect f R ?_
  · intro i
    exact dobCoeff_diag (isingWeight J) i
  · intro i k _ η η' hagree
    exact dobCoeff_dominates (isingWeight J) i k η η' hagree
  · intro i
    exact dobCoeff_ising_row_le J hJdiag hJsim i (hrow i)
  · intro i j hd
    exact dobCoeff_ising_zero J hJdiag hJsim i j (hJsupp i j hd)
  · intro i j hbi hδ
    have hi : D i := by
      by_contra hni
      exact hbi (by simp [b, hni])
    exact hfar i j hi hδ

/-! ## Cutting a volume inside one common chart -/

/-- Delete every bond with at least one endpoint outside `A`.  Spins outside
`A` are then independent uniform spectator variables. -/
noncomputable def restrictCoupling (J : ι → ι → ℝ) (A : ι → Prop) :
    ι → ι → ℝ := by
  classical
  exact fun i j => if A i ∧ A j then J i j else 0

theorem restrictCoupling_diag (J : ι → ι → ℝ) (A : ι → Prop)
    (hdiag : ∀ i, J i i = 0) :
    ∀ i, restrictCoupling J A i i = 0 := by
  classical
  intro i
  by_cases hi : A i <;> simp [restrictCoupling, hi, hdiag i]

theorem restrictCoupling_symm (J : ι → ι → ℝ) (A : ι → Prop)
    (hsymm : ∀ i j, J i j = J j i) :
    ∀ i j, restrictCoupling J A i j = restrictCoupling J A j i := by
  classical
  intro i j
  by_cases hi : A i <;> by_cases hj : A j <;>
    simp [restrictCoupling, hi, hj, hsymm i j]

/-- Common-chart volume comparison: a full Ising Hamiltonian versus the
Hamiltonian obtained by cutting out `A`.  The defect predicate is not guessed:
it is exactly the set of rows changed by the cut. -/
theorem ising_restriction_comparison
    (J : ι → ι → ℝ)
    (hJdiag : ∀ a, J a a = 0) (hJsim : ∀ a b, J a b = J b a)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, Real.tanh |J i k| ≤ α)
    (d : ι → ι → ℕ) (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hJsupp : ∀ i j, 1 < d i j → J i j = 0)
    (A : ι → Prop) (f : (ι → Fin 2) → ℝ) (R : ℕ)
    (hfar : ∀ i j,
      (∃ k, J i k ≠ restrictCoupling J A i k) →
      deltaAt j f ≠ 0 → R ≤ d j i) :
    |expect (gibbsMu (isingWeight J)) f
        - expect (gibbsMu (isingWeight (restrictCoupling J A))) f|
      ≤ (α ^ R / (1 - α)) * ∑ j, deltaAt j f := by
  classical
  let D : ι → Prop := fun i => ∃ k, J i k ≠ restrictCoupling J A i k
  refine ising_boundary_comparison J (restrictCoupling J A)
    hJdiag hJsim (restrictCoupling_diag J A hJdiag)
    (restrictCoupling_symm J A hJsim) hα0 hα1 hrow d hself htri hJsupp
    D ?_ f R ?_
  · intro i hi k
    by_contra hik
    exact hi ⟨k, hik⟩
  · intro i j hi hδ
    exact hfar i j hi hδ

end Dobrushin

end YangMills.OS
