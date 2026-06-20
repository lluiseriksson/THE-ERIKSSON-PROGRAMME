/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib

/-!
# Finite Berezin coefficient functional

This file starts the finite supergaussian substrate under the abstract Ward
interface.  It uses Mathlib's exterior algebra on the finite complex vector
space `Fin n → ℂ` and defines the finite Berezin functional as the coefficient
of the top exterior monomial.

Honest scope: this is only the algebraic top-coefficient functional.  It does
not yet construct a Gaussian Berezin weight, a fermionic covariance, or a
determinantal cancellation theorem.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.SUSY

noncomputable section

/-- The finite complex exterior algebra used by the Berezin toy substrate. -/
abbrev FiniteExterior (n : ℕ) := ExteriorAlgebra ℂ (Fin n → ℂ)

/-- The canonical finite exterior-algebra basis over complex generators indexed
by `Fin n`.  A basis vector is indexed by the finite set of generators appearing
in the wedge monomial. -/
def finiteExteriorBasis (n : ℕ) :
    Module.Basis (Finset (Fin n)) ℂ (FiniteExterior n) :=
  (Pi.basisFun ℂ (Fin n)).ExteriorAlgebra

/-- The finite Berezin functional: coefficient of the top exterior monomial. -/
def finiteBerezinTop (n : ℕ) : FiniteExterior n →ₗ[ℂ] ℂ :=
  (finiteExteriorBasis n).coord (Finset.univ : Finset (Fin n))

/-- The empty exterior basis vector is the unit. -/
@[simp] theorem finiteExteriorBasis_empty (n : ℕ) :
    finiteExteriorBasis n (∅ : Finset (Fin n)) =
      (1 : ExteriorAlgebra ℂ (Fin n → ℂ)) := by
  simp [finiteExteriorBasis, ExteriorAlgebra.basis_apply]

/-- The finite Berezin functional reads `1` on the top monomial and `0` on all
other exterior basis monomials. -/
@[simp] theorem finiteBerezinTop_basis (n : ℕ) (s : Finset (Fin n)) :
    finiteBerezinTop n ((finiteExteriorBasis n) s) =
      if s = (Finset.univ : Finset (Fin n)) then 1 else 0 := by
  simp only [finiteBerezinTop, finiteExteriorBasis, Module.Basis.coord_apply,
    Module.Basis.repr_self]
  by_cases h : s = (Finset.univ : Finset (Fin n))
  · subst h
    simp
  · rw [Finsupp.single_eq_of_ne (Ne.symm h)]
    simp [h]

/-- The top monomial has Berezin coefficient one. -/
@[simp] theorem finiteBerezinTop_top_basis (n : ℕ) :
    finiteBerezinTop n
        ((finiteExteriorBasis n) (Finset.univ : Finset (Fin n))) = 1 := by
  simp

/-- Any non-top exterior basis monomial has Berezin coefficient zero. -/
theorem finiteBerezinTop_basis_of_ne_top (n : ℕ) {s : Finset (Fin n)}
    (hs : s ≠ (Finset.univ : Finset (Fin n))) :
    finiteBerezinTop n ((finiteExteriorBasis n) s) = 0 := by
  simp [hs]

/-- In positive fermionic dimension, constants have zero Berezin integral. -/
@[simp] theorem finiteBerezinTop_one_of_pos {n : ℕ} (hn : 0 < n) :
    finiteBerezinTop n (1 : FiniteExterior n) = 0 := by
  rw [← finiteExteriorBasis_empty n]
  have hempty :
      (∅ : Finset (Fin n)) ≠ (Finset.univ : Finset (Fin n)) := by
    intro h
    have hcard := congrArg Finset.card h
    have hzero : 0 = n := by simpa using hcard
    exact (Nat.ne_of_gt hn) hzero.symm
  exact finiteBerezinTop_basis_of_ne_top n hempty

/-- In zero fermionic dimension, the Berezin functional is evaluation on the
scalar/empty monomial, so it sends `1` to `1`. -/
@[simp] theorem finiteBerezinTop_one_zero :
    finiteBerezinTop 0 (1 : FiniteExterior 0) = 1 := by
  have huniv : (Finset.univ : Finset (Fin 0)) = ∅ := by
    ext x
    exact x.elim0
  rw [← finiteExteriorBasis_empty 0, ← huniv]
  exact finiteBerezinTop_top_basis 0

/-- Scalar constants have zero finite Berezin integral in positive fermionic
dimension. -/
@[simp] theorem finiteBerezinTop_algebraMap_of_pos {n : ℕ}
    (hn : 0 < n) (z : ℂ) :
    finiteBerezinTop n (algebraMap ℂ (FiniteExterior n) z) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul,
    finiteBerezinTop_one_of_pos hn, smul_zero]

/-- A finite algebraic exact-Ward package for the Berezin top-coefficient
functional.  This is deliberately linear/algebraic, not an `ApproxWardComplex`:
the exterior algebra is not given an artificial norm or topology here. -/
structure FiniteBerezinExactWard (n : ℕ) where
  /-- The exact finite Ward differential. -/
  Q : FiniteExterior n →ₗ[ℂ] FiniteExterior n
  /-- Exact Ward identity for the finite Berezin functional. -/
  ward_exact : ∀ F : FiniteExterior n, finiteBerezinTop n (Q F) = 0

/-- Exact finite Berezin Ward cancellation of a `Q`-exact term. -/
theorem finiteBerezin_expect_Q_eq_zero {n : ℕ}
    (W : FiniteBerezinExactWard n) (F : FiniteExterior n) :
    finiteBerezinTop n (W.Q F) = 0 :=
  W.ward_exact F

/-- Exact finite Berezin cancellation for a decomposition `H = Q B + R`. -/
theorem finiteBerezin_eq_expect_remainder_of_exactWard {n : ℕ}
    (W : FiniteBerezinExactWard n) (H B R : FiniteExterior n)
    (hdec : H = W.Q B + R) :
    finiteBerezinTop n H = finiteBerezinTop n R := by
  calc
    finiteBerezinTop n H = finiteBerezinTop n (W.Q B + R) := by rw [hdec]
    _ = finiteBerezinTop n (W.Q B) + finiteBerezinTop n R := by rw [map_add]
    _ = 0 + finiteBerezinTop n R := by
      rw [finiteBerezin_expect_Q_eq_zero W B]
    _ = finiteBerezinTop n R := by rw [zero_add]

end

end YangMills.SUSY
