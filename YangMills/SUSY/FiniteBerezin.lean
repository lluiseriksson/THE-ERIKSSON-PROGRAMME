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

/-- The finite Berezin functional with an algebraic left weight.  This is the
finite-dimensional Grassmann analogue of integrating `F` against the weight
`weight`: it extracts the top coefficient of `weight * F`. -/
def finiteBerezinWeighted (n : ℕ) (weight : FiniteExterior n) :
    FiniteExterior n →ₗ[ℂ] ℂ :=
  (finiteBerezinTop n).comp (LinearMap.mulLeft ℂ weight)

/-- Weighted finite Berezin integration is top-coefficient extraction after
left multiplication by the weight. -/
@[simp] theorem finiteBerezinWeighted_apply (n : ℕ)
    (weight F : FiniteExterior n) :
    finiteBerezinWeighted n weight F = finiteBerezinTop n (weight * F) := by
  rfl

/-- Unit weight recovers the unweighted finite Berezin top functional. -/
@[simp] theorem finiteBerezinWeighted_one (n : ℕ) :
    finiteBerezinWeighted n (1 : FiniteExterior n) = finiteBerezinTop n := by
  ext F
  simp [finiteBerezinWeighted]

/-- The simplest finite Berezin density with a prescribed top-degree
coefficient.  This is not yet a Gaussian/Pfaffian construction; it is the
algebraic normalization seed saying that a top-degree density controls the
weighted integral of constants. -/
def finiteBerezinTopWeight (n : ℕ) (a : ℂ) : FiniteExterior n :=
  1 + a • (finiteExteriorBasis n (Finset.univ : Finset (Fin n)))

/-- The top exterior basis monomial has weighted integral one against the
constant observable. -/
@[simp] theorem finiteBerezinWeighted_top_basis_one (n : ℕ) :
    finiteBerezinWeighted n
        ((finiteExteriorBasis n) (Finset.univ : Finset (Fin n)))
        (1 : FiniteExterior n) = 1 := by
  simp [finiteBerezinWeighted_apply]

/-- Zero top coefficient leaves the unit density. -/
@[simp] theorem finiteBerezinTopWeight_zero (n : ℕ) :
    finiteBerezinTopWeight n 0 = 1 := by
  simp [finiteBerezinTopWeight]

/-- In positive fermionic dimension, the top-density weight integrates the
constant observable `1` to its top coefficient. -/
@[simp] theorem finiteBerezinWeighted_topWeight_one_of_pos {n : ℕ}
    (hn : 0 < n) (a : ℂ) :
    finiteBerezinWeighted n (finiteBerezinTopWeight n a)
        (1 : FiniteExterior n) = a := by
  simp [finiteBerezinTopWeight, finiteBerezinWeighted_apply,
    finiteBerezinTop_one_of_pos hn]

/-- In positive fermionic dimension, the top-density weight integrates scalar
constants by multiplying them with the top coefficient. -/
@[simp] theorem finiteBerezinWeighted_topWeight_algebraMap_of_pos {n : ℕ}
    (hn : 0 < n) (a z : ℂ) :
    finiteBerezinWeighted n (finiteBerezinTopWeight n a)
        (algebraMap ℂ (FiniteExterior n) z) = a * z := by
  rw [Algebra.algebraMap_eq_smul_one]
  rw [map_smul]
  simp [finiteBerezinTopWeight, finiteBerezinWeighted_apply,
    finiteBerezinTop_one_of_pos hn, mul_comm]

/-- Exterior basis multiplication for non-disjoint finite generator sets, in the
cardinality-indexed form used internally by Mathlib's exterior-algebra basis
API.  Repeated Grassmann generators kill the product. -/
@[simp] theorem finiteExteriorBasis_powersetCard_mul_of_not_disjoint
    {n m k : ℕ} (s : Set.powersetCard (Fin n) m)
    (t : Set.powersetCard (Fin n) k)
    (h : ¬ Disjoint (s : Finset (Fin n)) (t : Finset (Fin n))) :
    (finiteExteriorBasis n (s : Finset (Fin n))) *
      (finiteExteriorBasis n (t : Finset (Fin n))) = 0 := by
  simpa [finiteExteriorBasis] using
    ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun ℂ (Fin n)) s t h

/-- Exterior basis multiplication for disjoint finite generator sets.  The
orientation sign is kept explicit; later finite Gaussian/Pfaffian work must
consume this sign rather than hide it in a concrete decision procedure. -/
theorem finiteExteriorBasis_powersetCard_mul_of_disjoint
    {n m k : ℕ} (s : Set.powersetCard (Fin n) m)
    (t : Set.powersetCard (Fin n) k)
    (h : Disjoint (s : Finset (Fin n)) (t : Finset (Fin n))) :
    (finiteExteriorBasis n (s : Finset (Fin n))) *
      (finiteExteriorBasis n (t : Finset (Fin n))) =
        (Set.powersetCard.permOfDisjoint h).sign •
          finiteExteriorBasis n
            (Set.powersetCard.disjUnion h : Finset (Fin n)) := by
  simpa [finiteExteriorBasis] using
    ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun ℂ (Fin n)) s t h

/-- Finset-facing Grassmann product rule: if two exterior basis monomials share
a generator, their product is zero. -/
@[simp] theorem finiteExteriorBasis_mul_of_not_disjoint {n : ℕ}
    {s t : Finset (Fin n)} (h : ¬ Disjoint s t) :
    (finiteExteriorBasis n s) * (finiteExteriorBasis n t) = 0 := by
  let sp : Set.powersetCard (Fin n) s.card :=
    Set.powersetCard.ofCard (s := s) rfl
  let tp : Set.powersetCard (Fin n) t.card :=
    Set.powersetCard.ofCard (s := t) rfl
  have hp : ¬ Disjoint (sp : Finset (Fin n)) (tp : Finset (Fin n)) := by
    simpa [sp, tp] using h
  have hmul := finiteExteriorBasis_powersetCard_mul_of_not_disjoint sp tp hp
  simpa [sp, tp] using hmul

/-- The Berezin top coefficient of a product with a repeated generator is zero. -/
@[simp] theorem finiteBerezinTop_basis_mul_of_not_disjoint {n : ℕ}
    {s t : Finset (Fin n)} (h : ¬ Disjoint s t) :
    finiteBerezinTop n ((finiteExteriorBasis n s) * (finiteExteriorBasis n t)) =
      0 := by
  rw [finiteExteriorBasis_mul_of_not_disjoint h]
  simp

/-- If two disjoint cardinality-indexed basis monomials fill the top degree,
their Berezin top coefficient is exactly the explicit exterior orientation
sign. -/
theorem finiteBerezinTop_powersetCard_mul_of_disjoint_top
    {n m k : ℕ} (s : Set.powersetCard (Fin n) m)
    (t : Set.powersetCard (Fin n) k)
    (h : Disjoint (s : Finset (Fin n)) (t : Finset (Fin n)))
    (htop : (Set.powersetCard.disjUnion h : Finset (Fin n)) =
      (Finset.univ : Finset (Fin n))) :
    finiteBerezinTop n
        ((finiteExteriorBasis n (s : Finset (Fin n))) *
          (finiteExteriorBasis n (t : Finset (Fin n)))) =
      (Set.powersetCard.permOfDisjoint h).sign • (1 : ℂ) := by
  have hunion : (s : Finset (Fin n)) ∪ (t : Finset (Fin n)) =
      (Finset.univ : Finset (Fin n)) := by
    ext x
    have hx :
        (x ∈ (Set.powersetCard.disjUnion h : Finset (Fin n))) ↔
          x ∈ (Finset.univ : Finset (Fin n)) := by
      rw [htop]
    simpa [Set.powersetCard.mem_disjUnion, Finset.mem_union] using hx
  rw [finiteExteriorBasis_powersetCard_mul_of_disjoint s t h]
  simp [finiteBerezinTop, hunion]

/-- The top exterior monomial annihilates every nonempty basis monomial on the
right: multiplying by a repeated generator gives zero. -/
@[simp] theorem finiteExteriorBasis_univ_mul_of_nonempty {n : ℕ}
    {s : Finset (Fin n)} (hs : s.Nonempty) :
    (finiteExteriorBasis n (Finset.univ : Finset (Fin n))) *
      (finiteExteriorBasis n s) = 0 := by
  apply finiteExteriorBasis_mul_of_not_disjoint
  intro hdisj
  rcases hs with ⟨i, hi⟩
  exact (Finset.disjoint_left.mp hdisj (Finset.mem_univ i) hi)

/-- Every nonempty basis monomial annihilates the top exterior monomial on the
right: again, multiplying by a repeated generator gives zero. -/
@[simp] theorem finiteExteriorBasis_mul_univ_of_nonempty {n : ℕ}
    {s : Finset (Fin n)} (hs : s.Nonempty) :
    (finiteExteriorBasis n s) *
      (finiteExteriorBasis n (Finset.univ : Finset (Fin n))) = 0 := by
  apply finiteExteriorBasis_mul_of_not_disjoint
  intro hdisj
  rcases hs with ⟨i, hi⟩
  exact (Finset.disjoint_left.mp hdisj hi (Finset.mem_univ i))

/-- In positive fermionic dimension, the top-density weight integrates the
empty basis monomial to its prescribed top coefficient. -/
@[simp] theorem finiteBerezinWeighted_topWeight_basis_empty_of_pos {n : ℕ}
    (hn : 0 < n) (a : ℂ) :
    finiteBerezinWeighted n (finiteBerezinTopWeight n a)
        (finiteExteriorBasis n (∅ : Finset (Fin n))) = a := by
  rw [finiteExteriorBasis_empty]
  exact finiteBerezinWeighted_topWeight_one_of_pos hn a

/-- On nonempty basis monomials, the top-density weight contributes no extra
term: the added top monomial has repeated generator support and annihilates the
observable before top-coefficient extraction. -/
theorem finiteBerezinWeighted_topWeight_basis_of_nonempty {n : ℕ}
    (a : ℂ) {s : Finset (Fin n)} (hs : s.Nonempty) :
    finiteBerezinWeighted n (finiteBerezinTopWeight n a)
        (finiteExteriorBasis n s) =
      finiteBerezinTop n (finiteExteriorBasis n s) := by
  calc
    finiteBerezinWeighted n (finiteBerezinTopWeight n a)
        (finiteExteriorBasis n s) =
        finiteBerezinTop n
          ((1 + a • finiteExteriorBasis n (Finset.univ : Finset (Fin n))) *
            finiteExteriorBasis n s) := by
      rfl
    _ = finiteBerezinTop n
        (finiteExteriorBasis n s +
          (a • finiteExteriorBasis n (Finset.univ : Finset (Fin n))) *
            finiteExteriorBasis n s) := by
      rw [add_mul, one_mul]
    _ = finiteBerezinTop n
        (finiteExteriorBasis n s +
          a • ((finiteExteriorBasis n (Finset.univ : Finset (Fin n))) *
            finiteExteriorBasis n s)) := by
      rw [smul_mul_assoc]
    _ = finiteBerezinTop n (finiteExteriorBasis n s + a • 0) := by
      rw [finiteExteriorBasis_univ_mul_of_nonempty hs]
    _ = finiteBerezinTop n (finiteExteriorBasis n s) := by simp

/-- In positive fermionic dimension, the top-density weight integrates the top
basis monomial to one. -/
@[simp] theorem finiteBerezinWeighted_topWeight_top_basis_of_pos {n : ℕ}
    (hn : 0 < n) (a : ℂ) :
    finiteBerezinWeighted n (finiteBerezinTopWeight n a)
        (finiteExteriorBasis n (Finset.univ : Finset (Fin n))) = 1 := by
  have huniv_nonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, by simp⟩
  rw [finiteBerezinWeighted_topWeight_basis_of_nonempty a huniv_nonempty]
  simp

/-- Nonempty, non-top basis monomials still integrate to zero against the
top-density weight. -/
theorem finiteBerezinWeighted_topWeight_basis_of_nonempty_ne_top {n : ℕ}
    (a : ℂ) {s : Finset (Fin n)} (hs : s.Nonempty)
    (hstop : s ≠ (Finset.univ : Finset (Fin n))) :
    finiteBerezinWeighted n (finiteBerezinTopWeight n a)
        (finiteExteriorBasis n s) = 0 := by
  rw [finiteBerezinWeighted_topWeight_basis_of_nonempty a hs]
  exact finiteBerezinTop_basis_of_ne_top n hstop

/-- Grassmann nilpotence for finite exterior basis generators: each degree-one
basis monomial squares to zero.  This is the first generator-level algebraic
fact needed before finite Gaussian/Pfaffian identities can be stated honestly. -/
@[simp] theorem finiteExteriorBasis_singleton_mul_self {n : ℕ} (i : Fin n) :
    (finiteExteriorBasis n ({i} : Finset (Fin n))) *
      (finiteExteriorBasis n ({i} : Finset (Fin n))) = 0 := by
  let s : Set.powersetCard (Fin n) 1 :=
    Set.powersetCard.ofCard (s := ({i} : Finset (Fin n))) (by simp)
  have hndisj : ¬ Disjoint (s : Finset (Fin n)) (s : Finset (Fin n)) := by
    simp [s]
  have hmul :=
    ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun ℂ (Fin n)) s s
      hndisj
  change (Pi.basisFun ℂ (Fin n)).ExteriorAlgebra ({i} : Finset (Fin n)) *
      (Pi.basisFun ℂ (Fin n)).ExteriorAlgebra ({i} : Finset (Fin n)) = 0
  simpa [s] using hmul

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

/-- A finite algebraic exact-Ward package for a weighted Berezin functional.
The Ward identity is deliberately an explicit field: later Gaussian/Berezin
work must construct a weight and a differential that satisfy it. -/
structure FiniteBerezinWeightedExactWard (n : ℕ)
    (weight : FiniteExterior n) where
  /-- The exact finite Ward differential. -/
  Q : FiniteExterior n →ₗ[ℂ] FiniteExterior n
  /-- Exact Ward identity for the weighted finite Berezin functional. -/
  ward_exact : ∀ F : FiniteExterior n, finiteBerezinWeighted n weight (Q F) = 0

/-- Exact weighted finite Berezin Ward cancellation of a `Q`-exact term. -/
theorem finiteBerezinWeighted_expect_Q_eq_zero {n : ℕ}
    {weight : FiniteExterior n}
    (W : FiniteBerezinWeightedExactWard n weight) (F : FiniteExterior n) :
    finiteBerezinWeighted n weight (W.Q F) = 0 :=
  W.ward_exact F

/-- Exact weighted finite Berezin cancellation for a decomposition
`H = Q B + R`. -/
theorem finiteBerezinWeighted_eq_expect_remainder_of_exactWard {n : ℕ}
    {weight : FiniteExterior n}
    (W : FiniteBerezinWeightedExactWard n weight) (H B R : FiniteExterior n)
    (hdec : H = W.Q B + R) :
    finiteBerezinWeighted n weight H = finiteBerezinWeighted n weight R := by
  calc
    finiteBerezinWeighted n weight H =
        finiteBerezinWeighted n weight (W.Q B + R) := by rw [hdec]
    _ = finiteBerezinWeighted n weight (W.Q B) +
        finiteBerezinWeighted n weight R := by rw [map_add]
    _ = 0 + finiteBerezinWeighted n weight R := by
      rw [finiteBerezinWeighted_expect_Q_eq_zero W B]
    _ = finiteBerezinWeighted n weight R := by rw [zero_add]

end

end YangMills.SUSY
