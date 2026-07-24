/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexSymmetricRealFactorization
import YangMills.RG.BalabanCMP116SourcePi4FullComplexR1

/-!
# Active factorization of the `R1` covariance telescope

Suppose the covariance defect factors through a finite state `κ`, and the
Gamma defect is obtained by sandwiching the same defect.  Each of the three
terms in the exact `R1` telescope then factors through one copy of `κ`.
Their sum therefore factors through three copies, before the four-copy
symmetric-real construction is applied.

This module is pure matrix algebra.  It does not replace the physical source
factorization: later source-specific code must instantiate `A`, `B`, `U`,
and `V` from the restricted visited resolvent.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- Three disjoint copies of the covariance-defect active state. -/
abbrev CMP116R1TelescopeActiveState (κ : Type*) :=
  (κ ⊕ κ) ⊕ κ

@[simp]
theorem card_cmp116R1TelescopeActiveState
    (κ : Type*) [Fintype κ] :
    Fintype.card (CMP116R1TelescopeActiveState κ) =
      3 * Fintype.card κ := by
  simp [CMP116R1TelescopeActiveState]
  omega

/-- Left leg of the three-term `R1` telescope factorization. -/
def Matrix.r1TelescopeFactorLeft
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G0 C0 U V : Matrix ι ι ℂ)
    (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ) :
    Matrix ι (CMP116R1TelescopeActiveState κ) ℂ :=
  Matrix.sumFactorLeft
    (Matrix.sumFactorLeft
      (B * V).transpose
      (G0.transpose * A))
    (G0.transpose * C0 * (U * A))

/-- Right leg paired with `Matrix.r1TelescopeFactorLeft`. -/
def Matrix.r1TelescopeFactorRight
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G1 C1 U V : Matrix ι ι ℂ)
    (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ) :
    Matrix (CMP116R1TelescopeActiveState κ) ι ℂ :=
  Matrix.sumFactorRight
    (Matrix.sumFactorRight
      ((U * A).transpose * C1 * G1)
      (B * G1))
    (B * V)

/-- Exact finite factorization of the covariance-sandwich telescope. -/
theorem Matrix.r1TelescopeFactorLeft_mul_right
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (G0 G1 C0 C1 U V : Matrix ι ι ℂ)
    (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ)
    (hC : C1 - C0 = A * B)
    (hG : G1 - G0 = U * (A * B) * V) :
    Matrix.r1TelescopeFactorLeft G0 C0 U V A B *
        Matrix.r1TelescopeFactorRight G1 C1 U V A B =
      G1.transpose * C1 * G1 - G0.transpose * C0 * G0 := by
  rw [Matrix.r1TelescopeFactorLeft,
    Matrix.r1TelescopeFactorRight,
    Matrix.sumFactorLeft_mul_sumFactorRight,
    Matrix.sumFactorLeft_mul_sumFactorRight]
  rw [Matrix.transpose_mul_cov_mul_sub_eq_telescope G0 G1 C0 C1,
    hC, hG, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Applying the four-copy symmetric-real construction after the three-term
telescope gives twelve copies of the original active covariance state. -/
abbrev CMP116R1SymmetricRealActiveState (κ : Type*) :=
  CMP116ComplexSymmetricRealActiveState
    (CMP116R1TelescopeActiveState κ)

@[simp]
theorem card_cmp116R1SymmetricRealActiveState
    (κ : Type*) [Fintype κ] :
    Fintype.card (CMP116R1SymmetricRealActiveState κ) =
      12 * Fintype.card κ := by
  simp [CMP116R1SymmetricRealActiveState]
  omega

end

end YangMills.RG
