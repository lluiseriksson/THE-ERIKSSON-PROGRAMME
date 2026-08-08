/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexOuterActiveDeterminant
import YangMills.RG.BalabanCMP116RestrictedVisitedHeadDefect

/-!
# Finite factorization of a symmetric real complex quadratic

If a complex matrix factors through a finite state `κ`, then the
complexification of the negative symmetric part of its entrywise real matrix
factors through four disjoint copies of `κ`.  The four products are the
matrix, its entrywise conjugate, its transpose, and the conjugate transpose
in the analytic (non-Hermitian) ordering.

No coordinate support is asserted.  The result is purely finite-rank and is
therefore compatible with nonzero exponentially decaying tails.
-/

namespace YangMills.RG

open Matrix

noncomputable section

open scoped Matrix.Norms.Operator

/-- Entrywise complex conjugation without transposing the matrix. -/
def Matrix.entrywiseConj
    {m n : Type*} (A : Matrix m n ℂ) : Matrix m n ℂ :=
  Matrix.transpose A.conjTranspose

@[simp]
theorem Matrix.entrywiseConj_apply
    {m n : Type*} (A : Matrix m n ℂ) (i : m) (j : n) :
    Matrix.entrywiseConj A i j = star (A i j) := by
  rfl

/-- Entrywise conjugation preserves an ordered matrix product. -/
theorem Matrix.entrywiseConj_mul
    {m n p : Type*} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    Matrix.entrywiseConj (A * B) =
      Matrix.entrywiseConj A * Matrix.entrywiseConj B := by
  rw [Matrix.entrywiseConj, Matrix.conjTranspose_mul,
    Matrix.transpose_mul]
  rfl

/-- Four disjoint copies of one finite active state. -/
abbrev CMP116ComplexSymmetricRealActiveState (κ : Type*) :=
  (κ ⊕ κ) ⊕ (κ ⊕ κ)

@[simp]
theorem card_cmp116ComplexSymmetricRealActiveState
    (κ : Type*) [Fintype κ] :
    Fintype.card (CMP116ComplexSymmetricRealActiveState κ) =
      4 * Fintype.card κ := by
  simp [CMP116ComplexSymmetricRealActiveState]
  omega

/-- Left rectangular leg producing the negative symmetric real part of
`L * R`. -/
def Matrix.complexSymmetricRealFactorLeft
    {ι κ : Type*}
    (L : Matrix ι κ ℂ) (R : Matrix κ ι ℂ) :
    Matrix ι (CMP116ComplexSymmetricRealActiveState κ) ℂ :=
  (-1 / 4 : ℂ) •
    Matrix.sumFactorLeft
      (Matrix.sumFactorLeft L (Matrix.entrywiseConj L))
      (Matrix.sumFactorLeft R.transpose
        (Matrix.entrywiseConj R).transpose)

/-- Right rectangular leg paired with
`Matrix.complexSymmetricRealFactorLeft`. -/
def Matrix.complexSymmetricRealFactorRight
    {ι κ : Type*}
    (L : Matrix ι κ ℂ) (R : Matrix κ ι ℂ) :
    Matrix (CMP116ComplexSymmetricRealActiveState κ) ι ℂ :=
  Matrix.sumFactorRight
    (Matrix.sumFactorRight R (Matrix.entrywiseConj R))
    (Matrix.sumFactorRight L.transpose
      (Matrix.entrywiseConj L).transpose)

/-- Exact four-copy factorization of the complexified negative symmetric
entrywise-real part. -/
theorem Matrix.complexSymmetricRealFactorLeft_mul_right
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : Matrix ι κ ℂ) (R : Matrix κ ι ℂ) :
    Matrix.complexSymmetricRealFactorLeft L R *
        Matrix.complexSymmetricRealFactorRight L R =
      (-cmp116Eq214ComplexQuadraticSymmetricRealPart (L * R)).map
        Complex.ofRealHom := by
  rw [Matrix.complexSymmetricRealFactorLeft,
    Matrix.complexSymmetricRealFactorRight, Matrix.smul_mul,
    Matrix.sumFactorLeft_mul_sumFactorRight,
    Matrix.sumFactorLeft_mul_sumFactorRight,
    Matrix.sumFactorLeft_mul_sumFactorRight]
  have hconj :
      Matrix.entrywiseConj L * Matrix.entrywiseConj R =
        Matrix.entrywiseConj (L * R) :=
    (Matrix.entrywiseConj_mul L R).symm
  have htranspose :
      R.transpose * L.transpose = (L * R).transpose :=
    (Matrix.transpose_mul L R).symm
  have hconjTranspose :
      (Matrix.entrywiseConj R).transpose *
          (Matrix.entrywiseConj L).transpose =
        (Matrix.entrywiseConj (L * R)).transpose := by
    simpa only [Matrix.transpose_mul] using
      congrArg Matrix.transpose hconj
  ext i j
  have hconjEntry :
      (Matrix.entrywiseConj L * Matrix.entrywiseConj R) i j =
        star ((L * R) i j) := by
    rw [hconj]
    rfl
  have htransposeEntry :
      (R.transpose * L.transpose) i j = (L * R) j i := by
    rw [htranspose]
    rfl
  have hconjTransposeEntry :
      ((Matrix.entrywiseConj R).transpose *
          (Matrix.entrywiseConj L).transpose) i j =
        star ((L * R) j i) := by
    rw [hconjTranspose]
    rfl
  change
    (-1 / 4 : ℂ) *
        ((L * R + Matrix.entrywiseConj L * Matrix.entrywiseConj R +
          (R.transpose * L.transpose +
            (Matrix.entrywiseConj R).transpose *
              (Matrix.entrywiseConj L).transpose)) i j) = _
  simp only [Matrix.add_apply]
  rw [hconjEntry, htransposeEntry, hconjTransposeEntry]
  simp [cmp116Eq214ComplexQuadraticSymmetricRealPart,
    cmp116Eq214RealPartMatrix,
    Complex.ext_iff]
  <;> ring

/-- A finite factorization of the original complex quadratic yields an
outer-Gaussian bound with four times the original active cardinality. -/
theorem integral_exp_re_complexQuadratic_le_four_mul_factorCard
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ)
    (L : Matrix ι κ ℂ) (R : Matrix κ ι ℂ)
    (hA : A = L * R)
    (hpos :
      (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart A).PosDef)
    (hsmall :
      ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
          Complex.ofRealHom‖ < 1) :
    (∫ x : ι → ℝ,
        Real.exp ((cmp116Eq214ComplexQuadratic A x).re)
        ∂standardGaussianPi ι) ≤
      (Real.sqrt
        ((1 -
          ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
              Complex.ofRealHom‖) ^
            (4 * Fintype.card κ)))⁻¹ := by
  let Lbig := Matrix.complexSymmetricRealFactorLeft L R
  let Rbig := Matrix.complexSymmetricRealFactorRight L R
  have hfactor :
      (-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
          Complex.ofRealHom =
        Lbig * Rbig := by
    rw [hA]
    exact
      (Matrix.complexSymmetricRealFactorLeft_mul_right L R).symm
  have hsmall' : ‖Lbig * Rbig‖ < 1 := by
    rw [← hfactor]
    exact hsmall
  have hbound :=
    integral_exp_re_complexQuadratic_le_activeCard
      A Lbig Rbig hpos hfactor hsmall'
  rw [← hfactor,
    card_cmp116ComplexSymmetricRealActiveState κ] at hbound
  exact hbound

end

end YangMills.RG
