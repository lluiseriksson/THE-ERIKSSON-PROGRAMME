import YangMills.RG.BalabanCMP98GAdSeries
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# CMP99 (3.51) diagonal-sign no-go

CMP99 fixes `R(U) X = U X U⁻¹` and writes
`R(exp(i eta A')) = exp(i eta ad_{A'})` in (3.50). Thus the infinitesimal
convention is `ad_A X = A X - X A`, the same convention as
`cmp98AdCLM`.

At unit spacing, the canonical oriented sum is `A_sum = -Dstar`. The raw
Laplacian increment is therefore `-i [A_sum, phi] = +i [Dstar, phi]`.
Printed (3.51) instead contains `-i [Dstar, phi]`. This file records both
the algebraic sign and an explicit noncommuting `2 x 2` witness separating
the two expressions.

Honest scope: this is a no-go for silently identifying the raw canonical
stencil with the printed diagonal sign. It does not decide whether CMP99
contains a typographical error or whether a further source dictionary was
intended. It does not prove (3.51), (3.54), window 15, a terminal field, or
a `TermSource` instance.
-/

namespace YangMills.RG

noncomputable section

local instance cmp99Eq351DiagonalSignNoGoMatrixNormedRing :
    NormedRing (Matrix (Fin 2) (Fin 2) ℂ) :=
  Matrix.frobeniusNormedRing

local instance cmp99Eq351DiagonalSignNoGoMatrixNormedAlgebra :
    NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Matrix.frobeniusNormedAlgebra

/-- The unit-spacing diagonal contribution obtained from the raw exponential
stencil after summing the canonical oriented perturbations. -/
def cmp99Eq351RawDiagonalUnit
    (orientedSum phi : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  -(Complex.I • cmp98AdCLM orientedSum phi)

/-- The diagonal contribution printed in the Laplacian expansion (3.51). -/
def cmp99Eq351PrintedDiagonal
    (Dstar phi : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  -(Complex.I • cmp98AdCLM Dstar phi)

/-- With the canonical oriented sum `-Dstar`, the raw exponential stencil
has the positive `+i[Dstar,phi]` sign. -/
theorem cmp99Eq351RawDiagonalUnit_neg_eq_positive
    (Dstar phi : Matrix (Fin 2) (Fin 2) ℂ) :
    cmp99Eq351RawDiagonalUnit (-Dstar) phi =
      Complex.I • cmp98AdCLM Dstar phi := by
  simp only [cmp99Eq351RawDiagonalUnit, cmp98AdCLM_apply, neg_mul, mul_neg]
  module

/-- A smallest noncommuting source-adjoint/field pair. -/
def cmp99Eq351DiagonalSignWitnessDstar : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- The companion field for the diagonal-sign witness. -/
def cmp99Eq351DiagonalSignWitnessPhi : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- The canonical raw diagonal and the sign printed in (3.51) are genuinely
different; the discrepancy is not hidden by commutativity. -/
theorem cmp99Eq351RawDiagonalUnit_neg_ne_printedDiagonal :
    cmp99Eq351RawDiagonalUnit (-cmp99Eq351DiagonalSignWitnessDstar)
        cmp99Eq351DiagonalSignWitnessPhi ≠
      cmp99Eq351PrintedDiagonal cmp99Eq351DiagonalSignWitnessDstar
        cmp99Eq351DiagonalSignWitnessPhi := by
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) h
  norm_num [cmp99Eq351RawDiagonalUnit, cmp99Eq351PrintedDiagonal,
    cmp99Eq351DiagonalSignWitnessDstar, cmp99Eq351DiagonalSignWitnessPhi,
    cmp98AdCLM_apply, Matrix.mul_apply] at h00
  have him := congrArg Complex.im h00
  norm_num at him

/-- Although the exact signs disagree, the pointwise matrix norm consumed by
the quantitative estimate (3.54) is unchanged. This permits a corrected raw
regrouping to feed the printed absolute bound without asserting the false
exact identity. -/
theorem norm_cmp99Eq351RawDiagonalUnit_neg_eq_printedDiagonal
    (Dstar phi : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖cmp99Eq351RawDiagonalUnit (-Dstar) phi‖ =
      ‖cmp99Eq351PrintedDiagonal Dstar phi‖ := by
  rw [cmp99Eq351RawDiagonalUnit_neg_eq_positive]
  simp [cmp99Eq351PrintedDiagonal]

end

end YangMills.RG
