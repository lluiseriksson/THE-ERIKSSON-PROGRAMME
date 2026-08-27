import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
PRE-VALIDATION: algebra-only reproducer; no compiler verdict is claimed.

# CMP99 (3.51): diagonal-sign algebra reproducer

This file isolates the scalar and noncommutative algebra behind the diagonal
species.  It deliberately contains no project declaration: the warm gate can
decide the sign before another project-wide bootstrap.

If the raw Laplacian increment is

`-eta⁻² [i eta S, Phi]`

and the printed adjoint dictionary is `Dstar = -eta⁻¹ S`, then the raw term is
`+i [Dstar, Phi]`.  The source line (3.51) prints the opposite sign.  A later
project theorem must therefore either locate a different source dictionary or
seal the mismatch; changing either existing definition is not an admissible
repair.
-/

namespace Eq351DiagonalSignAlgebra

open Matrix

variable {n : Nat}

private def commutator
    (X Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  X * Y - Y * X

/-- The coefficient forced by the raw exponential-adjoint expansion and the
printed Eq. (3.8) adjoint dictionary has the positive diagonal sign. -/
theorem rawDiagonal_eq_posSourceAdjoint
    (eta : ℂ) (heta : eta ≠ 0)
    (S Phi : Matrix (Fin n) (Fin n) ℂ) :
    let Dstar := (-(eta⁻¹)) • S
    let Ysum := (Complex.I * eta) • S
    (-(eta⁻¹)) • (eta⁻¹ • commutator Ysum Phi) =
      Complex.I • commutator Dstar Phi := by
  dsimp only
  unfold commutator
  simp only [smul_mul, mul_smul_comm, smul_sub, smul_smul]
  have hcancel : eta⁻¹ * eta = 1 := inv_mul_cancel₀ heta
  rw [mul_assoc, hcancel, mul_one]
  module

end Eq351DiagonalSignAlgebra
