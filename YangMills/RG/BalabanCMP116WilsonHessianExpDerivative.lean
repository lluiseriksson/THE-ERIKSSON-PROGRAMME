import Mathlib
import YangMills.RG.BalabanCMP116WilsonHessianDifferential

/-!
# The noncommutative second derivative of the matrix exponential

This WIL-H3 module evaluates the second real Fréchet derivative of the
matrix exponential at zero.  The diagonal identity is extracted directly
from Mathlib's Banach-algebra exponential power series.  Polarization and
symmetry then give the full noncommutative formula

`D² exp(0)[X,Y] = (XY + YX) / 2`.

No commutativity assumption on the matrix algebra is used.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Nc : ℕ}

/-- On the diagonal, the second real Fréchet derivative of the matrix
exponential at zero is the square of the direction. -/
theorem physicalMatrixExp_sndFDeriv_zero_apply_self
    (X : Matrix (Fin Nc) (Fin Nc) ℂ) :
    fderiv ℝ (fderiv ℝ (physicalMatrixExp (Nc := Nc))) 0 X X = X * X := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  have h := (NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos
    (NormedSpace.expSeries_radius_pos ℝ
      (Matrix (Fin Nc) (Fin Nc) ℂ))).factorial_smul X 2
  rw [iteratedFDeriv_two_apply] at h
  calc
    fderiv ℝ (fderiv ℝ (physicalMatrixExp (Nc := Nc))) 0 X X =
        (2 : ℕ) • ((NormedSpace.expSeries ℝ
          (Matrix (Fin Nc) (Fin Nc) ℂ) 2) (fun _ => X)) := by
          simpa [physicalMatrixExp] using h.symm
    _ = X * X := by
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      rw [NormedSpace.expSeries_apply_eq]
      norm_num [pow_two]
      module

/-- The full noncommutative second derivative of the matrix exponential at
zero is the symmetrized matrix product. -/
theorem physicalMatrixExp_sndFDeriv_zero_apply
    (X Y : Matrix (Fin Nc) (Fin Nc) ℂ) :
    fderiv ℝ (fderiv ℝ (physicalMatrixExp (Nc := Nc))) 0 X Y =
      (1 / 2 : ℝ) • (X * Y + Y * X) := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  let B := fderiv ℝ (fderiv ℝ (physicalMatrixExp (Nc := Nc))) 0
  have hdiag (Z : Matrix (Fin Nc) (Fin Nc) ℂ) : B Z Z = Z * Z := by
    simpa [B] using physicalMatrixExp_sndFDeriv_zero_apply_self Z
  have hpos := NormedSpace.expSeries_radius_pos ℝ
    (Matrix (Fin Nc) (Fin Nc) ℂ)
  have hanalytic : AnalyticAt ℝ (physicalMatrixExp (Nc := Nc)) 0 :=
    (NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos hpos).analyticAt_of_mem
      (Metric.mem_eball_self hpos)
  have hc : ContDiffAt ℝ (2 : WithTop ℕ∞)
      (physicalMatrixExp (Nc := Nc)) 0 := hanalytic.contDiffAt
  have hs : IsSymmSndFDerivAt ℝ (physicalMatrixExp (Nc := Nc)) 0 :=
    hc.isSymmSndFDerivAt (by norm_num [minSmoothness])
  have hsym : B Y X = B X Y := hs.eq Y X
  have hsum := hdiag (X + Y)
  have hx := hdiag X
  have hy := hdiag Y
  dsimp [B] at hsym hsum hx hy ⊢
  simp only [map_add, ContinuousLinearMap.add_apply, add_mul, mul_add] at hsum
  rw [hx, hy, hsym] at hsum
  have htwo :
      (fderiv ℝ (fderiv ℝ (physicalMatrixExp (Nc := Nc))) 0 X Y) +
        (fderiv ℝ (fderiv ℝ (physicalMatrixExp (Nc := Nc))) 0 X Y) =
          X * Y + Y * X := by
    calc
      _ = -(X * X) +
          ((X * X + fderiv ℝ
              (fderiv ℝ (physicalMatrixExp (Nc := Nc))) 0 X Y) +
            (fderiv ℝ (fderiv ℝ (physicalMatrixExp (Nc := Nc))) 0 X Y +
              Y * Y)) - Y * Y := by abel
      _ = -(X * X) + (X * X + Y * X + (X * Y + Y * Y)) - Y * Y := by
        rw [hsum]
      _ = X * Y + Y * X := by abel
  rw [← htwo]
  module

end

end YangMills.RG
