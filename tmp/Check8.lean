import YangMills.RG.BalabanCMP99UbarUnitaryCovariance
import YangMills.RG.BalabanCMP116WilsonHessianUnitaryChart
namespace YangMills.RG
open Matrix
noncomputable section
variable {Nc : ℕ} [NeZero Nc]
example (u : UN Nc) (X : Matrix (Fin Nc) (Fin Nc) ℂ) :
    physicalMatrixExp ((u : Matrix (Fin Nc) (Fin Nc) ℂ) * X * Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ)) =
      (u : Matrix (Fin Nc) (Fin Nc) ℂ) * physicalMatrixExp X * Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) := by
  have hi : IsUnit (u : Matrix (Fin Nc) (Fin Nc) ℂ) := Unitary.isUnit_coe
  have hinv : (u : Matrix (Fin Nc) (Fin Nc) ℂ)⁻¹ =
      Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) := by
    have hdet : IsUnit (u : Matrix (Fin Nc) (Fin Nc) ℂ).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hi
    have hunit : (u : Matrix (Fin Nc) (Fin Nc) ℂ) *
        Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self u
    calc
      (u : Matrix (Fin Nc) (Fin Nc) ℂ)⁻¹ =
          (u : Matrix (Fin Nc) (Fin Nc) ℂ)⁻¹ * 1 := by rw [mul_one]
      _ = (u : Matrix (Fin Nc) (Fin Nc) ℂ)⁻¹ *
          ((u : Matrix (Fin Nc) (Fin Nc) ℂ) *
            Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ)) := by
              rw [hunit]
      _ = ((u : Matrix (Fin Nc) (Fin Nc) ℂ)⁻¹ *
            (u : Matrix (Fin Nc) (Fin Nc) ℂ)) *
          Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) := by
              rw [mul_assoc]
      _ = Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) := by
              rw [Matrix.nonsing_inv_mul _ hdet, one_mul]
  unfold physicalMatrixExp
  rw [← hinv]
  exact Matrix.exp_conj _ _ hi
end
end YangMills.RG
