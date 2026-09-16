import YangMills.RG.BalabanCMP116WilsonHessianUnitaryChart
namespace YangMills.RG
open Matrix
noncomputable section
variable {Nc : ℕ} [NeZero Nc]
example (u : UN Nc) :
    (u : Matrix (Fin Nc) (Fin Nc) ℂ)⁻¹ = Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) := by
  rw [← Units.val_inv_eq_inv_val (Unitary.toUnits u),
    Unitary.val_inv_toUnits_apply, ← Unitary.star_eq_inv, Unitary.coe_star]
  rfl
example (u : UN Nc) (X : Matrix (Fin Nc) (Fin Nc) ℂ) :
    physicalMatrixExp ((u : Matrix (Fin Nc) (Fin Nc) ℂ) * X * Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ)) =
      (u : Matrix (Fin Nc) (Fin Nc) ℂ) * physicalMatrixExp X * Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) := by
  have hi : IsUnit (u : Matrix (Fin Nc) (Fin Nc) ℂ) := Unitary.isUnit_coe
  have hinv : (u : Matrix (Fin Nc) (Fin Nc) ℂ)⁻¹ = Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) := by
    rw [← Units.val_inv_eq_inv_val (Unitary.toUnits u),
      Unitary.val_inv_toUnits_apply, ← Unitary.star_eq_inv, Unitary.coe_star]
    rfl
  unfold physicalMatrixExp
  rw [← hinv]
  exact Matrix.exp_conj _ _ hi
end
end YangMills.RG
