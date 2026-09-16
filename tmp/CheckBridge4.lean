import YangMills.RG.BalabanCMP99PhysicalRectangularMatrixReconstruction
namespace YangMills.RG
noncomputable section
example {d N₁ N₂ Nc : ℕ} [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)] (L : Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc) (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ →ₗ[ℝ] (PhysicalGaugeOneCochain d N₁ Nc →L[ℝ] PhysicalGaugeOneCochain d N₂ Nc)) : Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc) (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ →L[ℝ] (PhysicalGaugeOneCochain d N₁ Nc →L[ℝ] PhysicalGaugeOneCochain d N₂ Nc) := LinearMap.toContinuousLinearMap (𝕜 := ℝ) L
end
end YangMills.RG
