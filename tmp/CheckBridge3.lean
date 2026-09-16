import YangMills.RG.BalabanCMP99PhysicalRectangularMatrixReconstruction
namespace YangMills.RG
example {d N₁ N₂ Nc : ℕ} [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)] : Module ℝ (Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc) (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ) := inferInstance
#check LinearMap.map_add
#check LinearMap.map_smul
end YangMills.RG
