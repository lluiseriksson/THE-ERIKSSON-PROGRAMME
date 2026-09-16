import YangMills.RG.BalabanCMP116Eq223PhysicalRootNormBridge

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

namespace PhysicalGaugeCMP116Dictionary

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

example
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A B : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc) :
    D.physicalRootMatrix (A.comp B) =
      D.physicalRootMatrix A * D.physicalRootMatrix B := by
  apply Matrix.mulVec_injective
  funext x
  apply funext
  intro i
  have h :
      WithLp.toLp 2 (D.physicalRootMatrix (A.comp B) *ᵥ x) =
        WithLp.toLp 2
          ((D.physicalRootMatrix A * D.physicalRootMatrix B) *ᵥ x) := by
    apply D.flatPhysicalLinearIsometryEquiv.injective
    change D.flatPhysicalLinearIsometryEquiv
        ((Matrix.toEuclideanCLM
          (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
            (D.physicalRootMatrix (A.comp B)) (WithLp.toLp 2 x)) =
      D.flatPhysicalLinearIsometryEquiv
        ((Matrix.toEuclideanCLM
          (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
            (D.physicalRootMatrix A * D.physicalRootMatrix B)
              (WithLp.toLp 2 x))
    rw [D.physicalRootMatrix_action]
    rw [map_mul]
    change (A.comp B) (D.flatPhysicalLinearIsometryEquiv
        (WithLp.toLp 2 x)) =
      D.flatPhysicalLinearIsometryEquiv
        ((Matrix.toEuclideanCLM
          (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
            (D.physicalRootMatrix A)
          ((Matrix.toEuclideanCLM
            (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
              (D.physicalRootMatrix B) (WithLp.toLp 2 x)))
    rw [D.physicalRootMatrix_action, D.physicalRootMatrix_action]
    rfl
  exact congrArg (fun y => y i) h

end PhysicalGaugeCMP116Dictionary
end YangMills.RG
