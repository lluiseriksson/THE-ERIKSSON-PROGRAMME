import YangMills.RG.NeumannPhysicalHalfCellReflection
import Mathlib.Tactic.Ring

/-!
# PRE-VALIDATION: move a physical boundary reflection between endpoints

Source present; .olean not materialized; result not compiler-verified.
Consumes the cold-sealed simultaneous physical covariance, not transposition
or a supplied Green law. This is pointwise transfer only; fixed-source image
reindexing, summability and the regional Green equation remain separate.
The boundary remains N*B in fine coordinates, with N=L^j and integer B.
-/

namespace YangMills.RG
noncomputable section

theorem neumannPhysicalGreen_blockBoundaryTransfer_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (B : ℤ) (target source : Fin 4 → ℤ) :
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a
      (fun k => if k = mu then 2 * ((L ^ j : ℕ) : ℤ) * B - 1 - target k else target k)
      source =
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
      (fun k => if k = mu then 2 * ((L ^ j : ℕ) : ℤ) * B - 1 - source k else source k) := by
  let R : (Fin 4 → ℤ) → (Fin 4 → ℤ) := fun y k =>
    if k = mu then 2 * ((L ^ j : ℕ) : ℤ) * B - 1 - y k else y k
  have hRR : ∀ y : Fin 4 → ℤ, R (R y) = y := by
    intro y
    funext k
    by_cases hk : k = mu
    · simp [R, hk]
    · simp [R, hk]
  have h := neumannPhysicalGreen_blockBoundaryReflection_massUniform
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hrho hamplitude hradius hdenWindow hpairWindow hmass mu B target (R source)
  change cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a
    (R target) (R (R source)) =
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target (R source) at h
  rw [hRR source] at h
  exact h

end
end YangMills.RG

#print axioms YangMills.RG.neumannPhysicalGreen_blockBoundaryTransfer_massUniform
