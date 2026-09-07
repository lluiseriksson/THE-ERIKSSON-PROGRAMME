import YangMills.RG.NeumannPhysicalCoordinateGreenIntegral
import YangMills.RG.NeumannActualCommonBlockTranslation

/-!
# physical Green reflection at integer block boundaries
Cold compiler/audit verified at source 84ceb5f2 (2026-09-07).
Evidence and scope: VERIFICATION-LEDGER Addendum 1197; no terminal claim.
Both endpoints move together. Boundary B=0 is the lower half-cell reflection;
B equal to the regional block count gives the upper half-cell reflection.
The boundary uses fine integer units N*B, with N=L^j. No fine-translation
invariance, transposition, regional inverse, or Neumann seam is assumed.
-/

namespace YangMills.RG
noncomputable section

theorem neumannBlockBoundaryReflection_eq_center_shift
    {N : ℕ} (hN : 0 < N) (mu : Fin 4) (B : ℤ) (u : Fin 4 → ℤ) :
    (fun k => if k = mu then 2 * (N : ℤ) * B - 1 - u k else u k) =
      (fun k => neumannFineEndpointCoordinateReflection 4 N mu u k +
        (N : ℤ) * (if k = mu then 2 * B - 1 else 0)) := by
  have hc : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hN), Nat.cast_one]
  funext k
  by_cases h : k = mu
  · simp [neumannFineEndpointCoordinateReflection, h, hc] <;> ring
  · simp [neumannFineEndpointCoordinateReflection, h]

theorem neumannPhysicalGreen_blockBoundaryReflection_massUniform
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
      (fun k => if k = mu then 2 * ((L ^ j : ℕ) : ℤ) * B - 1 - source k else source k) =
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target source := by
  have hN : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  rw [neumannBlockBoundaryReflection_eq_center_shift hN mu B target,
    neumannBlockBoundaryReflection_eq_center_shift hN mu B source]
  rw [neumannActualNormalizedFineGreen_commonBlockShift]
  exact neumannPhysicalGreen_coordinateReflection_massUniform
    (L := L) (j := j) ha hrho hamplitude hradius hdenWindow hpairWindow
    hmass mu target source

theorem neumannPhysicalGreen_lowerHalfCellReflection_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (target source : Fin 4 → ℤ) :
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a
      (fun k => if k = mu then -target k - 1 else target k)
      (fun k => if k = mu then -source k - 1 else source k) =
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target source := by
  convert neumannPhysicalGreen_blockBoundaryReflection_massUniform
    (L := L) (j := j) ha hrho hamplitude hradius hdenWindow hpairWindow
    hmass mu 0 target source using 1 <;>
    congr 1 <;> funext k <;> split_ifs <;> ring


end
end YangMills.RG
