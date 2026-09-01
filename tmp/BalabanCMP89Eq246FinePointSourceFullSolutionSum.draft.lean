import YangMills.RG.BalabanCMP89Eq246FinePointSourceCentralComponentBound
import YangMills.RG.BalabanCMP89Eq246FinePointSourceNoncentralSolutionSum

/-!
# Draft: complete finite-fibre fine-point-source solution budget

This is the final finite-dimensional estimate below the Fourier synthesis.
It keeps the one physical volume loss visible: `O((L^j+1)^2)` from the
unsmoothed noncentral diagonal inverse.  The central branch and the rank-one
correction remain scale-uniform.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit budget for the complete finite alias-fibre solution. -/
def cmp89Eq246FinePointSourceFullSolutionSumBound
    (L j : ℕ) (a rho : ℝ) (sourceEndpoint : Fin 4 → ℝ) : ℝ :=
  cmp89Eq246FinePointSourceNoncentralSolutionSumBound
      L j a rho sourceEndpoint +
    cmp89Eq251ContourPhaseGrowth rho sourceEndpoint *
      cmp89Eq246FinePointSourceCentralComponentAmplitudeBound a rho

/-- The complete fine-point-source solution has the declared finite-volume
budget, before continuous Fourier synthesis. -/
theorem sum_norm_cmp89Eq246FinePointSourceFullSolution_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hstabilized : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpair : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (sourceEndpoint : Fin 4 → ℝ) :
    (∑ m : CMP89Eq246AliasIndex 4 L j,
      ‖cmp89Eq246StabilizedFinePointSourceSolution
        4 L j mass a z sourceEndpoint m‖) ≤
      cmp89Eq246FinePointSourceFullSolutionSumBound
        L j a rho sourceEndpoint := by
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let term : CMP89Eq246AliasIndex 4 L j → ℝ := fun m =>
    ‖cmp89Eq246StabilizedFinePointSourceSolution
      4 L j mass a z sourceEndpoint m‖
  have hsplit :
      (∑ m : CMP89Eq246AliasIndex 4 L j, term m) =
        (∑ m ∈ (Finset.univ :
          Finset (CMP89Eq246AliasIndex 4 L j)).erase central, term m) +
          term central := by
    exact (Finset.sum_erase_add Finset.univ term
      (Finset.mem_univ central)).symm
  have hnoncentral :=
    sum_norm_cmp89Eq246FinePointSourceNoncentralSolution_le
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hradius hmass hstabilized hamplitude hp hreal himag
      sourceEndpoint
  have hcentral :=
    norm_cmp89Eq246FinePointSourceCentralComponent_le
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hradius hmass hstabilized hpair hamplitude hp hreal himag
      sourceEndpoint
  rw [show (∑ m : CMP89Eq246AliasIndex 4 L j,
      ‖cmp89Eq246StabilizedFinePointSourceSolution
        4 L j mass a z sourceEndpoint m‖) = ∑ m, term m by rfl,
    hsplit]
  simpa [term, central, cmp89Eq246FinePointSourceFullSolutionSumBound] using
    add_le_add hnoncentral hcentral

end

end YangMills.RG
