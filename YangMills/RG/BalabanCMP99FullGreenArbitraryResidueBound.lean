import YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenFourierSummability
import YangMills.RG.BalabanCMP99FlatIntegerResidueClassDictionary

/-!
# PRE-VALIDATION: full two-endpoint Green on an arbitrary residue class

Source is present; the `.olean` is not yet materialized and this result is
not yet verified by the compiler. The coefficient is constructed from the
literal full Green with a fixed source endpoint. Its displacement bound is
the sealed mass-uniform contour estimate. No translation-invariance or
caller-supplied coefficient family is assumed.

The full amplitude retains its scale and averaging-coefficient dependence.
This module does not produce uniform regional B0, attain window 15, move
20/41, or construct a TermSource.
-/

namespace YangMills.RG

noncomputable section

/-- Literal full zero-mass Green bound in the signed lattice weight, with
both endpoints retained. -/
theorem norm_cmp89Eq246PhysicalZeroMassGreen_le_signedLatticeWeight
    {K : ℕ} [NeZero K] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (target source : Fin 4 → ℤ) :
    ‖cmp89Eq246NormalizedPhysicalFineToFineGreen K 1 0 a target source‖ ≤
      cmp89Eq246DirectedFullSolutionSumBound K 1 a rho *
        cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
          (fun mu => target mu - source mu) := by
  have h := norm_cmp89Eq246NormalizedPhysicalFineToFineGreen_le_massUniform
    (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
    ha hrho hamplitude hradius hdenWindow hpairWindow
    (by norm_num [CMP89Eq251UniformMassWindow]) target source
  rw [cmp89Eq246PhysicalFineGreenDecay_eq_signedLatticeWeight_massUniform] at h
  simpa only [pow_one, mul_comm] using h

/-- The actual full-G amplitude is nonnegative on its existing analytic
window; no additional scalar premise is required. -/
theorem cmp89Eq246DirectedFullSolutionSumBound_nonneg_of_window
    {K : ℕ} [NeZero K] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho) :
    0 ≤ cmp89Eq246DirectedFullSolutionSumBound K 1 a rho := by
  have h := norm_cmp89Eq246PhysicalZeroMassGreen_le_signedLatticeWeight
    (K := K) ha hrho hamplitude hradius hdenWindow hpairWindow 0 0
  simpa [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs] using
    (le_trans (norm_nonneg _) h)

/-- Absolute residue mass for the literal full Green. Its base combines the
two endpoint displacements with the canonical selected residue before the
complete physical period is centered. -/
theorem tsum_norm_cmp89Eq246FullGreen_arbitraryResidue_le_centeredPeriodic
    {K N : ℕ} [NeZero K] [NeZero N] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (target source : Fin 4 → ℤ) (r : CMP99FlatZModBox 4 N) :
    (∑' n : CMP99FlatIntegerResidueClass 4 N r,
      ‖cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
        K 1 0 a target source n.1‖) ≤
      cmp89Eq246DirectedFullSolutionSumBound K 1 a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
            (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
              (fun mu => target mu - source mu +
                (K : ℤ) * cmp99FlatIntegerResidueRepresentative r mu))) := by
  let base : Fin 4 → ℤ := fun mu => target mu - source mu
  let coefficient : (Fin 4 → ℤ) → ℂ := fun v =>
    cmp89Eq246NormalizedPhysicalFineToFineGreen K 1 0 a (v + source) source
  have hA := cmp89Eq246DirectedFullSolutionSumBound_nonneg_of_window
    (K := K) ha hrho.le hamplitude hradius hdenWindow hpairWindow
  have hcoefficient : ∀ v,
      ‖coefficient v‖ ≤ cmp89Eq246DirectedFullSolutionSumBound K 1 a rho *
        cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ)) v := by
    intro v
    have h := norm_cmp89Eq246PhysicalZeroMassGreen_le_signedLatticeWeight
      (K := K) ha hrho.le hamplitude hradius hdenWindow hpairWindow
      (v + source) source
    simpa only [coefficient, Pi.add_apply, add_sub_cancel_right] using h
  have hsum := tsum_norm_cmp99FlatIntegerResidueClass_le_centeredPeriodic
    (K := K) (N := N) hrho hA coefficient hcoefficient r base
  have hterm : ∀ n : CMP99FlatIntegerResidueClass 4 N r,
      coefficient (fun mu => base mu + (K : ℤ) * n.1 mu) =
        cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
          K 1 0 a target source n.1 := by
    intro n
    dsimp only [coefficient, cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient,
      cmp89SignedLatticeResidueAffineMap, pow_one]
    congr 1
    funext mu
    simp only [Pi.add_apply, base, cmp89SignedLatticeResidueAffineMap]
    ring
  simpa only [hterm, base] using hsum

/-- Norm of the actual complex residue sum, using the already established
full-G summability before applying the triangle inequality. -/
theorem norm_tsum_cmp89Eq246FullGreen_arbitraryResidue_le_centeredPeriodic
    {K N : ℕ} [NeZero K] [NeZero N] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (target source : Fin 4 → ℤ) (r : CMP99FlatZModBox 4 N) :
    ‖∑' n : CMP99FlatIntegerResidueClass 4 N r,
      cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
        K 1 0 a target source n.1‖ ≤
      cmp89Eq246DirectedFullSolutionSumBound K 1 a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
            (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
              (fun mu => target mu - source mu +
                (K : ℤ) * cmp99FlatIntegerResidueRepresentative r mu))) := by
  have hfull := summable_cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient_massUniform
    (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
    ha hrho hamplitude hradius hdenWindow hpairWindow
    (by norm_num [CMP89Eq251UniformMassWindow]) target source
  have hnorm : Summable (fun n : CMP99FlatIntegerResidueClass 4 N r =>
      ‖cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
        K 1 0 a target source n.1‖) := hfull.norm.subtype _
  exact (norm_tsum_le_tsum_norm hnorm).trans
    (tsum_norm_cmp89Eq246FullGreen_arbitraryResidue_le_centeredPeriodic
      ha hrho hamplitude hradius hdenWindow hpairWindow target source r)

end

end YangMills.RG
