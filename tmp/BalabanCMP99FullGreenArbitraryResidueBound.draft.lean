import YangMills.RG.BalabanCMP99FlatIntegerResidueClassDictionary
import YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenFourierSummability

/-!
# PRE-VALIDATION: literal full-G bound on an arbitrary finite-grid residue class

This draft combines the mass-uniform full CMP89 (2.46) coefficient estimate
with the arbitrary-residue dictionary.  The selected sum is centered at the
full physical period `K*N`, with the canonical residue lift visible.  It does
not yet identify that centered base with literal fine endpoints or insert the
generated point-source identity.

No regional `B0`/`delta0`, CMP89 (2.42), window-15 attainment, terminal
field, counter movement or `TermSource` inhabitant is asserted.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Absolute mass of the literal full-G coefficients selected by an
arbitrary residue class. -/
theorem tsum_norm_cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient_residueClass_le
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
              (fun mu ↦ target mu - source mu + (K : ℤ) *
                cmp99FlatIntegerResidueRepresentative r mu))) := by
  let A := cmp89Eq246DirectedFullSolutionSumBound K 1 a rho
  let coefficient := fun v : Fin 4 → ℤ ↦
    cmp89Eq246NormalizedPhysicalFineToFineGreen K 1 0 a
      (fun mu ↦ v mu + source mu) source
  have hmass : CMP89Eq251UniformMassWindow (0 : ℝ) := by
    norm_num [CMP89Eq251UniformMassWindow]
  have hA : 0 ≤ A := by
    have hpoint :=
      norm_cmp89Eq246NormalizedPhysicalFineToFineGreen_le_massUniform
        (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
        ha hrho.le hamplitude hradius hdenWindow hpairWindow hmass
        (0 : Fin 4 → ℤ) 0
    have hnonneg := le_trans
      (norm_nonneg (cmp89Eq246NormalizedPhysicalFineToFineGreen
        K 1 0 a (0 : Fin 4 → ℤ) 0)) hpoint
    simpa [A, cmp89Eq249FineLatticeSpacing,
      cmp89Eq251LatticeL1Length] using hnonneg
  have hcoefficient : ∀ v,
      ‖coefficient v‖ ≤ A *
        cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ)) v := by
    intro v
    have hgreen :=
      norm_cmp89Eq246NormalizedPhysicalFineToFineGreen_le_massUniform
        (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
        ha hrho.le hamplitude hradius hdenWindow hpairWindow hmass
        (fun mu ↦ v mu + source mu) source
    rw [cmp89Eq246PhysicalFineGreenDecay_eq_signedLatticeWeight_massUniform]
      at hgreen
    simpa [coefficient, A] using hgreen
  have hbound :=
    tsum_norm_cmp99FlatIntegerResidueClass_le_centeredPeriodic
      (d := 4) (K := K) (N := N) hrho hA coefficient hcoefficient r
      (fun mu ↦ target mu - source mu)
  simpa [A, coefficient,
    cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient,
    cmp89SignedLatticeResidueAffineMap] using hbound

/-- Norm of the actual complex full-G coefficient sum selected by an
arbitrary finite-grid residue. -/
theorem norm_tsum_cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient_residueClass_le
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
              (fun mu ↦ target mu - source mu + (K : ℤ) *
                cmp99FlatIntegerResidueRepresentative r mu))) := by
  have hfull :=
    summable_cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient_massUniform
      (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow
      (by norm_num [CMP89Eq251UniformMassWindow]) target source
  have hnorm : Summable
      (fun n : CMP99FlatIntegerResidueClass 4 N r ↦
        ‖cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
          K 1 0 a target source n.1‖) := hfull.norm.subtype _
  exact (norm_tsum_le_tsum_norm hnorm).trans
    (tsum_norm_cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient_residueClass_le
      ha hrho hamplitude hradius hdenWindow hpairWindow target source r)

end

end YangMills.RG
