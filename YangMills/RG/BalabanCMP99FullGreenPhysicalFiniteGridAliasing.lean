/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99FullGreenFiniteGridAliasing
import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceMixedDomain

/-!
# Physical finite-grid aliasing for the full Eq. (2.46) Green

The centered full-G torus sample is replaced by the literal uncentered CMP99
coarse momentum in the complete two-endpoint finite-grid aliasing identity.
Both adjacent mixed Eq. (2.46) domains are constructed by the imported
transport theorem; no periodicity of a singular quotient is assumed.

This module does not identify the periodic solution with the generated
regional Green, prove CMP89 (2.42), produce uniform physical `B0` or
`delta0`, attain window 15, move `20/41`, or construct a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- **Literal full-G physical finite-grid aliasing.**  At zero mass and a
positive stabilizing coefficient, the normalized finite DFT is taken over
the actual uncentered CMP99 momentum samples.  The source and target remain
separate throughout. -/
theorem cmp99Flat_normalizedFiniteGridFullPhysicalGreenSample_eq_residueClass
    {K N : ℕ} [NeZero K] [NeZero N] {a rho : ℝ}
    (ha : 0 < a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (target source : Fin 4 → ℤ) (r : CMP99FlatZModBox 4 N) :
    ((N : ℂ) ^ 4)⁻¹ *
        ∑ k : CMP99FlatZModBox 4 N,
          cmp99FlatZModFourierCharacter (-k) r *
            cmp89Eq246PhysicalFineToFineGreenIntegrand K 1 0 a
              (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
                ((cmp99FinBoxZModEquiv 4 N).symm k))
              target source =
      ∑' n : CMP99FlatIntegerResidueClass 4 N r,
        cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
          K 1 0 a target source n := by
  have hmass0 : CMP89Eq251UniformMassWindow (0 : ℝ) := by
    unfold CMP89Eq251UniformMassWindow
    norm_num
  have halias :=
    cmp99Flat_normalizedFiniteGridFullGreen_eq_residueClass_massUniform
      (L := K) (j := 1) (N := N) (mass := 0) (a := a) (rho := rho)
      ha.le hrho hamplitude hradius hdenWindow hpairWindow hmass0
      target source r
  have hsample : ∀ k : CMP99FlatZModBox 4 N,
      cmp89Eq246CenteredFullGreenTorus
          (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
          ha.le hrho.le hamplitude hradius hdenWindow hpairWindow hmass0
          target source (cmp99FlatZModUnitTorusSample k) =
        cmp89Eq246PhysicalFineToFineGreenIntegrand K 1 0 a
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
            ((cmp99FinBoxZModEquiv 4 N).symm k))
          target source := by
    intro k
    let ell : FinBox 4 N := (cmp99FinBoxZModEquiv 4 N).symm k
    let t := cmp99SourceFlatQprimeCenteredUnitCubeRepresentative ell
    have hcover :=
      cmp89Eq246CenteredFullGreenTorus_covering_apply
        (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
        ha.le hrho.le hamplitude hradius hdenWindow hpairWindow hmass0
        target source t
    have htorus :=
      cmp89CenteredUnitCubeToTorus_centeredRepresentative_eq_sample ell
    rw [htorus] at hcover
    have hmom :
        (fun mu => (cmp89Eq248CenteredCubeMomentum t mu : ℂ)) =
          fun mu =>
            (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ) := by
      have hnegative :=
        cmp89Eq248NegativeTwoPiTorusMomentum_centeredRepresentative ell
      funext mu
      rw [← congrFun hnegative mu]
      simp only [t]
      unfold cmp89Eq248CenteredCubeMomentum
        cmp89Eq248NegativeTwoPiTorusMomentum
      push_cast
      ring
    rw [cmp89Eq246CenteredFullGreenCube, hmom] at hcover
    calc
      cmp89Eq246CenteredFullGreenTorus
          (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
          ha.le hrho.le hamplitude hradius hdenWindow hpairWindow hmass0
          target source (cmp99FlatZModUnitTorusSample k) =
          cmp89Eq246PhysicalFineToFineGreenIntegrand K 1 0 a
            (fun mu =>
              (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ))
            target source := by
        simpa [cmp99FlatZModUnitTorusSample, ell, t] using hcover
      _ = cmp89Eq246PhysicalFineToFineGreenIntegrand K 1 0 a
            (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
            target source :=
        cmp89Eq246PhysicalFineToFineGreenIntegrand_centered_eq_physical
          ha hrho.le hamplitude hradius hdenWindow hpairWindow
          target source ell
      _ = cmp89Eq246PhysicalFineToFineGreenIntegrand K 1 0 a
            (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
              ((cmp99FinBoxZModEquiv 4 N).symm k))
            target source := by rfl
  simpa only [hsample] using halias

end

end YangMills.RG
