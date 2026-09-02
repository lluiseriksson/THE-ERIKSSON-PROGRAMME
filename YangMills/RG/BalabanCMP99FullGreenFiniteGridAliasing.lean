import YangMills.RG.BalabanCMP99FlatFiniteGridAliasing
import YangMills.RG.BalabanCMP99PhysicalGreenFiniteGridAliasing
import YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenFourierSummability

/-!
# PRE-VALIDATION: finite-grid aliasing for the literal full CMP89 (2.46) Green

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

The generic finite-grid Fourier identity is instantiated with the actual
two-endpoint full-G torus coefficients.  Fourier reconstruction comes from
their proved absolute summability and the coefficient dictionary; it is not
accepted as a family equality.  The exact residue sum moves only the target
endpoint, while the source endpoint remains fixed.

This module does not yet identify the torus sample with the generated CMP99
regional Green or perform the reflection/carry reindexing required by that
consumer.  It does not produce `B0`, `delta0`, attain window 15, discharge a
terminal field or inhabit `TermSource`.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The generic finite-grid Fourier-series sample of the literal full-G
coefficients equals the actual descended two-endpoint Green at the finite
torus sample. -/
theorem cmp99FlatFiniteGridFourierSeriesSample_fullGreen_eq_torusSample_massUniform
    {L j N : ℕ} [NeZero L] [NeZero N] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) (k : CMP99FlatZModBox 4 N) :
    cmp99FlatFiniteGridFourierSeriesSample
        (cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
          L j mass a target source) k =
      cmp89Eq246CenteredFullGreenTorus
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho.le hamplitude hradius hdenWindow hpairWindow hmass
        target source (cmp99FlatZModUnitTorusSample k) := by
  let f := cmp89Eq246CenteredFullGreenTorus
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hrho.le hamplitude hradius hdenWindow hpairWindow hmass target source
  have hcoeff :=
    summable_mFourierCoeff_cmp89Eq246CenteredFullGreenTorus_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass target source
  have hseries :=
    UnitAddTorus.hasSum_mFourier_series_apply_of_summable hcoeff
      (cmp99FlatZModUnitTorusSample k)
  have hterm :
      (fun n : Fin 4 → ℤ =>
        UnitAddTorus.mFourierCoeff f n •
          UnitAddTorus.mFourier n (cmp99FlatZModUnitTorusSample k)) =
        (fun n : Fin 4 → ℤ =>
          cmp99FlatZModFourierCharacter k
              (cmp99FlatIntegerResidue (N := N) n) *
            cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
              L j mass a target source n) := by
    funext n
    dsimp [f]
    rw [cmp89_mFourierCoeff_centeredFullGreen_eq_normalizedFineToFineGreen_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho.le hamplitude hradius hdenWindow hpairWindow hmass
      target source n]
    rw [cmp89UnitAddTorus_mFourier_flatZModSample_eq_character_draft]
    ring
  have hseries' : HasSum (fun n : Fin 4 → ℤ =>
      cmp99FlatZModFourierCharacter k
          (cmp99FlatIntegerResidue (N := N) n) *
        cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
          L j mass a target source n)
      (f (cmp99FlatZModUnitTorusSample k)) := by
    rw [← hterm]
    exact hseries
  simpa [cmp99FlatFiniteGridFourierSeriesSample, f] using hseries'.tsum_eq

/-- **Full-G finite-grid aliasing.**  The normalized finite DFT of the
actual descended two-endpoint Green is the sum of the literal normalized
full-G coefficients in the selected integer residue class. -/
theorem cmp99Flat_normalizedFiniteGridFullGreen_eq_residueClass_massUniform
    {L j N : ℕ} [NeZero L] [NeZero N] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) (r : CMP99FlatZModBox 4 N) :
    ((N : ℂ) ^ 4)⁻¹ *
        ∑ k : CMP99FlatZModBox 4 N,
          cmp99FlatZModFourierCharacter (-k) r *
            cmp89Eq246CenteredFullGreenTorus
              (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
              ha hrho.le hamplitude hradius hdenWindow hpairWindow hmass
              target source (cmp99FlatZModUnitTorusSample k) =
      ∑' n : CMP99FlatIntegerResidueClass 4 N r,
        cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
          L j mass a target source n := by
  let coefficient :=
    cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
      L j mass a target source
  have hsummable :=
    summable_cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass target source
  have halias :=
    cmp99Flat_normalizedFiniteGridFourierSeriesSample_eq_residueClass
      coefficient hsummable r
  have hsample : ∀ k : CMP99FlatZModBox 4 N,
      cmp99FlatFiniteGridFourierSeriesSample coefficient k =
        cmp89Eq246CenteredFullGreenTorus
          (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
          ha hrho.le hamplitude hradius hdenWindow hpairWindow hmass
          target source (cmp99FlatZModUnitTorusSample k) := by
    intro k
    exact
      cmp99FlatFiniteGridFourierSeriesSample_fullGreen_eq_torusSample_massUniform
        (L := L) (j := j) (N := N) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hdenWindow hpairWindow hmass
        target source k
  simpa only [coefficient, hsample] using halias

end

end YangMills.RG
