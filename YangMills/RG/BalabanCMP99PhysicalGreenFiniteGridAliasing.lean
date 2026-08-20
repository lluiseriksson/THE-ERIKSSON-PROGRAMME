/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Source-specific application of Step 8b.22 to the literal mass-uniform
stabilized Green.  Fourier reconstruction is derived from the actual torus
coefficients and their physical exponential bound; it is not accepted as a
family equality.  The finite grid is sampled with the positive torus point
and Step 8b.22 then selects the exact integer residue fibre.

The CMP99 centered-to-physical sample transport is consumed only in the
final source-specific theorem below.  No regional `B0`, window-15
attainment or terminal field is asserted here.
-/

import YangMills.RG.BalabanCMP99FlatFiniteGridAliasing
import YangMills.RG.BalabanCMP99CenteredTorusSampleDictionary
import YangMills.RG.BalabanCMP99CenteredTorusPhysicalGreenSampleTransport
import YangMills.RG.BalabanCMP89CenteredGreenFourierSummability

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- Positive unit-torus sample attached directly to a finite `ZMod` grid
point. -/
def cmp99FlatZModUnitTorusSample
    {d N : ℕ} [NeZero N] (k : CMP99FlatZModBox d N) :
    UnitAddTorus (Fin d) :=
  cmp99SourceFlatQprimeUnitTorusSample
    ((cmp99FinBoxZModEquiv d N).symm k)

/-- The positive torus monomial at the direct `ZMod` sample is exactly the
finite character used by Step 8b.22. -/
theorem cmp89UnitAddTorus_mFourier_flatZModSample_eq_character_draft
    {d N : ℕ} [NeZero N] (n : Fin d → ℤ)
    (k : CMP99FlatZModBox d N) :
    UnitAddTorus.mFourier n (cmp99FlatZModUnitTorusSample k) =
      cmp99FlatZModFourierCharacter k
        (cmp99FlatIntegerResidue (N := N) n) := by
  simpa [cmp99FlatZModUnitTorusSample] using
    (cmp89UnitAddTorus_mFourier_unitTorusSample_eq_flatCharacter n
      ((cmp99FinBoxZModEquiv d N).symm k))

/-- The generic Step-8b.22 Fourier-series sample of the literal physical
Green coefficients equals the actual descended Green at the finite torus
sample. -/
theorem cmp99FlatFiniteGridFourierSeriesSample_physicalGreen_eq_torusSample_draft
    {L j N : ℕ} [NeZero L] [NeZero N] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (u : Fin 4 → ℤ) (k : CMP99FlatZModBox 4 N) :
    cmp99FlatFiniteGridFourierSeriesSample
        (cmp89Eq248CenteredGreenPhysicalFourierCoefficient L j mass a u) k =
      cmp89Eq248CenteredGreenTorus
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho.le hamplitude hradius hwindow hmass u
        (cmp99FlatZModUnitTorusSample k) := by
  let f := cmp89Eq248CenteredGreenTorus
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hrho.le hamplitude hradius hwindow hmass u
  have hcoeff :=
    summable_mFourierCoeff_cmp89Eq248CenteredGreenTorus_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass u
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
            cmp89Eq248CenteredGreenPhysicalFourierCoefficient
              L j mass a u n) := by
    funext n
    dsimp [f]
    rw [cmp89_mFourierCoeff_centeredGreen_eq_physicalCoefficient_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho.le hamplitude hradius hwindow hmass u]
    rw [cmp89UnitAddTorus_mFourier_flatZModSample_eq_character_draft]
    simp only [smul_eq_mul]
    ring
  have hseries' : HasSum (fun n : Fin 4 → ℤ =>
      cmp99FlatZModFourierCharacter k
          (cmp99FlatIntegerResidue (N := N) n) *
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient L j mass a u n)
      (f (cmp99FlatZModUnitTorusSample k)) := by
    rw [← hterm]
    exact hseries
  simpa [cmp99FlatFiniteGridFourierSeriesSample, f] using hseries'.tsum_eq

/-- **Physical finite-grid aliasing.**  The normalized finite DFT of the
actual descended Green is the sum of the literal normalized physical Green
coefficients in the selected integer residue class. -/
theorem cmp99Flat_normalizedFiniteGridPhysicalGreen_eq_residueClass_draft
    {L j N : ℕ} [NeZero L] [NeZero N] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (u : Fin 4 → ℤ) (r : CMP99FlatZModBox 4 N) :
    ((N : ℂ) ^ 4)⁻¹ *
        ∑ k : CMP99FlatZModBox 4 N,
          cmp99FlatZModFourierCharacter (-k) r *
            cmp89Eq248CenteredGreenTorus
              (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
              ha hrho.le hamplitude hradius hwindow hmass u
              (cmp99FlatZModUnitTorusSample k) =
      ∑' n : CMP99FlatIntegerResidueClass 4 N r,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          L j mass a u n := by
  let coefficient :=
    cmp89Eq248CenteredGreenPhysicalFourierCoefficient L j mass a u
  have hsummable :=
    summable_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass u
  have halias :=
    cmp99Flat_normalizedFiniteGridFourierSeriesSample_eq_residueClass
      coefficient hsummable r
  have hsample : ∀ k : CMP99FlatZModBox 4 N,
      cmp99FlatFiniteGridFourierSeriesSample coefficient k =
        cmp89Eq248CenteredGreenTorus
          (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
          ha hrho.le hamplitude hradius hwindow hmass u
          (cmp99FlatZModUnitTorusSample k) := by
    intro k
    exact
      cmp99FlatFiniteGridFourierSeriesSample_physicalGreen_eq_torusSample_draft
        (L := L) (j := j) (N := N) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hwindow hmass u k
  simpa only [coefficient, hsample] using halias

/-- **Literal CMP99 physical finite-grid aliasing.**  At zero mass and a
positive physical stabilizing coefficient, the normalized DFT is now taken
over the actual uncentered CMP99 momentum samples.  The right-hand side is
still the literal normalized fine Green on the selected affine residue
class.  The centered torus has disappeared from the public conclusion. -/
theorem cmp99Flat_normalizedFiniteGridPhysicalGreenSample_eq_residueClass_draft
    {K N : ℕ} [NeZero K] [NeZero N] {a rho : ℝ}
    (ha : 0 < a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (u : Fin 4 → ℤ) (r : CMP99FlatZModBox 4 N) :
    ((N : ℂ) ^ 4)⁻¹ *
        ∑ k : CMP99FlatZModBox 4 N,
          cmp99FlatZModFourierCharacter (-k) r *
            cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 K 1 0 a
              (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
                ((cmp99FinBoxZModEquiv 4 N).symm k))
              (cmp89Eq249PhysicalFineLatticeDisplacement
                (((K ^ 1 : ℕ) : ℝ)⁻¹) u) =
      ∑' n : CMP99FlatIntegerResidueClass 4 N r,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          K 1 0 a u n := by
  have hmass0 : CMP89Eq251UniformMassWindow (0 : ℝ) := by
    unfold CMP89Eq251UniformMassWindow
    norm_num
  have halias :=
    cmp99Flat_normalizedFiniteGridPhysicalGreen_eq_residueClass_draft
      (L := K) (j := 1) (N := N) (mass := 0) (a := a) (rho := rho)
      ha.le hrho hamplitude hradius hwindow hmass0 u r
  have hsample : ∀ k : CMP99FlatZModBox 4 N,
      cmp89Eq248CenteredGreenTorus
          (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
          ha.le hrho.le hamplitude hradius hwindow hmass0 u
          (cmp99FlatZModUnitTorusSample k) =
        cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 K 1 0 a
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
            ((cmp99FinBoxZModEquiv 4 N).symm k))
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((K ^ 1 : ℕ) : ℝ)⁻¹) u) := by
    intro k
    simpa [cmp99FlatZModUnitTorusSample] using
      (cmp89Eq248CenteredGreenTorus_unitSample_eq_physical
        (K := K) (N' := N) ha hrho.le hamplitude hradius hwindow u
        ((cmp99FinBoxZModEquiv 4 N).symm k))
  simpa only [hsample] using halias

end

end YangMills.RG
