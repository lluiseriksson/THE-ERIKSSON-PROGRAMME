/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Absolute summability of the literal centered-torus Green coefficients.  The
coefficient is not synthetic: it is the normalized physical Green at the
positive affine residue `u + L^j*n`, identified with `mFourierCoeff` by the
G23.4 dictionary.  The majorant uses the exact signed `l1` product sum and
therefore introduces no spurious `(L^j)^4` volume factor.

No finite-grid sample identity, regional `B0`, window-15 attainment or
terminal field is asserted here.
-/

import YangMills.RG.BalabanCMP89SignedLatticeL1TotalSum
import YangMills.RG.BalabanCMP89Eq248MassUniformNormalizedGreenBound
import YangMills.RG.BalabanCMP89CenteredTorusGreenCoefficientDictionary

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- Literal physical Green coefficient in the affine residue fibre based at
`u` and lattice scale `L^j`. -/
def cmp89Eq248CenteredGreenPhysicalFourierCoefficient
    (L j : ℕ) [NeZero L] (mass a : ℝ) (u n : Fin 4 → ℤ) : ℂ :=
  cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen L j mass a
    (cmp89SignedLatticeResidueAffineMap (L ^ j) u n)

/-- The contour decay in the physical normalized Green is exactly the
signed-lattice weight at fine rate `rho/(L^j)`. -/
theorem cmp89Eq248PhysicalFineGreenDecay_eq_signedLatticeWeight_draft
    {L j : ℕ} [NeZero L] (rho : ℝ) (v : Fin 4 → ℤ) :
    Real.exp (-(rho * cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) v))) =
      cmp89SignedLatticeL1ExponentialWeight
        (rho / ((L ^ j : ℕ) : ℝ)) v := by
  have hLj : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hxi : 0 ≤ (((L ^ j : ℕ) : ℝ)⁻¹) := by positivity
  rw [cmp89Eq251DisplacementL1_physicalFineLatticeDisplacement hxi,
    cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
  unfold cmp89Eq251LatticeL1Length
  congr 1
  have hLjR : (((L ^ j : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast hLj.ne'
  field_simp [hLjR]
  ring

/-- The literal physical affine-residue Green coefficients are absolutely
summable at every positive common radius. -/
theorem summable_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (u : Fin 4 → ℤ) :
    Summable
      (cmp89Eq248CenteredGreenPhysicalFourierCoefficient L j mass a u) := by
  let M : ℕ := L ^ j
  let amplitude : ℝ :=
    cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho
  have hM : 0 < M := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hweight :=
    summable_cmp89SignedLatticeL1ExponentialWeight_physicalResidue
      (d := 4) hM hrho u
  have hmajor := hweight.mul_right amplitude
  apply Summable.of_norm_bounded hmajor
  intro n
  have hgreen :=
    norm_cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen_le_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho.le hamplitude hradius hwindow hmass
      (cmp89SignedLatticeResidueAffineMap M u n)
  simpa [cmp89Eq248CenteredGreenPhysicalFourierCoefficient, M, amplitude,
    cmp89Eq248PhysicalFineGreenDecay_eq_signedLatticeWeight_draft]
    using hgreen

/-- The Mathlib torus coefficient is definitionally the literal physical
affine-residue coefficient after consuming the G23.4 dictionary. -/
theorem cmp89_mFourierCoeff_centeredGreen_eq_physicalCoefficient_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (u n : Fin 4 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (cmp89Eq248CenteredGreenTorus
          (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
          ha hrho hamplitude hradius hwindow hmass u) n =
      cmp89Eq248CenteredGreenPhysicalFourierCoefficient
        L j mass a u n := by
  simpa [cmp89Eq248CenteredGreenPhysicalFourierCoefficient,
    cmp89SignedLatticeResidueAffineMap] using
    (cmp89_mFourierCoeff_centeredGreen_eq_normalizedFineGreen
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass u n)

/-- Consequently the actual Fourier coefficients of the literal descended
Green are summable; no coefficient family is supplied by the caller. -/
theorem summable_mFourierCoeff_cmp89Eq248CenteredGreenTorus_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (u : Fin 4 → ℤ) :
    Summable (UnitAddTorus.mFourierCoeff
      (cmp89Eq248CenteredGreenTorus
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho.le hamplitude hradius hwindow hmass u)) := by
  have hphysical :=
    summable_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass u
  simpa only [cmp89_mFourierCoeff_centeredGreen_eq_physicalCoefficient_draft
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hrho.le hamplitude hradius hwindow hmass u] using hphysical

end

end YangMills.RG
