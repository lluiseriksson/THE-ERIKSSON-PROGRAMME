import YangMills.RG.BalabanCMP89SignedLatticeL1TotalSum
import YangMills.RG.BalabanCMP89Eq246MassUniformPhysicalContour
import YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenCoefficientDictionary

/-!
# Absolute summability of full CMP89 (2.46) torus coefficients

The coefficient is the literal normalized two-endpoint Green with only the
target moving in the affine residue fibre.  Its mass-uniform full-G contour
bound is summed with the exact signed `l1` product majorant, so no spurious
`(L^j)^4` fine-volume factor is introduced.

No arbitrary coefficient family, finite-grid periodization, generated
regional Green identification, `B0`, `delta0`, window-15 attainment,
terminal field or `TermSource` inhabitant is accepted or asserted.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Literal full-G Fourier coefficient on the affine target residue fibre;
the source endpoint is fixed. -/
def cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (target source n : Fin 4 → ℤ) : ℂ :=
  cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a
    (cmp89SignedLatticeResidueAffineMap (L ^ j) target n) source

/-- The target-source displacement of one affine target residue is itself
the affine residue based at the literal target-source difference. -/
theorem cmp89Eq246_affineTarget_sub_source
    (M : ℕ) (target source n : Fin 4 → ℤ) :
    (fun mu =>
        cmp89SignedLatticeResidueAffineMap M target n mu - source mu) =
      cmp89SignedLatticeResidueAffineMap M
        (fun mu => target mu - source mu) n := by
  funext mu
  simp [cmp89SignedLatticeResidueAffineMap]
  ring

/-- The fine-lattice decay factor in the literal full-G estimate is exactly
the signed-lattice exponential weight at rate `rho / L^j`. -/
theorem cmp89Eq246PhysicalFineGreenDecay_eq_signedLatticeWeight_massUniform
    {L j : ℕ} [NeZero L] (rho : ℝ) (v : Fin 4 → ℤ) :
    Real.exp (-((rho * cmp89Eq249FineLatticeSpacing L j) *
        cmp89Eq251LatticeL1Length v)) =
      cmp89SignedLatticeL1ExponentialWeight
        (rho / ((L ^ j : ℕ) : ℝ)) v := by
  rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
  simp [cmp89Eq249FineLatticeSpacing, cmp89Eq251LatticeL1Length,
    div_eq_mul_inv, mul_assoc]

/-- The literal full-G affine-target coefficients are absolutely summable
at every positive common contour radius, including at physical mass zero. -/
theorem summable_cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    Summable
      (cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
        L j mass a target source) := by
  let M : ℕ := L ^ j
  let base : Fin 4 → ℤ := fun mu => target mu - source mu
  let amplitude : ℝ := cmp89Eq246DirectedFullSolutionSumBound L j a rho
  have hM : 0 < M := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hweight :=
    summable_cmp89SignedLatticeL1ExponentialWeight_physicalResidue
      (d := 4) hM hrho base
  have hmajor := hweight.mul_right amplitude
  apply Summable.of_norm_bounded hmajor
  intro n
  have hgreen :=
    norm_cmp89Eq246NormalizedPhysicalFineToFineGreen_le_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho.le hamplitude hradius hdenWindow hpairWindow hmass
      (cmp89SignedLatticeResidueAffineMap M target n) source
  rw [cmp89Eq246_affineTarget_sub_source M target source n] at hgreen
  rw [cmp89Eq246PhysicalFineGreenDecay_eq_signedLatticeWeight_massUniform]
    at hgreen
  simpa [cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient,
    M, base, amplitude] using hgreen

/-- The actual torus coefficients of the literal full Green are summable;
the coefficient dictionary is consumed rather than supplied by the caller. -/
theorem summable_mFourierCoeff_cmp89Eq246CenteredFullGreenTorus_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    Summable (UnitAddTorus.mFourierCoeff
      (cmp89Eq246CenteredFullGreenTorus
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho.le hamplitude hradius hdenWindow hpairWindow hmass
        target source)) := by
  have hphysical :=
    summable_cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass target source
  apply hphysical.congr
  intro n
  exact
    (cmp89_mFourierCoeff_centeredFullGreen_eq_normalizedFineToFineGreen_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho.le hamplitude hradius hdenWindow hpairWindow hmass
      target source n).symm

end

end YangMills.RG
