/-
SEALED SOURCE-SPECIFIC BRICK -- COMPILER-VERIFIED.

This scratch file isolates the sign-sensitive sample dictionary below
Step 8b.23.  It intentionally imports the future promoted centered-cube
quotient module, which does not yet exist in the tracked tree.

No Green periodicity, Fourier coefficient, `B0`, window-15 attainment or
terminal field is asserted here.
-/

import YangMills.RG.BalabanCMP89CenteredUnitCubeTorusQuotient
import YangMills.RG.BalabanCMP89CenteredTorusFourierPhase
import YangMills.RG.BalabanCMP99SourceFlatQprimeCenteredCoarseMomentum
import YangMills.RG.BalabanCMP99FlatFiniteGridAliasing
import YangMills.RG.BalabanCMP99FlatFinBoxDFT


namespace YangMills.RG

noncomputable section

/-- Positive finite torus sample represented by the literal nonnegative
coarse Fourier coordinate `ell/N'`. -/
def cmp99SourceFlatQprimeUnitTorusSample
    {d N' : ℕ} [NeZero N'] (ell : FinBox d N') :
    UnitAddTorus (Fin d) :=
  fun mu => ((((ell mu).val : ℝ) / (N' : ℝ) : ℝ) : UnitAddCircle)

/-- The centered cube representative of the positive torus sample.  The
minus sign is porting: the existing centered alias represents `-ell mod N'`.
-/
def cmp99SourceFlatQprimeCenteredUnitCubeRepresentative
    {d N' : ℕ} [NeZero N'] (ell : FinBox d N') :
    CMP89CenteredUnitCube (Fin d) :=
  fun mu =>
    ⟨-((cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℝ) /
        (N' : ℝ)), by
      have hN : 0 < (N' : ℝ) := Nat.cast_pos.mpr (NeZero.pos N')
      have hbound :
          2 * |(cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℝ)| ≤
            (N' : ℝ) := by
        exact_mod_cast
          two_mul_abs_cmp99SourceFlatQprimeCenteredCoarseAlias_le ell mu
      have habsDiv :
          |(cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℝ) /
              (N' : ℝ)| ≤ 1 / 2 := by
        rw [abs_div, abs_of_pos hN]
        exact (div_le_iff₀ hN).2 (by linarith)
      exact (abs_le.mp (by simpa using habsDiv))⟩

/-- The centered representative really covers the positive sample
`ell/N'`.  This is the discrete sign gate; replacing the representative by
`+a_ell/N'` would cover the Fourier-negated mode. -/
theorem cmp89CenteredUnitCubeToTorus_centeredRepresentative_eq_sample
    {d N' : ℕ} [NeZero N'] (ell : FinBox d N') :
    cmp89CenteredUnitCubeToTorus
        (cmp99SourceFlatQprimeCenteredUnitCubeRepresentative ell) =
      cmp99SourceFlatQprimeUnitTorusSample ell := by
  funext mu
  change
    (((-((cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℝ) /
        (N' : ℝ)) : ℝ) : UnitAddCircle)) =
      ((((ell mu).val : ℝ) / (N' : ℝ) : ℝ) : UnitAddCircle)
  have hdiv : (N' : ℤ) ∣
      cmp99SourceFlatQprimeCenteredCoarseAlias ell mu +
        ((ell mu).val : ℤ) :=
    cmp99SourceFlatQprimeSignedCenteredAlias_add_quotient_dvd N' (ell mu)
  rcases hdiv with ⟨c, hc⟩
  have hN : (N' : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (NeZero.pos N'))
  have hcR := congrArg (fun x : ℤ => (x : ℝ)) hc
  push_cast at hcR
  have hdiff :
      -((cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℝ) /
          (N' : ℝ)) -
        (((ell mu).val : ℝ) / (N' : ℝ)) = -(c : ℝ) := by
    field_simp [hN]
    linarith
  have hzero :
      (((-((cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℝ) /
          (N' : ℝ)) -
        (((ell mu).val : ℝ) / (N' : ℝ)) : ℝ) : UnitAddCircle)) = 0 := by
    rw [hdiff]
    exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2
      ⟨-c, by simp⟩
  rw [← sub_eq_zero, ← AddCircle.coe_sub]
  exact hzero

/-- Under `p(t) = -2*pi*t`, the centered torus representative becomes the
already sealed centered physical coarse base momentum. -/
theorem cmp89Eq248NegativeTwoPiTorusMomentum_centeredRepresentative
    {d N' : ℕ} [NeZero N'] (ell : FinBox d N') :
    cmp89Eq248NegativeTwoPiTorusMomentum
        (fun mu =>
          (cmp99SourceFlatQprimeCenteredUnitCubeRepresentative ell mu).1) =
      fun mu =>
        (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ) := by
  funext mu
  unfold cmp89Eq248NegativeTwoPiTorusMomentum
    cmp99SourceFlatQprimeCenteredUnitCubeRepresentative
    cmp99SourceFlatQprimeCenteredCoarseBaseMomentum
  push_cast
  ring

/-- Sampling Mathlib's positive torus monomial at `ell/N'` gives exactly
the positive finite `ZMod` character used by Step 8b.22.  This is the second
sign gate between the continuous and finite Fourier conventions. -/
theorem cmp89UnitAddTorus_mFourier_unitTorusSample_eq_flatCharacter
    {d N' : ℕ} [NeZero N'] (n : Fin d → ℤ) (ell : FinBox d N') :
    UnitAddTorus.mFourier n
        (cmp99SourceFlatQprimeUnitTorusSample ell) =
      cmp99FlatZModFourierCharacter
        (cmp99FinBoxZModEquiv d N' ell)
        (cmp99FlatIntegerResidue (N := N') n) := by
  unfold UnitAddTorus.mFourier cmp99FlatZModFourierCharacter
    cmp99SourceFlatQprimeUnitTorusSample cmp99FlatIntegerResidue
  change (∏ mu, fourier (n mu)
      (((((ell mu).val : ℝ) / (N' : ℝ) : ℝ) : UnitAddCircle))) =
    ∏ mu, ZMod.stdAddChar
      ((cmp99FinBoxZModEquiv d N') ell mu * (n mu : ZMod N'))
  apply Finset.prod_congr rfl
  intro mu _
  simp only [cmp99FinBoxZModEquiv_apply]
  rw [fourier_coe_apply]
  push_cast
  rw [show ((ell mu).val : ZMod N') * (n mu : ZMod N') =
      (((ell mu).val : ℤ) * n mu : ℤ) by push_cast; rfl,
    ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

end

end YangMills.RG
