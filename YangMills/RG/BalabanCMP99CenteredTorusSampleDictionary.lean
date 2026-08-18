/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

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

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

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
      constructor
      · rw [neg_div]
        have habsLower :
            -(N' : ℝ) / 2 ≤
              -(cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℝ) := by
          rw [neg_le_neg_iff]
          exact le_trans (le_abs_self _) (by linarith)
        exact (div_le_div_iff_of_pos_right hN).2 (by linarith)
      · rw [neg_div]
        have habsUpper :
            -(cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℝ) ≤
              (N' : ℝ) / 2 := by
          exact le_trans (le_abs_self _) (by linarith)
        exact (div_le_div_iff_of_pos_right hN).2 (by linarith)⟩

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
  apply Finset.prod_congr rfl
  intro mu _
  rw [fourier_coe_apply]
  change
    Complex.exp
        (2 * Real.pi * Complex.I * (n mu : ℂ) *
          (((ell mu).val : ℂ) / (N' : ℂ)) / 1) =
      ZMod.stdAddChar
        (((ell mu).val : ZMod N') * (n mu : ZMod N'))
  rw [show ((ell mu).val : ZMod N') * (n mu : ZMod N') =
      (((ell mu).val : ℤ) * n mu : ℤ) by push_cast; rfl,
    ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

end

end YangMills.RG
