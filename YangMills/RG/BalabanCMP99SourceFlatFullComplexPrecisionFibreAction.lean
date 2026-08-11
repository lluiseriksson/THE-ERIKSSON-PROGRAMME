/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionModeAction

/-!
# Full-box flat complex precision on one reciprocal fibre

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

The mode-column identity is lifted to an arbitrary coefficient vector on one
fixed physical reciprocal fibre.  The coefficients are extended by zero to
the literal full momentum box and reconstructed by the already sealed
physical-fibre inverse DFT.  The unnormalized forward-transform volume factor
therefore cancels the inverse-transform normalization internally.

The resulting forward transform of the literal full-box precision is the
transpose of the sealed physical alias precision matrix applied entrywise to
the Lie-fibre coefficients.  No synthetic Fourier operator and no abstract
self-adjointness argument is introduced.

Honest scope: this is a finite fixed-fibre action identity on the flat full
periodic box.  It does not construct a Green operator, prove nonsingularity,
stabilize the central removable zero, or transport the result to an
interacting or regional precision.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Extend coefficients on one fixed coarse reciprocal fibre by zero to the
literal full fine-momentum box. -/
def cmp99SourceFlatFixedCoarseFibreCoefficientExtension
    (ell : FinBox d N')
    (coeff : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc)
    (k : FinBox d (M * N')) : SUNLieComplexCoord Nc :=
  if hk : cmp99SourceFlatQprimeCoarseAlias k = ell then
    coeff ⟨k, hk⟩
  else
    0

omit [NeZero d] [NeZero Nc] in
@[simp] theorem cmp99SourceFlatFixedCoarseFibreCoefficientExtension_apply
    (ell : FinBox d N')
    (coeff : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc)
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99SourceFlatFixedCoarseFibreCoefficientExtension ell coeff k.1 =
      coeff k := by
  simp [cmp99SourceFlatFixedCoarseFibreCoefficientExtension, k.2]

/-- Literal inverse-DFT reconstruction of a coefficient vector supported on
one fixed coarse reciprocal fibre. -/
def cmp99SourceFlatFixedCoarseFibreFourierSynthesis
    (ell : FinBox d N')
    (coeff : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc) :
    FinBox d (M * N') → SUNLieComplexCoord Nc :=
  cmp99FlatPhysicalFibreInvDFT
    (cmp99SourceFlatFixedCoarseFibreCoefficientExtension ell coeff)

omit [NeZero d] [NeZero Nc] in
/-- The literal DFT recovers every coefficient on the selected fibre. -/
theorem cmp99FlatPhysicalFibreDFT_fixedCoarseFibreFourierSynthesis
    (ell : FinBox d N')
    (coeff : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc)
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFixedCoarseFibreFourierSynthesis ell coeff) k.1 =
      coeff k := by
  rw [cmp99SourceFlatFixedCoarseFibreFourierSynthesis,
    cmp99FlatPhysicalFibreDFT_InvDFT]
  exact cmp99SourceFlatFixedCoarseFibreCoefficientExtension_apply ell coeff k

/-- The inverse-DFT synthesis is the finite sum of physical Fourier modes
with the literal inverse volume normalization. -/
theorem cmp99SourceFlatFixedCoarseFibreFourierSynthesis_eq_sum
    (ell : FinBox d N')
    (coeff : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc) :
    cmp99SourceFlatFixedCoarseFibreFourierSynthesis ell coeff =
      fun x => ∑ k,
        cmp99FlatComplexFibreFourierMode k.1
          (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) • coeff k) x := by
  apply (cmp99FlatPhysicalFibreDFTLinearEquiv
    (d := d) (N := M * N') (Nc := Nc)).injective
  rw [cmp99SourceFlatFixedCoarseFibreFourierSynthesis]
  change (cmp99FlatPhysicalFibreDFTLinearEquiv
      (d := d) (N := M * N') (Nc := Nc))
        ((cmp99FlatPhysicalFibreDFTLinearEquiv
          (d := d) (N := M * N') (Nc := Nc)).symm
            (cmp99SourceFlatFixedCoarseFibreCoefficientExtension ell coeff)) =
    (cmp99FlatPhysicalFibreDFTLinearEquiv
      (d := d) (N := M * N') (Nc := Nc)) (fun x =>
      ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99FlatComplexFibreFourierMode k.1
          (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) • coeff k) x)
  rw [LinearEquiv.apply_symm_apply]
  have hsum : (fun x =>
      ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99FlatComplexFibreFourierMode k.1
          (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) • coeff k) x) =
      ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99FlatComplexFibreFourierMode k.1
          (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) • coeff k) := by
    funext x
    rw [Finset.sum_apply]
  rw [hsum, map_sum]
  funext l
  rw [Finset.sum_apply]
  by_cases hl : cmp99SourceFlatQprimeCoarseAlias l = ell
  · let k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell := ⟨l, hl⟩
    rw [show cmp99SourceFlatFixedCoarseFibreCoefficientExtension ell coeff l =
        coeff k by
      simp [cmp99SourceFlatFixedCoarseFibreCoefficientExtension, hl, k]]
    rw [Finset.sum_eq_single k]
    · change coeff k = cmp99FlatPhysicalFibreDFT
          (cmp99FlatComplexFibreFourierMode k.1
            (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) • coeff k)) l
      rw [cmp99FlatPhysicalFibreDFT_fourierMode]
      simp only [k, if_true]
      have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
      have hN : (N' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N')
      rw [Nat.cast_mul, mul_pow]
      field_simp [hM, hN]
    · intro b _ hb
      change cmp99FlatPhysicalFibreDFT
          (cmp99FlatComplexFibreFourierMode b.1
            (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) • coeff b)) l = 0
      rw [cmp99FlatPhysicalFibreDFT_fourierMode]
      have hval : b.1 ≠ l := by
        intro hbl
        apply hb
        exact Subtype.ext hbl
      rw [if_neg hval]
      simp
    · simp
  · rw [show cmp99SourceFlatFixedCoarseFibreCoefficientExtension ell coeff l = 0 by
      simp [cmp99SourceFlatFixedCoarseFibreCoefficientExtension, hl]]
    symm
    apply Finset.sum_eq_zero
    intro k _
    change cmp99FlatPhysicalFibreDFT
        (cmp99FlatComplexFibreFourierMode k.1
          (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) • coeff k)) l = 0
    rw [cmp99FlatPhysicalFibreDFT_fourierMode]
    have hkl : k.1 ≠ l := by
      intro hval
      apply hl
      simpa [hval] using k.2
    rw [if_neg hkl]
    simp

omit [NeZero d] [NeZero Nc] in
/-- The literal full-box precision is additive in the physical field. -/
theorem cmp99SourceFlatFullComplexPrecisionAction_add
    (mass a : ℝ)
    (phi psi : FinBox d (M * N') → SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionAction mass a (phi + psi) =
      cmp99SourceFlatFullComplexPrecisionAction mass a phi +
        cmp99SourceFlatFullComplexPrecisionAction mass a psi := by
  funext x
  have hactive :
      cmp99SourceFlatFullActiveComplexField (phi + psi) =
        cmp99SourceFlatFullActiveComplexField phi +
          cmp99SourceFlatFullActiveComplexField psi := by
    ext y b
    rfl
  have hq :
      cmp99SourceFlatFullComplexQprimeMass (phi + psi) x =
        cmp99SourceFlatFullComplexQprimeMass phi x +
          cmp99SourceFlatFullComplexQprimeMass psi x := by
    unfold cmp99SourceFlatFullComplexQprimeMass
    rw [hactive, map_add, map_add]
    rfl
  have hstencil :
      cmp99FlatPeriodicComplexFibreStencil (phi + psi) x =
        cmp99FlatPeriodicComplexFibreStencil phi x +
          cmp99FlatPeriodicComplexFibreStencil psi x := by
    unfold cmp99FlatPeriodicComplexFibreStencil
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply]
    module
  unfold cmp99SourceFlatFullComplexPrecisionAction
  rw [hq, hstencil]
  simp only [Pi.add_apply]
  module

/-- Additive packaging of the literal full-box precision action. -/
noncomputable def cmp99SourceFlatFullComplexPrecisionAddHom
    (mass a : ℝ) :
    (FinBox d (M * N') → SUNLieComplexCoord Nc) →+
      (FinBox d (M * N') → SUNLieComplexCoord Nc) where
  toFun := cmp99SourceFlatFullComplexPrecisionAction mass a
  map_zero' := by
    funext x
    have hactive :
        cmp99SourceFlatFullActiveComplexField
            (0 : FinBox d (M * N') → SUNLieComplexCoord Nc) = 0 := by
      ext y b
      rfl
    have hq :
        cmp99SourceFlatFullComplexQprimeMass
            (0 : FinBox d (M * N') → SUNLieComplexCoord Nc) x = 0 := by
      unfold cmp99SourceFlatFullComplexQprimeMass
      rw [hactive, map_zero, map_zero]
      rfl
    have hstencil :
        cmp99FlatPeriodicComplexFibreStencil
            (0 : FinBox d (M * N') → SUNLieComplexCoord Nc) x = 0 := by
      simp [cmp99FlatPeriodicComplexFibreStencil]
    unfold cmp99SourceFlatFullComplexPrecisionAction
    rw [hq, hstencil]
    simp
  map_add' := cmp99SourceFlatFullComplexPrecisionAction_add mass a

omit [NeZero d] [NeZero Nc] in
/-- The literal additive precision action commutes with every finite sum. -/
theorem cmp99SourceFlatFullComplexPrecisionAction_finset_sum
    {ι : Type*} (mass a : ℝ) (s : Finset ι)
    (term : ι → FinBox d (M * N') → SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionAction mass a
        (∑ i ∈ s, term i) =
      ∑ i ∈ s, cmp99SourceFlatFullComplexPrecisionAction mass a (term i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact (cmp99SourceFlatFullComplexPrecisionAddHom
        (d := d) (M := M) (N' := N') (Nc := Nc) mass a).map_zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        cmp99SourceFlatFullComplexPrecisionAction_add, ih]

/-- Arbitrary fixed-fibre coefficient action of the literal full-box
precision.  The output is the transpose alias matrix applied entrywise to the
Lie-fibre coefficient vector; the DFT volume cancels internally. -/
theorem cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fixedCoarseFibre
    (ell : FinBox d N') (mass a : ℝ)
    (coeff : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc)
    (output : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionAction mass a
          (cmp99SourceFlatFixedCoarseFibreFourierSynthesis ell coeff))
        output.1 =
      ∑ input,
        (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a).transpose
          output input • coeff input := by
  rw [cmp99SourceFlatFixedCoarseFibreFourierSynthesis_eq_sum]
  let term : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      FinBox d (M * N') → SUNLieComplexCoord Nc :=
    fun input => cmp99FlatComplexFibreFourierMode input.1
      (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) • coeff input)
  have hprecisionSum :
      cmp99SourceFlatFullComplexPrecisionAction mass a (∑ input, term input) =
        ∑ input,
          cmp99SourceFlatFullComplexPrecisionAction mass a (term input) := by
    simpa only using
      cmp99SourceFlatFullComplexPrecisionAction_finset_sum
        (d := d) (M := M) (N' := N') (Nc := Nc)
        mass a Finset.univ term
  have hterm : (fun x => ∑ input,
      cmp99FlatComplexFibreFourierMode input.1
        (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) • coeff input) x) =
      ∑ input, term input := by
    funext x
    rw [Finset.sum_apply]
  rw [hterm]
  rw [hprecisionSum]
  change cmp99FlatPhysicalFibreDFTLinearEquiv
      (∑ input : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99SourceFlatFullComplexPrecisionAction mass a (term input))
      output.1 = _
  rw [map_sum]
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro input _
  change cmp99FlatPhysicalFibreDFT
      (cmp99SourceFlatFullComplexPrecisionAction mass a
        (cmp99FlatComplexFibreFourierMode input.1
          (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) • coeff input))) output.1 = _
  rw [cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fourierMode]
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hN : (N' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N')
  ext b
  simp only [PiLp.smul_apply, smul_eq_mul]
  field_simp [hM, hN]

end

end YangMills.RG
