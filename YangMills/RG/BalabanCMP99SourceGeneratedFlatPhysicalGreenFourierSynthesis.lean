/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierMode

/-!
# Pointwise Fourier synthesis of the generated flat physical Green

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations have not yet been compiler verified.

Cold-sealed Gate 7 exposes every fine DFT coefficient of the generated Green
on one coarse Fourier source.  This file cancels the literal inverse-volume
normalization in the already sealed inverse DFT and records the resulting
pointwise finite sum.  Each summand keeps the positive physical Fourier
character and the transposed stabilized alias coefficient as separate named
factors; no orientation is inferred from the words `row` or `column`.

This is still a finite periodic synthesis.  It does not identify the sum with
the continuous CMP89 Brillouin integral, prove a Poisson/periodization theorem,
separate the source scales `L` and `K`, construct a regional `B0`, attain
window 15, discharge a terminal field, or inhabit `TermSource`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Scalar summand in the literal inverse-DFT reconstruction of the
central-stabilized physical solution.  The Fourier orientation and the
transposed alias solution remain visible as two factors. -/
def cmp99SourceFlatPhysicalTransposeGreenFourierTerm
    (ell : FinBox d N') (mass a : ℝ) (x : FinBox d (M * N'))
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) : ℂ :=
  cmp99FlatFourierMode k.1 x *
    cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
      (d := d) (M := M) (N' := N') ell mass a k

/-- The internally constructed one-fibre particular solution is exactly the
finite pointwise sum of its positive Fourier characters times the transposed
stabilized alias coefficients.  The fine-volume normalization cancels
internally; no Fourier coefficient or reconstruction identity is supplied by
the caller. -/
theorem cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution_apply_eq_sum_transposeGreenTerms
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc)
    (x : FinBox d (M * N')) :
    cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
        ell mass a v x =
      ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99SourceFlatPhysicalTransposeGreenFourierTerm
          ell mass a x k • v := by
  rw [cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution,
    cmp99SourceFlatFixedCoarseFibreFourierSynthesis_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hvolume : ((((M * N' : ℕ) : ℂ) ^ d)) ≠ 0 := by
    exact pow_ne_zero d
      (Nat.cast_ne_zero.mpr (mul_ne_zero (NeZero.ne M) (NeZero.ne N')))
  unfold cmp99SourceFlatFullComplexPrecisionStabilizedParticularCoefficients
    cmp99SourceFlatPhysicalTransposeGreenFourierTerm
    cmp99FlatComplexFibreFourierMode
  calc
    cmp99FlatFourierMode k.1 x •
          (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) •
            (((((M * N' : ℕ) : ℂ) ^ d) *
              cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
                ell mass a k) • v)) =
        cmp99FlatFourierMode k.1 x •
          (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) •
            ((((M * N' : ℕ) : ℂ) ^ d) •
              (cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
                ell mass a k • v))) := by
      rw [mul_smul]
    _ = cmp99FlatFourierMode k.1 x •
          (cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
            ell mass a k • v) := by
      rw [inv_smul_smul₀ hvolume]
    _ = (cmp99FlatFourierMode k.1 x *
          cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
            ell mass a k) • v := by
      rw [smul_smul]

variable {M Q Nc : ℕ}
variable [NeZero M] [NeZero Q] [NeZero Nc]

/-- Generated Gate-7 endpoint in pointwise finite-synthesis form.  This is
the exact discrete input to the remaining orientation and periodization
dictionary; it is not a continuous-integral identity. -/
theorem cmp99SourceGeneratedFlatPhysicalGreenQprimeStar_fourierMode_apply_eq_sum_transposeGreenTerms
    (hM : 2 ≤ M) (depth : ℕ)
    (ell : FinBox 4 (2 * (M * Q)))
    (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (M ^ (depth + 1) * (2 * (M * Q)))) :
    (((cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM
          (M := M) (Q := Q) (Nc := Nc) hM depth).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
            (Nc := Nc)))
        (cmp99FlatComplexFibreFourierMode ell v)) x =
      ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre
          4 (M ^ (depth + 1)) (2 * (M * Q)) ell,
        cmp99SourceFlatPhysicalTransposeGreenFourierTerm
          ell 0
            (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
              (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0)
          x k • v := by
  rw [cmp99SourceGeneratedFlatPhysicalGreenQprimeStar_fourierMode
    (M := M) (Q := Q) (Nc := Nc) hM depth ell v]
  exact
    cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution_apply_eq_sum_transposeGreenTerms
      ell 0
        (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
          (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0)
        v x

end

end YangMills.RG
