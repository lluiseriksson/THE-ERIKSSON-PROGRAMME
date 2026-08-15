/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreenIdentification

/-!
# Generated flat physical Green on one coarse Fourier mode

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations have not yet been compiler verified.

Gate 6 identifies the complete stabilized Step-7b field with the internally
generated Green composed with the literal coefficient-one `Q'^*`.  This file
specializes that equality to one coarse physical Fourier mode.  The finite
coarse DFT then collapses the complete field to the already constructed
central-stabilized particular solution on exactly one reciprocal fibre.

The last two theorems expose the resulting fine DFT coefficients on and off
that fibre.  They are the discrete side of the remaining Fourier/operator
dictionary.  No equality with the continuous Brillouin integral, regional
Green bound, uniform physical `B0`, window-15 attainment, terminal field, or
`TermSource` inhabitant is asserted.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

omit [NeZero d] [NeZero Nc] in
/-- A single coarse Fourier source collapses the complete stabilized
`G Q'^*` field to its one-fibre particular solution. -/
theorem
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField_fourierMode
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
        (d := d) (M := M) (N' := N') (Nc := Nc) mass a
        (cmp99FlatComplexFibreFourierMode ell v) =
      cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
        (d := d) (M := M) (N' := N') (Nc := Nc) ell mass a v := by
  classical
  unfold cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
  rw [Finset.sum_eq_single ell]
  · have hN : ((N' : ℂ) ^ d) ≠ 0 := by
      exact pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne N'))
    rw [cmp99FlatPhysicalFibreDFT_fourierMode, if_pos rfl]
    simp only [inv_smul_smul₀ hN]
  · intro k _ hk
    have hellk : ell ≠ k := by
      exact fun h => hk h.symm
    rw [cmp99FlatPhysicalFibreDFT_fourierMode, if_neg hellk]
    simpa using
      (cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution_smul
        (d := d) (M := M) (N' := N') (Nc := Nc)
        k mass a (0 : ℂ) v)
  · intro hnot
    exact (hnot (Finset.mem_univ ell)).elim

variable {M Q Nc : ℕ}
variable [NeZero M] [NeZero Q] [NeZero Nc]

/-- Generated Gate-6 endpoint on one coarse Fourier mode: the literal
`G Q'^*` output is exactly the central-stabilized one-fibre solution. -/
theorem cmp99SourceGeneratedFlatPhysicalGreenQprimeStar_fourierMode
    (hM : 2 ≤ M) (depth : ℕ)
    (ell : FinBox 4 (2 * (M * Q)))
    (v : SUNLieComplexCoord Nc) :
    ((cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM
        (M := M) (Q := Q) (Nc := Nc) hM depth).comp
      (cmp99SourceFlatFullComplexWeightedAdjointCLM
        (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
          (Nc := Nc)))
        (cmp99FlatComplexFibreFourierMode ell v) =
      cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
        (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
        (Nc := Nc) ell 0
        (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
          (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0) v := by
  have hgate := congrArg
    (fun T :
        (FinBox 4 (2 * (M * Q)) → SUNLieComplexCoord Nc) →L[ℂ]
          (FinBox 4 (M ^ (depth + 1) * (2 * (M * Q))) →
            SUNLieComplexCoord Nc) =>
      T (cmp99FlatComplexFibreFourierMode ell v))
    (cmp99SourceGeneratedFlatPhysicalStabilizedFieldCLM_eq_green_comp
      (M := M) (Q := Q) (Nc := Nc) hM depth)
  simpa only [
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldCLM_apply,
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField_fourierMode]
    using hgate.symm

/-- On its selected reciprocal fibre, the generated Gate-6 endpoint has the
literal stabilized alias coefficient and the exact fine-volume factor. -/
theorem cmp99FlatPhysicalFibreDFT_generatedFlatPhysicalGreenQprimeStar_fourierMode
    (hM : 2 ≤ M) (depth : ℕ)
    (ell : FinBox 4 (2 * (M * Q)))
    (v : SUNLieComplexCoord Nc)
    (k : CMP99SourceFlatQprimeFixedCoarseFibre
      4 (M ^ (depth + 1)) (2 * (M * Q)) ell) :
    cmp99FlatPhysicalFibreDFT
        (((cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM
            (M := M) (Q := Q) (Nc := Nc) hM depth).comp
          (cmp99SourceFlatFullComplexWeightedAdjointCLM
            (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
              (Nc := Nc)))
          (cmp99FlatComplexFibreFourierMode ell v)) k.1 =
      ((((M ^ (depth + 1) * (2 * (M * Q)) : ℕ) : ℂ) ^ 4) *
          cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
            ell 0
              (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
                (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0)
              k) • v := by
  rw [cmp99SourceGeneratedFlatPhysicalGreenQprimeStar_fourierMode
    (M := M) (Q := Q) (Nc := Nc) hM depth ell v]
  exact cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_fixedCoarseFibre
    ell 0
      (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0)
      v k

/-- Outside the selected reciprocal fibre, the generated Gate-6 one-mode
endpoint has zero fine DFT. -/
theorem cmp99FlatPhysicalFibreDFT_generatedFlatPhysicalGreenQprimeStar_fourierMode_eq_zero_of_coarseAlias_ne
    (hM : 2 ≤ M) (depth : ℕ)
    (ell : FinBox 4 (2 * (M * Q)))
    (v : SUNLieComplexCoord Nc)
    (k : FinBox 4 (M ^ (depth + 1) * (2 * (M * Q))))
    (hk : cmp99SourceFlatQprimeCoarseAlias k ≠ ell) :
    cmp99FlatPhysicalFibreDFT
        (((cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM
            (M := M) (Q := Q) (Nc := Nc) hM depth).comp
          (cmp99SourceFlatFullComplexWeightedAdjointCLM
            (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
              (Nc := Nc)))
          (cmp99FlatComplexFibreFourierMode ell v)) k = 0 := by
  rw [cmp99SourceGeneratedFlatPhysicalGreenQprimeStar_fourierMode
    (M := M) (Q := Q) (Nc := Nc) hM depth ell v]
  exact
    cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_eq_zero_of_coarseAlias_ne
      ell 0
        (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
          (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0)
        v k hk

end

end YangMills.RG
