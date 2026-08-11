/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatWeightedAdjointFourierOrientation

/-!
# PRE-VALIDATION: full-box flat complex precision on one Fourier mode

The source is present, its `.olean` has not yet been materialized, and its
result has not yet been verified by the compiler.

CMP89 (2.44) uses the literal full-lattice precision

`-Delta^xi + m_j^2 + a_j Q_j^* Q_j`.

This module assembles that operator pointwise from the already constructed
flat complex physical stencil, the scalar mass and the actual source
full-box average followed by its coefficient-one weighted adjoint.  The
scalar mass `m_j^2` and the averaging coefficient `a_j` remain separate: the
former is not the recursively generated CMP99 coefficient multiplying
`Q'^*Q'`.

On a single physical Fourier mode, the forward DFT is proved to be one
column of the transpose of the sealed fixed-fibre alias matrix.  Thus the
orientation is inherited from the literal `Q'`/weighted-adjoint action, not
from an abstract self-adjointness argument and not from a synthetic Fourier
operator.

Honest scope: this is a mode-column identity on the flat periodic full box.
It does not yet prove the action on an arbitrary Fourier coefficient vector,
construct an inverse CLM, stabilize the central removable zero, or transport
the result to an interacting or regional precision.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- A full-box complex field viewed on the literal full active region. -/
def cmp99SourceFlatFullActiveComplexField
    (phi : FinBox d (M * N') → SUNLieComplexCoord Nc) :
    ActiveGaugeZeroCochain
      (cmp99SourceFlatFullFineRegion d (M * N'))
      (SUNLieComplexCoord Nc) :=
  WithLp.toLp 2 fun x => phi x.1

omit [NeZero d] [NeZero Nc] in
@[simp] theorem cmp99SourceFlatFullActiveComplexField_apply
    (phi : FinBox d (M * N') → SUNLieComplexCoord Nc)
    (x : ActiveGaugeRegion.Site
      (cmp99SourceFlatFullFineRegion d (M * N'))) :
    cmp99SourceFlatFullActiveComplexField phi x = phi x.1 := rfl

/-- Literal full-box `Q'^*Q'`, built by composing the already constructed
source-normalized flat average and coefficient-one weighted adjoint. -/
noncomputable def cmp99SourceFlatFullComplexQprimeMass
    (phi : FinBox d (M * N') → SUNLieComplexCoord Nc)
    (x : FinBox d (M * N')) : SUNLieComplexCoord Nc :=
  cmp99SourceFlatComplexBlockWeightedAdjointCLM
      (cmp99SourceFlatFullFineRegion d (M * N'))
      (cmp99SourceFlatFullFineRegion_blockSaturated
        (d := d) (M := M) (N' := N'))
      (cmp99SourceFlatComplexBlockAverageCLM
        (cmp99SourceFlatFullFineRegion d (M * N'))
        (cmp99SourceFlatFullActiveComplexField phi))
      ⟨x, mem_cmp99SourceFlatFullFineRegion_sites x⟩

/-- The literal full-box `Q'^*Q'` sends one fine Fourier mode to the direct
average column times the actual weighted-adjoint coarse-mode synthesis. -/
theorem cmp99SourceFlatFullComplexQprimeMass_fourierMode
    (k : FinBox d (M * N')) (v : SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexQprimeMass
        (cmp99FlatComplexFibreFourierMode k v) =
      fun x =>
        cmp89Eq245EntireAverageAmplitude d M
            (cmp99SourceFlatQprimeAmplitudeMomentum k) •
          cmp99SourceFlatFullComplexWeightedAdjointCoarseMode
            (cmp99SourceFlatQprimeCoarseAlias k) v x := by
  funext x
  rw [cmp99SourceFlatFullComplexQprimeMass,
    cmp99SourceFlatComplexBlockWeightedAdjointCLM_apply]
  have hmode :
      cmp99SourceFlatFullActiveComplexField
          (cmp99FlatComplexFibreFourierMode k v) =
        cmp99SourceFlatActiveComplexFibreFourierMode
          (cmp99SourceFlatFullFineRegion d (M * N')) k v := by
    rfl
  rw [hmode, cmp99SourceFlatComplexBlockAverage_fourierMode]
  simp only [PiLp.smul_apply]
  rw [cmp99SourceFlatFullComplexWeightedAdjointCoarseMode_apply]
  rfl

/-- Literal pointwise full-box complex precision from CMP89 (2.44): scaled
flat stencil, scalar mass, and the separate source `Q'^*Q'` term. -/
noncomputable def cmp99SourceFlatFullComplexPrecisionAction
    (mass a : ℝ)
    (phi : FinBox d (M * N') → SUNLieComplexCoord Nc)
    (x : FinBox d (M * N')) : SUNLieComplexCoord Nc :=
  (M : ℂ) ^ 2 • cmp99FlatPeriodicComplexFibreStencil phi x +
    (mass : ℂ) ^ 2 • phi x +
      (a : ℂ) • cmp99SourceFlatFullComplexQprimeMass phi x

/-- On one Fourier mode the literal physical precision separates into its
physical diagonal and the actual weighted-adjoint synthesis. -/
theorem cmp99SourceFlatFullComplexPrecisionAction_fourierMode
    (mass a : ℝ) (k : FinBox d (M * N'))
    (v : SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionAction mass a
        (cmp99FlatComplexFibreFourierMode k v) =
      fun x =>
        cmp99SourceFlatQprimePhysicalFineSymbol mass k •
            cmp99FlatComplexFibreFourierMode k v x +
          ((a : ℂ) * cmp89Eq245EntireAverageAmplitude d M
            (cmp99SourceFlatQprimeAmplitudeMomentum k)) •
            cmp99SourceFlatFullComplexWeightedAdjointCoarseMode
              (cmp99SourceFlatQprimeCoarseAlias k) v x := by
  funext x
  rw [cmp99SourceFlatFullComplexPrecisionAction,
    cmp99FlatPeriodicComplexFibreStencil_fourierMode,
    cmp99SourceFlatFullComplexQprimeMass_fourierMode]
  rw [cmp99SourceFlatQprimePhysicalFineSymbol_eq_rescaledPeriodic]
  unfold cmp99SourceFlatQprimeRescaledPeriodicFineSymbol
  module

/-- Exact DFT column of the literal full-box precision on one fixed physical
reciprocal fibre.  The matrix is transposed for the source orientation fixed
by the forward DFT and the coefficient-one weighted adjoint. -/
theorem cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fourierMode
    (ell : FinBox d N') (mass a : ℝ)
    (input output : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell)
    (v : SUNLieComplexCoord Nc) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionAction mass a
          (cmp99FlatComplexFibreFourierMode input.1 v)) output.1 =
      ((((M * N' : ℕ) : ℂ) ^ d) *
        (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a).transpose
          output input) • v := by
  rw [cmp99SourceFlatFullComplexPrecisionAction_fourierMode]
  rw [input.property]
  change cmp99FlatPhysicalFibreDFTLinearEquiv
      (cmp99SourceFlatQprimePhysicalFineSymbol mass input.1 •
          cmp99FlatComplexFibreFourierMode input.1 v +
        (((a : ℂ) * cmp89Eq245EntireAverageAmplitude d M
          (cmp99SourceFlatQprimeAmplitudeMomentum input.1)) •
            cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell v))
        output.1 = _
  rw [map_add, map_smul, map_smul]
  change
    cmp99SourceFlatQprimePhysicalFineSymbol mass input.1 •
          cmp99FlatPhysicalFibreDFT
            (cmp99FlatComplexFibreFourierMode input.1 v) output.1 +
        (((a : ℂ) * cmp89Eq245EntireAverageAmplitude d M
          (cmp99SourceFlatQprimeAmplitudeMomentum input.1)) •
            cmp99FlatPhysicalFibreDFT
              (cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell v)
              output.1) = _
  rw [cmp99FlatPhysicalFibreDFT_fourierMode,
    cmp99FlatPhysicalFibreDFT_sourceFlatWeightedAdjoint_fixedCoarse_eq_aliasRow]
  rw [Matrix.transpose_apply,
    cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix,
    cmp99SourceFlatQprimePhysicalRankOneMatrix,
    cmp99SourceFlatQprimeNegAmplitude_eq_entireAliasRow]
  by_cases h : input = output
  · subst output
    rw [if_pos rfl, if_pos rfl]
    module
  · have hval : input.1 ≠ output.1 := by
      intro hval
      exact h (Subtype.ext hval)
    rw [if_neg hval, if_neg h]
    module

end

end YangMills.RG
