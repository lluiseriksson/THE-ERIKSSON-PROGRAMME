/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatPhysicalComplexWeightedAdjoint
import YangMills.RG.BalabanCMP99SourceFlatWeightedAdjointScalarColumn

/-!
# PRE-VALIDATION: physical Fourier column of the flat weighted adjoint

Source is present at this checkpoint, its `.olean` has not yet been
materialized, and the result is not yet compiler-verified.

This module lifts the sealed scalar reciprocal-fibre column coordinatewise
to the literal `SUNLieComplexCoord` fibre.  The synthesized fine field is not
introduced independently: it is the actual active-region flat complex
weighted adjoint, specialized to the full fine box and applied to one
restricted coarse Fourier mode.

The output support is the literal coarse-alias fibre.  The coefficient keeps
the full fine volume, the one-block entire amplitude and the periodic
negative momentum selected by the forward DFT visible.

Honest scope: this is still the flat full-box column.  It does not identify
flat and interacting transport, construct the interacting precision or its
inverse, restrict to a regional Dirichlet carrier, or prove a Green bound.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- The literal full fine site region used only to specialize the already
constructed active-region weighted adjoint. -/
def cmp99SourceFlatFullFineRegion (d N : ℕ) : ActiveGaugeRegion d N :=
  ActiveGaugeRegion.mk Finset.univ

@[simp] theorem mem_cmp99SourceFlatFullFineRegion_sites
    {d N : ℕ} (x : FinBox d N) :
    x ∈ (cmp99SourceFlatFullFineRegion d N).sites := by
  simp [cmp99SourceFlatFullFineRegion]

/-- The full fine box is block-saturated for every literal owner map. -/
theorem cmp99SourceFlatFullFineRegion_blockSaturated
    {d M N' : ℕ} [NeZero M] [NeZero N'] :
    (cmp99SourceFlatFullFineRegion d (M * N')).BlockSaturated := by
  intro x _ z _
  exact mem_cmp99SourceFlatFullFineRegion_sites z

/-- Full-box field obtained by applying the actual coefficient-one flat
complex weighted adjoint to one coarse physical-fibre Fourier mode. -/
noncomputable def cmp99SourceFlatFullComplexWeightedAdjointCoarseMode
    {d M N' Nc : ℕ} [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (ell : FinBox d N') (v : SUNLieComplexCoord Nc) :
    FinBox d (M * N') → SUNLieComplexCoord Nc :=
  fun x =>
    cmp99SourceFlatComplexBlockWeightedAdjointCLM
      (cmp99SourceFlatFullFineRegion d (M * N'))
      (cmp99SourceFlatFullFineRegion_blockSaturated
        (d := d) (M := M) (N' := N'))
      (cmp99SourceFlatActiveComplexFibreFourierMode
        (cmp99ActiveCoarseRegion (M := M) (N' := N')
          (cmp99SourceFlatFullFineRegion d (M * N'))) ell v)
      ⟨x, mem_cmp99SourceFlatFullFineRegion_sites x⟩

/-- Pointwise identification of the full active weighted-adjoint output with
the scalar owner pullback times the unchanged physical Lie-fibre vector. -/
theorem cmp99SourceFlatFullComplexWeightedAdjointCoarseMode_apply
    {d M N' Nc : ℕ} [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (ell : FinBox d N') (v : SUNLieComplexCoord Nc)
    (x : FinBox d (M * N')) :
    cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell v x =
      cmp99FlatComplexFibreFourierMode ell v (blockSite M N' x) := by
  unfold cmp99SourceFlatFullComplexWeightedAdjointCoarseMode
  rw [cmp99SourceFlatComplexBlockWeightedAdjoint_fourierMode]
  rfl

/-- Exact complex physical-fibre direct Fourier column of the source flat
weighted adjoint.  No free Fourier family or pointwise column is supplied. -/
theorem cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexWeightedAdjointCoarseMode
    {d M N' Nc : ℕ} [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (ell : FinBox d N') (v : SUNLieComplexCoord Nc)
    (k : FinBox d (M * N')) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell v) k =
      if cmp99SourceFlatQprimeCoarseAlias k = ell then
        (((M * N' : ℕ) : ℂ) ^ d *
          cmp89Eq245EntireAverageAmplitude d M
            (cmp99SourceFlatQprimeAmplitudeMomentum
              (cmp99FinBoxFourierNeg k))) • v
      else 0 := by
  have hfun (a : Fin (Nc ^ 2 - 1)) :
      (fun x : FinBox d (M * N') =>
        cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell v x a) =
        fun x => cmp99SourceFlatScalarCoarseModeSynthesis ell x * v a := by
    funext x
    rw [cmp99SourceFlatFullComplexWeightedAdjointCoarseMode_apply]
    rfl
  by_cases h : cmp99SourceFlatQprimeCoarseAlias k = ell
  · rw [if_pos h]
    ext a
    change cmp99FlatFinBoxDFT
        (fun x =>
          cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell v x a) k =
      (((M * N' : ℕ) : ℂ) ^ d *
        cmp89Eq245EntireAverageAmplitude d M
          (cmp99SourceFlatQprimeAmplitudeMomentum
            (cmp99FinBoxFourierNeg k))) * v a
    rw [hfun a, cmp99FlatFinBoxDFT_mul_const,
      cmp99FlatFinBoxDFT_sourceFlatScalarCoarseModeSynthesis, if_pos h]
  · rw [if_neg h]
    ext a
    change cmp99FlatFinBoxDFT
        (fun x =>
          cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell v x a) k = 0
    rw [hfun a, cmp99FlatFinBoxDFT_mul_const,
      cmp99FlatFinBoxDFT_sourceFlatScalarCoarseModeSynthesis, if_neg h,
      zero_mul]

end

end YangMills.RG
