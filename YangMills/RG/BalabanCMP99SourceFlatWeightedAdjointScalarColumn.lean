/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AveragingL2
import YangMills.RG.BalabanCMP99FlatPhysicalFibreDFT
import YangMills.RG.BalabanCMP99SourceFlatQprimeBlockOffsetEquiv

/-!
# PRE-VALIDATION: scalar Fourier column of the flat weighted adjoint

Source is present at this checkpoint, its `.olean` has not yet been
materialized, and the result is not yet compiler-verified.

The source-weighted adjoint of one flat block average has coefficient one:
it pulls a coarse scalar field back along `blockSite`.  This module computes
the exact full-box forward DFT of that pullback on one coarse Fourier mode.
The answer is supported on the literal reciprocal fibre
`coarseAlias k = ell`, with the complete fine-volume coefficient and the
one-block amplitude evaluated at the periodic negative representative used
by the forward DFT.

The sign is not converted into a real discrete momentum identity.  Such an
identity would be false for the chosen half-open periodic representatives;
the negative `FinBox` momentum is constructed through the sealed `ZMod`
equivalence and retained literally.

Honest scope: this is the scalar full-box column only.  The physical
`SUNLieComplexCoord` fibre, active-region weighted adjoint, interacting
transport, inverse and regional Green bound remain separate obligations.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

/-- Periodic momentum negation transported from the additive `ZMod` box.
This fixes the forward-DFT sign without choosing an integer representative. -/
def cmp99FinBoxFourierNeg {d N : ℕ} [NeZero N]
    (k : FinBox d N) : FinBox d N :=
  (cmp99FinBoxZModEquiv d N).symm (-(cmp99FinBoxZModEquiv d N k))

@[simp] theorem cmp99FinBoxZModEquiv_fourierNeg
    {d N : ℕ} [NeZero N] (k : FinBox d N) :
    cmp99FinBoxZModEquiv d N (cmp99FinBoxFourierNeg k) =
      -(cmp99FinBoxZModEquiv d N k) := by
  simp [cmp99FinBoxFourierNeg]

/-- The transported negative momentum is exactly the inverse product
character, with no real-representative convention inserted. -/
theorem cmp99FlatFourierMode_fourierNeg
    {d N : ℕ} [NeZero N] (k x : FinBox d N) :
    cmp99FlatFourierMode (cmp99FinBoxFourierNeg k) x =
      (cmp99FlatFourierMode k x)⁻¹ := by
  rw [cmp99FlatFourierMode_eq_finBoxFourierCharacter,
    cmp99FlatFourierMode_eq_finBoxFourierCharacter,
    cmp99FinBoxZModEquiv_fourierNeg,
    cmp99FlatZModFourierCharacter_neg_left]

/-- The literal `FinBox` DFT is the sum against the periodic negative
Fourier mode.  This exposes the site carrier needed for block reindexing. -/
theorem cmp99FlatFinBoxDFT_eq_sum_fourierNeg
    {d N : ℕ} [NeZero N]
    (phi : FinBox d N → ℂ) (k : FinBox d N) :
    cmp99FlatFinBoxDFT phi k =
      ∑ x : FinBox d N, cmp99FlatFourierMode
        (cmp99FinBoxFourierNeg k) x * phi x := by
  unfold cmp99FlatFinBoxDFT cmp99FlatZModDFT
  let e := cmp99FinBoxZModEquiv d N
  calc
    (∑ x, cmp99FlatZModFourierCharacter (-e k) x * phi (e.symm x)) =
        ∑ x, cmp99FlatZModFourierCharacter (-e k) (e x) * phi x := by
      exact (e.sum_comp
        (fun x => cmp99FlatZModFourierCharacter (-e k) x *
          phi (e.symm x))).symm
    _ = ∑ x, cmp99FlatFourierMode (cmp99FinBoxFourierNeg k) x *
          phi x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [cmp99FlatFourierMode_eq_finBoxFourierCharacter,
        cmp99FinBoxZModEquiv_fourierNeg]

/-- Scalar full-box pullback of one coarse Fourier mode along the physical
owner map.  This is the coefficient-one weighted adjoint before adding the
Lie fibre. -/
def cmp99SourceFlatScalarCoarseModeSynthesis
    {d M N' : ℕ} [NeZero M]
    (ell : FinBox d N') (x : FinBox d (M * N')) : ℂ :=
  cmp99FlatFourierMode ell (blockSite M N' x)

/-- After multiplying by the source block weight, the full fine DFT reduces
exactly to the one-block negative-momentum amplitude times the coarse DFT.
This form isolates the normalization cancellation used in the final column. -/
theorem cmp99SourceBlockAverageWeight_mul_flatScalarSynthesisDFT
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N') (k : FinBox d (M * N')) :
    (cmp99SourceBlockAverageWeight M d : ℂ) *
        cmp99FlatFinBoxDFT
          (cmp99SourceFlatScalarCoarseModeSynthesis (M := M) ell) k =
      cmp89Eq245EntireAverageAmplitude d M
          (cmp99SourceFlatQprimeAmplitudeMomentum
            (cmp99FinBoxFourierNeg k)) *
        (if ell = cmp99SourceFlatQprimeCoarseAlias k
          then (N' : ℂ) ^ d else 0) := by
  let kneg : FinBox d (M * N') := cmp99FinBoxFourierNeg k
  let amplitude : ℂ := cmp89Eq245EntireAverageAmplitude d M
    (cmp99SourceFlatQprimeAmplitudeMomentum kneg)
  have hblock (y : FinBox d N') :
      (cmp99SourceBlockAverageWeight M d : ℂ) *
          ∑ x ∈ blockOf M N' y,
            cmp99FlatFourierMode kneg x *
              cmp99FlatFourierMode ell (blockSite M N' x) =
        amplitude * (cmp99FlatFourierMode
          (cmp99SourceFlatQprimeCoarseAlias k) y)⁻¹ *
            cmp99FlatFourierMode ell y := by
    have hsite (r : FinBox d M) :
        blockSite M N' (cmp99BlockEmbed y r) = y :=
      (mem_blockOf M N' y (cmp99BlockEmbed y r)).1
        (cmp99BlockEmbed_mem_blockOf y r)
    calc
      (cmp99SourceBlockAverageWeight M d : ℂ) *
            ∑ x ∈ blockOf M N' y,
              cmp99FlatFourierMode kneg x *
                cmp99FlatFourierMode ell (blockSite M N' x) =
          (cmp99SourceBlockAverageWeight M d : ℂ) *
            ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
              cmp99FlatFourierMode kneg x.1 *
                cmp99FlatFourierMode ell (blockSite M N' x.1) := by
        congr 1
        exact (Finset.sum_subtype (blockOf M N' y) (fun _ => Iff.rfl)
          (fun x => cmp99FlatFourierMode kneg x *
            cmp99FlatFourierMode ell (blockSite M N' x))).symm
      _ = (cmp99SourceBlockAverageWeight M d : ℂ) *
            ∑ r : FinBox d M,
              cmp99FlatFourierMode kneg (cmp99BlockEmbed y r) *
                cmp99FlatFourierMode ell y := by
        congr 1
        rw [sum_blockSites_eq_sum_offsets]
        apply Finset.sum_congr rfl
        intro r _
        rw [hsite]
      _ = ((cmp99SourceBlockAverageWeight M d : ℂ) *
            ∑ r : FinBox d M,
              cmp99FlatFourierMode kneg (cmp99BlockEmbed y r)) *
            cmp99FlatFourierMode ell y := by
        rw [← Finset.sum_mul]
        ring
      _ = (amplitude * cmp99FlatFourierMode kneg
              (blockBasepoint M N' y)) *
            cmp99FlatFourierMode ell y := by
        rw [cmp99SourceFlatQprimeWeightedBlockSum_fourierMode]
      _ = amplitude * (cmp99FlatFourierMode
              (cmp99SourceFlatQprimeCoarseAlias k) y)⁻¹ *
            cmp99FlatFourierMode ell y := by
        rw [cmp99FlatFourierMode_fourierNeg,
          cmp99FlatFourierMode_blockBasepoint_eq_coarseAlias]
  calc
    (cmp99SourceBlockAverageWeight M d : ℂ) *
          cmp99FlatFinBoxDFT
            (cmp99SourceFlatScalarCoarseModeSynthesis (M := M) ell) k =
        (cmp99SourceBlockAverageWeight M d : ℂ) *
          ∑ x : FinBox d (M * N'),
            cmp99FlatFourierMode kneg x *
              cmp99FlatFourierMode ell (blockSite M N' x) := by
      rw [cmp99FlatFinBoxDFT_eq_sum_fourierNeg]
      rfl
    _ = (cmp99SourceBlockAverageWeight M d : ℂ) *
          ∑ y : FinBox d N', ∑ x ∈ blockOf M N' y,
            cmp99FlatFourierMode kneg x *
              cmp99FlatFourierMode ell (blockSite M N' x) := by
      rw [← sum_blockOf M N']
    _ = ∑ y : FinBox d N',
          (cmp99SourceBlockAverageWeight M d : ℂ) *
            ∑ x ∈ blockOf M N' y,
              cmp99FlatFourierMode kneg x *
                cmp99FlatFourierMode ell (blockSite M N' x) := by
      rw [Finset.mul_sum]
    _ = ∑ y : FinBox d N',
          amplitude * (cmp99FlatFourierMode
            (cmp99SourceFlatQprimeCoarseAlias k) y)⁻¹ *
              cmp99FlatFourierMode ell y := by
      apply Finset.sum_congr rfl
      intro y _
      exact hblock y
    _ = amplitude *
          ∑ y : FinBox d N',
            (cmp99FlatFourierMode
              (cmp99SourceFlatQprimeCoarseAlias k) y)⁻¹ *
                cmp99FlatFourierMode ell y := by
      rw [Finset.mul_sum]
    _ = amplitude * cmp99FlatFinBoxDFT
          (cmp99FlatFourierMode ell)
          (cmp99SourceFlatQprimeCoarseAlias k) := by
      congr 1
      rw [cmp99FlatFinBoxDFT_eq_sum_fourierNeg]
      apply Finset.sum_congr rfl
      intro y _
      rw [cmp99FlatFourierMode_fourierNeg]
    _ = amplitude *
          (if ell = cmp99SourceFlatQprimeCoarseAlias k
            then (N' : ℂ) ^ d else 0) := by
      rw [cmp99FlatFinBoxDFT_fourierMode]

/-- Exact scalar direct Fourier column of the coefficient-one source
weighted adjoint.  The volume factor is the full fine cardinality and the
support is the literal coarse reciprocal fibre. -/
theorem cmp99FlatFinBoxDFT_sourceFlatScalarCoarseModeSynthesis
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N') (k : FinBox d (M * N')) :
    cmp99FlatFinBoxDFT
        (cmp99SourceFlatScalarCoarseModeSynthesis (M := M) ell) k =
      if cmp99SourceFlatQprimeCoarseAlias k = ell then
        ((M * N' : ℕ) : ℂ) ^ d *
          cmp89Eq245EntireAverageAmplitude d M
            (cmp99SourceFlatQprimeAmplitudeMomentum
              (cmp99FinBoxFourierNeg k))
      else 0 := by
  have hw : (M : ℂ) ^ d *
      (cmp99SourceBlockAverageWeight M d : ℂ) = 1 := by
    exact_mod_cast (card_mul_cmp99SourceBlockAverageWeight
      (M := M) (d := d))
  have hweighted :=
    cmp99SourceBlockAverageWeight_mul_flatScalarSynthesisDFT
      (M := M) ell k
  calc
    cmp99FlatFinBoxDFT
          (cmp99SourceFlatScalarCoarseModeSynthesis (M := M) ell) k =
        (M : ℂ) ^ d *
          ((cmp99SourceBlockAverageWeight M d : ℂ) *
            cmp99FlatFinBoxDFT
              (cmp99SourceFlatScalarCoarseModeSynthesis (M := M) ell) k) := by
      rw [← mul_assoc, hw, one_mul]
    _ = (M : ℂ) ^ d *
          (cmp89Eq245EntireAverageAmplitude d M
              (cmp99SourceFlatQprimeAmplitudeMomentum
                (cmp99FinBoxFourierNeg k)) *
            (if ell = cmp99SourceFlatQprimeCoarseAlias k
              then (N' : ℂ) ^ d else 0)) := by
      rw [hweighted]
    _ = if cmp99SourceFlatQprimeCoarseAlias k = ell then
          ((M * N' : ℕ) : ℂ) ^ d *
            cmp89Eq245EntireAverageAmplitude d M
              (cmp99SourceFlatQprimeAmplitudeMomentum
                (cmp99FinBoxFourierNeg k))
        else 0 := by
      by_cases h : cmp99SourceFlatQprimeCoarseAlias k = ell
      · rw [if_pos h, if_pos h.symm]
        push_cast
        rw [mul_pow]
        ring
      · rw [if_neg h, if_neg]
        · ring
        · exact fun heq => h heq.symm

end

end YangMills.RG
