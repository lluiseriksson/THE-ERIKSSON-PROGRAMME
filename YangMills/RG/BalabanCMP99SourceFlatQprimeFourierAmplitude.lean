/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251EntireAverageAmplitude
import YangMills.RG.BalabanCMP99SourceWeightedRegionalAdjoint

/-!
# The flat one-block `Q'` Fourier amplitude

CMP99 (3.19) fixes the one-step zero-cochain average to the coefficient
`M^-d`.  CMP89 (2.45) writes its momentum-space amplitude as the product of
the normalized finite geometric sums `u_M`.  This file proves that these are
literally the same normalization: summing the product character over the
`M^d` block offsets and multiplying once by `M^-d` gives the printed product
amplitude.

The two momentum orientations are kept separate.  Their product is the
scalar factor used by the rank-one `Q'^* Q'` term on an alias fibre.

Honest scope: this file identifies only the scalar offset amplitude.  It does
not yet prove the action of the physical regional `Q'`, identify a fine mode
with a coarse mode, construct the adjoint operator symbol, or diagonalize the
generated precision.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Product character carried by one `d`-dimensional block offset.  Each
coordinate offset is represented by its literal member of `Fin M`. -/
def cmp99SourceFlatQprimeOffsetCharacter
    (d M : ℕ) (z : Fin d → ℂ) (r : Fin d → Fin M) : ℂ :=
  ∏ mu, cmp89Eq245EntireAverageBase M (z mu) ^ (r mu).val

/-- The literal source-normalized sum over all `M^d` offsets of one block. -/
def cmp99SourceFlatQprimeOffsetAmplitude
    (d M : ℕ) (z : Fin d → ℂ) : ℂ :=
  (cmp99SourceBlockAverageWeight M d : ℂ) *
    ∑ r ∈ Fintype.piFinset
        (fun _mu : Fin d ↦ (Finset.univ : Finset (Fin M))),
      cmp99SourceFlatQprimeOffsetCharacter d M z r

/-- The source coefficient `M^-d`, applied once to the block-offset sum, is
exactly the product of the `d` coordinatewise normalizations `M^-1`. -/
theorem cmp99SourceFlatQprimeOffsetAmplitude_eq_entireAverageAmplitude
    (d M : ℕ) (z : Fin d → ℂ) :
    cmp99SourceFlatQprimeOffsetAmplitude d M z =
      cmp89Eq245EntireAverageAmplitude d M z := by
  unfold cmp99SourceFlatQprimeOffsetAmplitude
    cmp99SourceFlatQprimeOffsetCharacter
    cmp89Eq245EntireAverageAmplitude
    cmp89Eq245EntireAverageFactor
  have hsum :
      (∑ r ∈ Fintype.piFinset
          (fun _mu : Fin d ↦ (Finset.univ : Finset (Fin M))),
        ∏ mu, cmp89Eq245EntireAverageBase M (z mu) ^ (r mu).val) =
        ∏ mu, ∑ r : Fin M,
          cmp89Eq245EntireAverageBase M (z mu) ^ r.val := by
    simpa only using
      (Finset.sum_prod_piFinset
        (R := ℂ) (ι := Fin d)
        (Finset.univ : Finset (Fin M))
        (fun mu r => cmp89Eq245EntireAverageBase M (z mu) ^ r.val))
  rw [hsum]
  have hcoeff :
      (cmp99SourceBlockAverageWeight M d : ℂ) =
        ∏ _mu : Fin d, (M : ℂ)⁻¹ := by
    simp [cmp99SourceBlockAverageWeight, ← inv_pow]
  rw [hcoeff, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro mu _
  rw [Fin.sum_univ_eq_sum_range]

/-- Opposite momenta give exactly the holomorphic row/column pairing used for
the source rank-one `Q'^* Q'` term.  No conjugation is inserted away from the
real slice. -/
theorem cmp99SourceFlatQprimeOffsetAmplitude_mul_neg_eq
    (d M : ℕ) (z : Fin d → ℂ) :
    cmp99SourceFlatQprimeOffsetAmplitude d M z *
        cmp99SourceFlatQprimeOffsetAmplitude d M (-z) =
      cmp89Eq245EntireAverageAmplitude d M z *
        cmp89Eq245EntireAverageAmplitude d M (-z) := by
  rw [cmp99SourceFlatQprimeOffsetAmplitude_eq_entireAverageAmplitude,
    cmp99SourceFlatQprimeOffsetAmplitude_eq_entireAverageAmplitude]

end

end YangMills.RG
