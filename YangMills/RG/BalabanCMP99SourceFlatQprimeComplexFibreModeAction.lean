/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalFibreComplexification
import YangMills.RG.BalabanCMP99SourceFlatQprimeCoarseAlias

/-!
# Flat `Q'` mode action in the complexified physical fibre

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the compiler.

The scalar one-block action and its reciprocal alias are already literal.
This module transports that equality to `SUNLieComplexCoord Nc`, the explicit
coordinatewise complexification of the physical Lie-coordinate fibre.  A
second endpoint specializes the fibre vector to the image of an actual
`SUNLieCoord Nc` vector.

Honest scope: this is the flat identity-transport block sum.  It does not
identify the contour-holonomy transport with the identity, instantiate the
active-region CLM, construct the weighted adjoint, diagonalize `Q'^* Q'`,
construct an inverse or transport to a regional Green operator.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {d M N' Nc : ℕ} [NeZero M] [NeZero N']

/-- Sampling a complexified physical-fibre mode at the block basepoint gives
the same fibre vector carried by the constructed coarse reciprocal alias. -/
theorem cmp99FlatComplexFibreFourierMode_blockBasepoint_eq_coarseAlias
    (k : FinBox d (M * N')) (y : FinBox d N')
    (v : SUNLieComplexCoord Nc) :
    cmp99FlatComplexFibreFourierMode k v (blockBasepoint M N' y) =
      cmp99FlatComplexFibreFourierMode
        (cmp99SourceFlatQprimeCoarseAlias k) v y := by
  unfold cmp99FlatComplexFibreFourierMode
  rw [cmp99FlatFourierMode_blockBasepoint_eq_coarseAlias]

/-- Exact one-block action on a Fourier mode valued in the explicit
complexified physical fibre. -/
theorem cmp99SourceFlatQprimeWeightedBlockSum_complexFibreFourierMode_eq_coarseAlias
    (k : FinBox d (M * N')) (y : FinBox d N')
    (v : SUNLieComplexCoord Nc) :
    ((cmp99SourceBlockAverageWeight M d : ℝ) : ℂ) •
        ∑ r : FinBox d M,
          cmp99FlatComplexFibreFourierMode k v (cmp99BlockEmbed y r) =
      cmp89Eq245EntireAverageAmplitude d M
          (cmp99SourceFlatQprimeAmplitudeMomentum k) •
        cmp99FlatComplexFibreFourierMode
          (cmp99SourceFlatQprimeCoarseAlias k) v y := by
  unfold cmp99FlatComplexFibreFourierMode
  rw [← Finset.sum_smul]
  simp only [smul_smul]
  rw [cmp99SourceFlatQprimeWeightedBlockSum_fourierMode_eq_coarseAlias]

/-- Physical-real specialization of the complex-fibre one-block action.  The
fibre vector is constructed internally by the sealed coordinatewise
complexification map. -/
theorem cmp99SourceFlatQprimeWeightedBlockSum_complexifiedPhysicalMode_eq_coarseAlias
    (k : FinBox d (M * N')) (y : FinBox d N') (X : SUNLieCoord Nc) :
    ((cmp99SourceBlockAverageWeight M d : ℝ) : ℂ) •
        ∑ r : FinBox d M,
          cmp99FlatComplexFibreFourierMode k
            (cmp99SUNLieCoordComplexificationLM Nc X) (cmp99BlockEmbed y r) =
      cmp89Eq245EntireAverageAmplitude d M
          (cmp99SourceFlatQprimeAmplitudeMomentum k) •
        cmp99FlatComplexFibreFourierMode
          (cmp99SourceFlatQprimeCoarseAlias k)
          (cmp99SUNLieCoordComplexificationLM Nc X) y := by
  exact
    cmp99SourceFlatQprimeWeightedBlockSum_complexFibreFourierMode_eq_coarseAlias
      k y (cmp99SUNLieCoordComplexificationLM Nc X)

end

end YangMills.RG
