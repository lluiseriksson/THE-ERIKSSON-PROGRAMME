/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246StabilizedAliasTransposeFullSolution

/-!
# Direct/transpose pairing for the full CMP89 (2.46) solve

The direct and transposed arbitrary-source solvers already satisfy the two
literal finite matrix equations.  This module records the exact bilinear
pairing between them.  It is the algebraic orientation gate needed before
the half-open alias reflection can exchange the two physical endpoints.

No self-adjointness of the precision, endpoint reflection, finite-grid
aliasing, regional estimate, window-15 attainment, terminal field, or
`TermSource` inhabitant is assumed or asserted.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- Pairing a target with the direct full solution of one source is exactly
pairing that source with the transposed full solution of the target.  Both
solutions are constructed internally and the equality uses their literal
matrix equations; no symmetry of the precision matrix is assumed. -/
theorem cmp89Eq246StabilizedAliasFullSolution_transpose_pairing
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (source target : CMP89Eq246AliasIndex d L j → ℂ)
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0)
    (hrow : cmp89Eq246EntireAliasAverageRow d L j z
        (cmp89Eq249CentralAliasIndex d L j) ≠ 0)
    (hcolumn : cmp89Eq246EntireAliasAverageColumn d L j z
        (cmp89Eq249CentralAliasIndex d L j) ≠ 0) :
    (∑ m, target m *
        cmp89Eq246StabilizedAliasFullSolution
          d L j mass a z source m) =
      ∑ m, source m *
        cmp89Eq246StabilizedAliasTransposeFullSolution
          d L j mass a z target m := by
  let A := cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z
  let x := cmp89Eq246StabilizedAliasFullSolution
    d L j mass a z source
  let y := cmp89Eq246StabilizedAliasTransposeFullSolution
    d L j mass a z target
  have hx : A.mulVec x = source := by
    exact cmp89Eq246EntireAliasPrecisionMatrix_mulVec_stabilizedFullSolution
      d L j mass a z source hfine hstabilized hrow
  have hy : A.transpose.mulVec y = target := by
    exact
      cmp89Eq246EntireAliasPrecisionMatrix_transpose_mulVec_stabilizedFullSolution
        d L j mass a z target hfine hstabilized hcolumn
  change dotProduct target x = dotProduct source y
  calc
    dotProduct target x = dotProduct (A.transpose.mulVec y) x := by rw [hy]
    _ = dotProduct x (A.transpose.mulVec y) := dotProduct_comm _ _
    _ = dotProduct (A.mulVec x) y := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = dotProduct y (A.mulVec x) := dotProduct_comm _ _
    _ = dotProduct y source := by rw [hx]
    _ = dotProduct source y := dotProduct_comm _ _

end

end YangMills.RG
