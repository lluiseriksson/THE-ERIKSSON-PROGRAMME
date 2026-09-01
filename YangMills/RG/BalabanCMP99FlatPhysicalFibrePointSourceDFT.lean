/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction

/-!
# PRE-VALIDATION: exact DFT of a full-box physical point source

The literal point source is sent by the sealed negative-character physical
DFT to the inverse source character. This is the source vector consumed by
the arbitrary-source transposed Eq. (2.46) solution. No Green, inverse or
periodization identity is used.

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler. It remains outside the project
import graph until its own compiler and axiom gates pass.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- Exact forward DFT of one literal complex physical-fibre point source. -/
theorem cmp99FlatPhysicalFibreDFT_pointSource
    {d N Nc : ℕ} [NeZero N]
    (y k : FinBox d N) (v : SUNLieComplexCoord Nc) :
    cmp99FlatPhysicalFibreDFT (cmp99FlatComplexFibrePointSource y v) k =
      (cmp99FlatFourierMode k y)⁻¹ • v := by
  classical
  let e := cmp99FinBoxZModEquiv d N
  ext A
  simp only [cmp99FlatPhysicalFibreDFT_apply, cmp99FlatFinBoxDFT,
    cmp99FlatZModDFT, cmp99FlatComplexFibrePointSource,
    PiLp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (e y)]
  · simp only [Equiv.symm_apply_apply, if_pos]
    rw [cmp99FlatZModFourierCharacter_neg_left]
    rw [cmp99FlatFourierMode_eq_finBoxFourierCharacter]
    rfl
  · intro x _ hx
    have hxy : e.symm x ≠ y := by
      intro h
      apply hx
      rw [← h]
      exact e.apply_symm_apply x
    simp [hxy]
  · intro hy
    exact (hy (Finset.mem_univ (e y))).elim

end

end YangMills.RG
