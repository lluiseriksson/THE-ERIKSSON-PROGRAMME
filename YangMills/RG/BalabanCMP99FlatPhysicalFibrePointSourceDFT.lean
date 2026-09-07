/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction

/-!
# Exact DFT of a full-box physical point source

The literal point source is sent by the sealed negative-character physical
DFT to the inverse source character. This is the source vector consumed by
the arbitrary-source transposed Eq. (2.46) solution. No Green, inverse or
periodization identity is used.

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
  · have hey :
        (cmp99FinBoxZModEquiv d N).symm (e y) = y :=
      e.symm_apply_apply y
    rw [if_pos hey]
    rw [cmp99FlatZModFourierCharacter_neg_left]
    rw [cmp99FlatFourierMode_eq_finBoxFourierCharacter]
  · intro x _ hx
    have hxy : (cmp99FinBoxZModEquiv d N).symm x ≠ y := by
      intro h
      apply hx
      rw [← h]
      exact (e.apply_symm_apply x).symm
    simp only [if_neg hxy, WithLp.ofLp_zero, Pi.zero_apply, mul_zero]
  · intro hy
    exact (hy (Finset.mem_univ (e y))).elim

end

end YangMills.RG
