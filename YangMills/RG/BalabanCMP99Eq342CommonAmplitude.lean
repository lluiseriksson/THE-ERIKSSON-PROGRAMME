/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpBlockLocalizedSup

/-!
# PRE-VALIDATION: common amplitude for CMP99 (3.42)

This source is present, its `.olean` has not yet been materialized, and none
of the declarations below has yet been verified by the Lean compiler.

The final regional Green certificate uses one strictly positive normalized
amplitude for its value, left derivative, right-adjoint derivative and
Laplacian actions.  The visible added one makes the common majorant strictly
positive even when a particular physical action vanishes; it does not hide a
field-scale factor or replace any analytic estimate.
-/

namespace YangMills.RG

noncomputable section

/-- One explicit common normalized amplitude for the four CMP99 (3.42)
actions. -/
def cmp99Eq342CommonAmplitude
    (Avalue Aleft Aright Alaplacian : ℝ) : ℝ :=
  1 + Avalue + Aleft + Aright + Alaplacian

/-- The common amplitude is strictly positive when all component budgets are
nonnegative. -/
theorem cmp99Eq342CommonAmplitude_pos
    {Avalue Aleft Aright Alaplacian : ℝ}
    (hvalue : 0 ≤ Avalue) (hleft : 0 ≤ Aleft)
    (hright : 0 ≤ Aright) (hlaplacian : 0 ≤ Alaplacian) :
    0 < cmp99Eq342CommonAmplitude
      Avalue Aleft Aright Alaplacian := by
  unfold cmp99Eq342CommonAmplitude
  linarith

theorem le_cmp99Eq342CommonAmplitude_value
    {Avalue Aleft Aright Alaplacian : ℝ}
    (hvalue : 0 ≤ Avalue) (hleft : 0 ≤ Aleft)
    (hright : 0 ≤ Aright) (hlaplacian : 0 ≤ Alaplacian) :
    Avalue ≤ cmp99Eq342CommonAmplitude
      Avalue Aleft Aright Alaplacian := by
  unfold cmp99Eq342CommonAmplitude
  linarith

theorem le_cmp99Eq342CommonAmplitude_left
    {Avalue Aleft Aright Alaplacian : ℝ}
    (hvalue : 0 ≤ Avalue) (hleft : 0 ≤ Aleft)
    (hright : 0 ≤ Aright) (hlaplacian : 0 ≤ Alaplacian) :
    Aleft ≤ cmp99Eq342CommonAmplitude
      Avalue Aleft Aright Alaplacian := by
  unfold cmp99Eq342CommonAmplitude
  linarith

theorem le_cmp99Eq342CommonAmplitude_right
    {Avalue Aleft Aright Alaplacian : ℝ}
    (hvalue : 0 ≤ Avalue) (hleft : 0 ≤ Aleft)
    (hright : 0 ≤ Aright) (hlaplacian : 0 ≤ Alaplacian) :
    Aright ≤ cmp99Eq342CommonAmplitude
      Avalue Aleft Aright Alaplacian := by
  unfold cmp99Eq342CommonAmplitude
  linarith

theorem le_cmp99Eq342CommonAmplitude_laplacian
    {Avalue Aleft Aright Alaplacian : ℝ}
    (hvalue : 0 ≤ Avalue) (hleft : 0 ≤ Aleft)
    (hright : 0 ≤ Aright) (hlaplacian : 0 ≤ Alaplacian) :
    Alaplacian ≤ cmp99Eq342CommonAmplitude
      Avalue Aleft Aright Alaplacian := by
  unfold cmp99Eq342CommonAmplitude
  linarith

end

end YangMills.RG
