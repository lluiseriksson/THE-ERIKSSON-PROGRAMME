/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq237GapComponentCovering

/-!
# Scalar hierarchy for the CMP116 equation-(2.37) split rate

The equation-(2.37) component decay is split into a transport rate and an
entropy reserve.  This module derives the sign and smallness facts used by the
terminal contour theorem from transparent source-hierarchy inequalities.  In
particular, it removes three free certificates from that terminal interface:

* nonnegativity of the transport rate follows from `15 * delta <= 2`;
* nonnegativity of the entropy rate follows from `delta, kappa >= 0`; and
* the rooted-component smallness follows from the equation-(2.29) smallness
  once the block scale is at least two.
-/

namespace YangMills.RG

noncomputable section

/-- The quarter-delta entropy reserve is nonnegative under the source sign
conditions. -/
theorem cmp116Eq237_componentEntropyRate_nonneg
    (hp : CMP116Lemma3Parameters)
    (hdelta : 0 ≤ hp.delta) (hkappa : 0 ≤ hp.kappa) :
    0 ≤ cmp116Eq237ComponentEntropyRate hp := by
  unfold cmp116Eq237ComponentEntropyRate
  positivity

/-- The standard source hierarchy `delta <= 1/16` implies the four-delta
budget used in equations (2.28)--(2.29). -/
theorem cmp116Eq237_four_delta_le_one_of_delta_le_one_sixteen
    {delta : ℝ} (hdelta : delta ≤ (1 : ℝ) / 16) :
    4 * delta ≤ 1 := by
  linarith

/-- The same source hierarchy implies the sign condition for the retained
equation-(2.37) transport rate. -/
theorem cmp116Eq237_fifteen_delta_le_two_of_delta_le_one_sixteen
    {delta : ℝ} (hdelta : delta ≤ (1 : ℝ) / 16) :
    15 * delta ≤ 2 := by
  linarith

/-- The residual transport rate is nonnegative under the explicit hierarchy
condition `15 * delta <= 2`. -/
theorem cmp116Eq237_componentTransportRate_nonneg_of_fifteen_delta
    (hp : CMP116Lemma3Parameters)
    (hkappa : 0 ≤ hp.kappa)
    (hfifteen : 15 * hp.delta ≤ 2) :
    0 ≤ cmp116Eq237ComponentTransportRate hp := by
  rw [show
      cmp116Eq237ComponentTransportRate hp =
        ((2 - 15 * hp.delta) / 4) *
          (hp.blockScale : ℝ) * hp.kappa by
        unfold cmp116Eq237ComponentTransportRate
          cmp116Eq237ComponentEntropyRate
        ring]
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg (sub_nonneg.mpr hfifteen) (by norm_num))
      (Nat.cast_nonneg _))
    hkappa

/-- The equation-(2.29) rooted-animal smallness also controls the component
gas reserve when the block scale is at least two. -/
theorem cmp116Eq237_componentRootedSmall_of_eq229
    (hp : CMP116Lemma3Parameters)
    (hdeltaKappa : 0 ≤ hp.delta * hp.kappa)
    (hblockScale : 2 ≤ hp.blockScale)
    (hEq229 :
      64 * Real.exp (-((hp.delta * hp.kappa) / 48)) < 1) :
    64 *
        Real.exp
          (-(cmp116Eq237ComponentEntropyRate hp / 24)) < 1 := by
  have hscale : (2 : ℝ) ≤ (hp.blockScale : ℝ) := by
    exact_mod_cast hblockScale
  have hmul :
      2 * (hp.delta * hp.kappa) ≤
        (hp.blockScale : ℝ) * (hp.delta * hp.kappa) :=
    mul_le_mul_of_nonneg_right hscale hdeltaKappa
  have harg :
      -(cmp116Eq237ComponentEntropyRate hp / 24) ≤
        -((hp.delta * hp.kappa) / 48) := by
    unfold cmp116Eq237ComponentEntropyRate
    nlinarith
  calc
    64 *
        Real.exp
          (-(cmp116Eq237ComponentEntropyRate hp / 24)) ≤
      64 * Real.exp (-((hp.delta * hp.kappa) / 48)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr harg) (by norm_num)
    _ < 1 := hEq229

end

end YangMills.RG
