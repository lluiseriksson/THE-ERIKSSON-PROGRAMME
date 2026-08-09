/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245EntireLaplacianVariation

/-!
# PRE-VALIDATION: scaled-difference upper bound on the CMP89 strip

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.

One stabilized endpoint numerator contains a single entire scaled lattice
difference.  Its sealed vertical variation costs `rho * exp rho`, while its
matching real value is bounded by the absolute real momentum.  This file
exposes their literal sum without replacing it by an anonymous constant.

No endpoint numerator, alias sum, contour integral, complete `B0`, physical
owner bound, window-15 conclusion or terminal field is produced here.
-/

namespace YangMills.RG

noncomputable section

/-- A single entire scaled difference is bounded on the strip by the real
momentum plus the already sealed vertical budget. -/
theorem norm_cmp89Eq245EntireScaledDifference_le_abs_re_add_vertical
    {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    {z : ℂ} {rho : ℝ} (hrho : 0 ≤ rho) (hz : |z.im| ≤ rho) :
    ‖cmp89Eq245EntireScaledDifference xi z‖ ≤
      |z.re| + rho * Real.exp rho := by
  have hvariation :=
    norm_cmp89Eq245EntireScaledDifference_sub_realSlice_le
      hxi hxi1 hrho hz
  have hreal :
      ‖cmp89Eq245EntireScaledDifference xi (z.re : ℂ)‖ ≤ |z.re| := by
    rw [norm_cmp89Eq245EntireScaledDifference_ofReal_eq]
    exact cmp89Eq245ScaledDifferenceNorm_le_abs hxi
  calc
    ‖cmp89Eq245EntireScaledDifference xi z‖ =
        ‖(cmp89Eq245EntireScaledDifference xi z -
            cmp89Eq245EntireScaledDifference xi (z.re : ℂ)) +
          cmp89Eq245EntireScaledDifference xi (z.re : ℂ)‖ := by
      congr 1
      ring
    _ ≤ ‖cmp89Eq245EntireScaledDifference xi z -
          cmp89Eq245EntireScaledDifference xi (z.re : ℂ)‖ +
        ‖cmp89Eq245EntireScaledDifference xi (z.re : ℂ)‖ :=
      norm_add_le _ _
    _ ≤ rho * Real.exp rho + |z.re| :=
      add_le_add hvariation hreal
    _ = |z.re| + rho * Real.exp rho := add_comm _ _

end

end YangMills.RG
