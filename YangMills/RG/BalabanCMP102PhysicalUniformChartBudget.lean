/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalChartBudget
import YangMills.RG.BalabanCMP102PhysicalSourceBudgetEnvelope

/-!
# Uniform scalar production of the CMP102 physical chart

One source-sup bound and explicit scalar envelope inequalities now generate
the complete logarithmic chart package.  In particular, no pointwise
near-identity or no-winding statement is supplied to the constructor.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- A common source-norm envelope produces the full physical nonlinear
chart at a given field. -/
noncomputable def cmp102PhysicalNonlinearChartBudget_of_envelope
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (R radius r s : ℝ)
    (hA : cmp98SourceFieldSupNorm A ≤ R)
    (hone : 1 < radius)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hs1 : s < 1)
    (hrNoWinding : (Nc : ℝ) * (r / (1 - r)) < 2 * Real.pi)
    (hsNoWinding : (Nc : ℝ) * (s / (1 - s)) < 2 * Real.pi)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : ∀ t, |t| < radius → |t| * R ≤ 1 / 2)
    (hlocal : ∀ t, |t| < radius →
      1 / 3 + cmp102PhysicalContourDisplacementEnvelope d M R t ≤ r)
    (hrelative : ∀ t, |t| < radius →
      cmp102PhysicalBlockDisplacementEnvelope d M R t r ≤ s) :
    CMP102PhysicalNonlinearChartBudget U A where
  radius := radius
  one_lt_radius := hone
  localNoWinding :=
    { δ := r
      δ_lt_one := hr1
      noWinding := hrNoWinding }
  relativeNoWinding :=
    { δ := s
      δ_lt_one := hs1
      noWinding := hsNoWinding }
  base := hbase
  small := by
    intro t ht
    exact
      (mul_le_mul_of_nonneg_left hA (abs_nonneg t)).trans
        (hsmall t ht)
  localRadius := by
    intro t ht
    exact
      (add_le_add (le_refl (1 / 3 : ℝ))
        (cmp98SourceContourDisplacementBudget_le_envelope A R t hA)).trans
        (hlocal t ht)
  relativeRadius := by
    intro t ht
    exact
      (cmp98SourcePhysicalBlockDisplacementBudget_le_envelope
        A R t r hr0 hA).trans
        (hrelative t ht)

@[simp]
theorem cmp102PhysicalNonlinearChartBudget_of_envelope_localRadius
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (R radius r s : ℝ)
    (hA hone hr0 hr1 hs1 hrNoWinding hsNoWinding hbase hsmall
      hlocal hrelative) :
    (cmp102PhysicalNonlinearChartBudget_of_envelope
      U A R radius r s hA hone hr0 hr1 hs1
      hrNoWinding hsNoWinding hbase hsmall hlocal hrelative
    ).localNoWinding.δ = r := rfl

@[simp]
theorem cmp102PhysicalNonlinearChartBudget_of_envelope_relativeRadius
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (R radius r s : ℝ)
    (hA hone hr0 hr1 hs1 hrNoWinding hsNoWinding hbase hsmall
      hlocal hrelative) :
    (cmp102PhysicalNonlinearChartBudget_of_envelope
      U A R radius r s hA hone hr0 hr1 hs1
      hrNoWinding hsNoWinding hbase hsmall hlocal hrelative
    ).relativeNoWinding.δ = s := rfl

end

end YangMills.RG
