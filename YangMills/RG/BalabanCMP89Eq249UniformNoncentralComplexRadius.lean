/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249NoncentralComplexGap

/-!
# Uniform scalar radius for noncentral CMP89 aliases

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

The moment-dependent complex-gap theorem is useful only after one common
strip width is shown to satisfy its budget for every nonzero reciprocal
alias. This module reduces that family of inequalities to the nearest-alias
scalar inequality at Euclidean radius `pi`. The reduction uses the literal
conservative budget already sealed in the tree,
`eps * (4 * ‖q‖₂ + 4 * eps)`, with `eps = rho * exp rho`.

This is deliberately separate from the averaging-amplitude condition
`rho * exp rho <= 1/6`. It neither sharpens the opposite-pair variation nor
claims a numerical radius, a stabilized-denominator bound, `B0`, a contour
shift, or a regional-Green estimate.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Exact nearest-alias scalar condition sufficient for the conservative
four-dimensional noncentral complex-gap budget. -/
def CMP89Eq249UniformNoncentralComplexRadiusCondition (rho : ℝ) : Prop :=
  let eps := rho * Real.exp rho
  eps * (4 * Real.pi + 4 * eps) ≤
    ((1 / (3 * Real.pi)) ^ 2 * Real.pi ^ 2) / 2

/-- Once the scalar condition holds at radius `pi`, it holds at every larger
Euclidean momentum. No alias-cardinality or alias-diameter bound enters. -/
theorem cmp89Eq249NoncentralComplexGapBudget_le_of_uniformRadiusCondition
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {q : Fin 4 → ℝ}
    (hq : Real.pi ≤ cmp89Eq251EuclideanNorm q) :
    cmp89Eq249NoncentralComplexGapBudget rho q ≤
      ((1 / (3 * Real.pi)) ^ 2 * cmp89Eq251MomentumSquare q) / 2 := by
  let eps : ℝ := rho * Real.exp rho
  let radius : ℝ := cmp89Eq251EuclideanNorm q
  let coeff : ℝ := (1 / (3 * Real.pi)) ^ 2
  have heps : 0 ≤ eps := mul_nonneg hrho (Real.exp_pos rho).le
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcoeff : 0 ≤ coeff := sq_nonneg _
  have hbase :
      eps * (4 * Real.pi + 4 * eps) ≤
        coeff * Real.pi ^ 2 / 2 := by
    simpa [CMP89Eq249UniformNoncentralComplexRadiusCondition, eps, coeff]
      using hradius
  have hepsSlope : 4 * eps ≤ coeff * Real.pi / 2 := by
    have hmul :
        (4 * eps) * Real.pi ≤ (coeff * Real.pi / 2) * Real.pi := by
      calc
        (4 * eps) * Real.pi ≤ eps * (4 * Real.pi + 4 * eps) := by
          nlinarith [sq_nonneg eps]
        _ ≤ coeff * Real.pi ^ 2 / 2 := hbase
        _ = (coeff * Real.pi / 2) * Real.pi := by ring
    exact le_of_mul_le_mul_right hmul hpi
  have hradiusPi : Real.pi ≤ radius := by simpa [radius] using hq
  have hincrement :
      4 * eps * (radius - Real.pi) ≤
        (coeff * Real.pi / 2) * (radius - Real.pi) :=
    mul_le_mul_of_nonneg_right hepsSlope (sub_nonneg.mpr hradiusPi)
  have hpiRadius : Real.pi * radius ≤ radius ^ 2 := by
    have hradiusNonneg : 0 ≤ radius := hpi.le.trans hradiusPi
    nlinarith
  have hradial :
      eps * (4 * radius + 4 * eps) ≤ coeff * radius ^ 2 / 2 := by
    calc
      eps * (4 * radius + 4 * eps) =
          eps * (4 * Real.pi + 4 * eps) +
            4 * eps * (radius - Real.pi) := by ring
      _ ≤ coeff * Real.pi ^ 2 / 2 +
          (coeff * Real.pi / 2) * (radius - Real.pi) :=
        add_le_add hbase hincrement
      _ = coeff * (Real.pi * radius) / 2 := by ring
      _ ≤ coeff * radius ^ 2 / 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpiRadius hcoeff) (by norm_num)
  have hsquare := sq_cmp89Eq251EuclideanNorm q
  simpa [cmp89Eq249NoncentralComplexGapBudget, eps, radius, coeff, hsquare]
    using hradial

/-- The single scalar radius condition discharges the moment-dependent budget
for every nonzero printed alias. -/
theorem half_momentum_gap_le_norm_cmp89Eq245EntireScaledLaplacianSymbol_of_uniformRadius
    {N : ℕ} (hN : 0 < N) {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 N) (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu + 2 * Real.pi * (m mu : ℝ))
    (himag : ∀ mu, |(z mu).im| ≤ rho) :
    ((1 / (3 * Real.pi)) ^ 2 *
        cmp89Eq251MomentumSquare
          (fun mu => p mu + 2 * Real.pi * (m mu : ℝ))) / 2 ≤
      ‖cmp89Eq245EntireScaledLaplacianSymbol
        4 (N : ℝ)⁻¹ mass z‖ := by
  apply half_momentum_gap_le_norm_cmp89Eq245EntireScaledLaplacianSymbol
    hN hrho hm hp hreal himag
  exact cmp89Eq249NoncentralComplexGapBudget_le_of_uniformRadiusCondition
    hrho hradius (pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp)

end

end YangMills.RG
