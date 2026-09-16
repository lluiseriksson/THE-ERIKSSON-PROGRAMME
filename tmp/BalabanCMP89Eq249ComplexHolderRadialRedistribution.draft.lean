/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251ComplexNoncentralEndpointQuotientBound
import YangMills.RG.BalabanCMP89Eq251AliasWeightExponentMonotonicity

/-!
# PRE-VALIDATION: general-alpha complex Holder radial redistribution

This H2b support source is a static draft. Its `.olean` has not been
materialized and none of its declarations has been compiler-verified.

The global strip phase quotient contributes the two radial branches
`||q_m||^alpha` and `rho`; the sealed endpoint quotient contributes
`||q_m||^(-1) * aliasWeight(1,m)`. This module redistributes both branches to
the one source weight with exponent `1 + (1-alpha)/4`. The vertical branch is
first redistributed at `alpha = 0` and then transported pointwise by exponent
monotonicity. No alias cardinality or second summation is introduced.

This is deliberately only radial algebra. It does not remove or bound the
literal endpoint transport phase, prove a complete alias-summand estimate,
sum aliases, construct `B0`, attain window 15, discharge a terminal field or
inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Literal H2b radial constant before alias summation. -/
def cmp89Eq249ComplexHolderNoncentralRadialConstant_draft
    (rho alpha : ℝ) : ℝ :=
  2 * Real.exp (2 * rho) *
    cmp89Eq251ComplexNoncentralEndpointRadialConstant rho *
      (3 ^ (1 - alpha) + 3 * rho)

/-- The two radial branches land on one literal general-alpha source weight.
The factors `3^(1-alpha)` and `3*rho` remain separate and visible. -/
theorem cmp89Eq249_complexHolderRadialBranches_le_sourceWeight_draft
    {alpha rho : ℝ} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hrho : 0 ≤ rho) {m : Fin 4 → ℤ} (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    let q : Fin 4 → ℝ :=
      fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
    (cmp89Eq251EuclideanNorm q ^ alpha + rho) *
        (cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) ≤
      (3 ^ (1 - alpha) + 3 * rho) *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 alpha) m := by
  dsimp only
  let q : Fin 4 → ℝ :=
    fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
  let sourceWeight :=
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 alpha) m
  have hQ : 0 < cmp89Eq251EuclideanNorm q :=
    Real.pi_pos.trans_le (pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp)
  have hpow :
      cmp89Eq251EuclideanNorm q ^ alpha *
          cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) =
        cmp89Eq251EuclideanNorm q ^ (alpha - 1) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  have hsource :
      cmp89Eq251EuclideanNorm q ^ (alpha - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m ≤
        3 ^ (1 - alpha) * sourceWeight := by
    simpa only [q, sourceWeight] using
      (cmp89Eq251EuclideanNorm_rpow_mul_aliasWeight_le_sourceWeight
        (d := 4) (alpha := alpha) (by norm_num) halpha1 hm0 hp)
  have hverticalZero :
      cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m ≤
        3 ^ (1 - (0 : ℝ)) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 0) m := by
    simpa only [q] using
      (cmp89Eq251EuclideanNorm_rpow_mul_aliasWeight_le_sourceWeight
        (d := 4) (alpha := (0 : ℝ)) (by norm_num) (by norm_num) hm0 hp)
  have hweight :
      cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 0) m ≤ sourceWeight := by
    simpa only [sourceWeight] using
      (cmp89Eq251AliasWeight_alpha_zero_le_alpha_draft
        (d := 4) (by norm_num) halpha0 m)
  have hvertical :
      cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m ≤
        3 * sourceWeight := by
    calc
      cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m ≤
        3 ^ (1 - (0 : ℝ)) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 0) m := hverticalZero
      _ = 3 * cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 0) m := by norm_num
      _ ≤ 3 * sourceWeight :=
        mul_le_mul_of_nonneg_left hweight (by norm_num)
  calc
    (cmp89Eq251EuclideanNorm q ^ alpha + rho) *
        (cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) =
      (cmp89Eq251EuclideanNorm q ^ alpha *
          cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1)) *
          cmp89Eq251MultidimensionalAliasWeight 1 m +
        rho * (cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := by ring
    _ = cmp89Eq251EuclideanNorm q ^ (alpha - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m +
        rho * (cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := by rw [hpow]
    _ ≤ 3 ^ (1 - alpha) * sourceWeight + rho * (3 * sourceWeight) :=
      add_le_add hsource (mul_le_mul_of_nonneg_left hvertical hrho)
    _ = (3 ^ (1 - alpha) + 3 * rho) * sourceWeight := by ring

/-- The exact scalar product of the H2a phase majorant and the sealed
noncentral radial endpoint majorant has the advertised single-weight bound.
No phase or endpoint object is replaced by this scalar helper. -/
theorem cmp89Eq249_complexHolderPhase_mul_endpointRadial_le_sourceWeight_draft
    {alpha rho : ℝ} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hrho : 0 ≤ rho) {m : Fin 4 → ℤ} (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    let q : Fin 4 → ℝ :=
      fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
    (2 * Real.exp (2 * rho) *
        (cmp89Eq251EuclideanNorm q ^ alpha + rho)) *
      (cmp89Eq251ComplexNoncentralEndpointRadialConstant rho *
        (cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m)) ≤
      cmp89Eq249ComplexHolderNoncentralRadialConstant_draft rho alpha *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 alpha) m := by
  dsimp only
  let q : Fin 4 → ℝ :=
    fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
  let radialConstant :=
    cmp89Eq251ComplexNoncentralEndpointRadialConstant rho
  let sourceWeight :=
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 alpha) m
  have hbranches :=
    cmp89Eq249_complexHolderRadialBranches_le_sourceWeight_draft
      halpha0 halpha1 hrho hm0 hp
  have hconstant : 0 ≤ 2 * Real.exp (2 * rho) * radialConstant := by
    dsimp [radialConstant, cmp89Eq251ComplexNoncentralEndpointRadialConstant,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  calc
    (2 * Real.exp (2 * rho) *
        (cmp89Eq251EuclideanNorm q ^ alpha + rho)) *
      (radialConstant *
        (cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m)) =
      (2 * Real.exp (2 * rho) * radialConstant) *
        ((cmp89Eq251EuclideanNorm q ^ alpha + rho) *
          (cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
            cmp89Eq251MultidimensionalAliasWeight 1 m)) := by ring
    _ ≤ (2 * Real.exp (2 * rho) * radialConstant) *
        ((3 ^ (1 - alpha) + 3 * rho) * sourceWeight) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [q, sourceWeight] using hbranches) hconstant
    _ = cmp89Eq249ComplexHolderNoncentralRadialConstant_draft rho alpha *
        sourceWeight := by
      rw [cmp89Eq249ComplexHolderNoncentralRadialConstant_draft]
      ring

end

end YangMills.RG
