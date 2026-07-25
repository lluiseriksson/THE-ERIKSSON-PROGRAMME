/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedPhysicalOuterCardinality

/-!
# Mixed-carrier cost of the conditioned physical outer boundary

In the source formula, `Z₀` controls the inner covariance and the contour
determinant, whereas the outer product Gaussian is restricted to the activity
carrier `Z`.  This module absorbs the resulting mixed expression into one
explicit exponential linear in `Z.card`, assuming the physical inclusion
`Z₀ ⊆ Z`.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Complete per-outer-block cost for the conditioned source boundary.
The absolute value on the determinant coefficient makes the transport from
`Z₀` to `Z` independent of a separately supplied sign certificate. -/
noncomputable def
    cmp116SourceRestrictedConditionedPhysicalOuterPerCarrierCost
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ)
    (radius rate Ahead rho alpha sourceRate qBound determinantCost : ℝ) : ℝ :=
  cmp116SourceRestrictedPhysicalOuterPerCarrierCost
    K root hc hmass hK Z0 Delta radius rate Ahead rho
      alpha sourceRate qBound |determinantCost|

set_option maxHeartbeats 5000000 in
/-- The mixed conditioned boundary is polymer-local on the literal outer
carrier `Z`.  No ambient cardinality and no sign hypothesis for the
determinant cost occur in the statement. -/
theorem
    cmp116SourceRestrictedConditionedPhysicalOuterBoundary_le_exp_card
    {nDelta M Q Nc Delta L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero L] [NeZero lieDim]
    (carrier Z0 Z : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥carrier)
    (hcarrierZ0 : carrier ⊆ Z0)
    (hZ0Z : Z0 ⊆ Z)
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {radius rate Ahead rho alpha sourceRate qBound determinantCost : ℝ}
    (hradius : 0 ≤ radius) (hAhead : 0 ≤ Ahead)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius (1 + radius) < 1)
    (hneumannTranspose :
      cmp116SourcePi4PhysicalComplexTransposeRelativeDefectBound
        K Delta Ahead rho rate radius (1 + radius) < 1)
    (halpha : 0 ≤ alpha)
    (hrootSmall :
      alpha *
        (@norm
          (Matrix
            (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
            (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℝ)
          Matrix.instL2OpNormedAddCommGroup.toNorm
          (cmp116PhysicalEndomorphismRealMatrix root)) ^ 2 < 1)
    (hq1 : qBound < 1) :
    let S := cmp116SourcePhysicalLocalizedCoordinates Dict Z
    let multiplier :=
      cmp116SourcePi4PhysicalComplexR1TraceMultiplierBound
        K root hc hmass hK Z0 Delta
          Ahead rho rate radius (1 + radius)
    let traceCost :=
      cmp116SourceRestrictedUniformR1TraceCost
        nDelta M Nc Delta radius (1 + radius) rate Ahead rho multiplier
    let beta :=
      cmp116Eq225SourceCoefficient
        (cmp116PhysicalEndomorphismRealMatrix root) alpha * sourceRate
    (Real.exp (determinantCost * (Z0.card : ℝ)) *
        cmp116Eq225LocalizedSourceEnergyPrefactor S
          (cmp116PhysicalEndomorphismRealMatrix root) alpha 0) *
      Real.exp
        (((traceCost + 2 * |beta| * (S.card : ℝ)) /
          (1 - qBound)) / 2) ≤
      Real.exp
        (cmp116SourceRestrictedConditionedPhysicalOuterPerCarrierCost
          K root hc hmass hK Z0 Delta radius rate Ahead rho
            alpha sourceRate qBound determinantCost *
          (Z.card : ℝ)) := by
  dsimp only
  let S := cmp116SourcePhysicalLocalizedCoordinates Dict Z
  let multiplier :=
    cmp116SourcePi4PhysicalComplexR1TraceMultiplierBound
      K root hc hmass hK Z0 Delta
        Ahead rho rate radius (1 + radius)
  let traceCost :=
    cmp116SourceRestrictedUniformR1TraceCost
      nDelta M Nc Delta radius (1 + radius) rate Ahead rho multiplier
  let tracePerCarrier :=
    cmp116SourceRestrictedUniformR1TraceCost
      1 M Nc Delta radius (1 + radius) rate Ahead rho multiplier
  let beta :=
    cmp116Eq225SourceCoefficient
      (cmp116PhysicalEndomorphismRealMatrix root) alpha * sourceRate
  let rootCost := cmp116SourcePhysicalRootCardinalityRate root alpha
  have hZcardNat : Z0.card ≤ Z.card :=
    Finset.card_le_card hZ0Z
  have hZcard : (Z0.card : ℝ) ≤ (Z.card : ℝ) := by
    exact_mod_cast hZcardNat
  have hmultiplier : 0 ≤ multiplier := by
    dsimp [multiplier]
    exact
      cmp116SourcePi4PhysicalComplexR1TraceMultiplierBound_nonneg
        K root hc hmass hK Z0 Delta hAhead hradius hgeom
          hneumann hneumannTranspose
  have htracePerCarrier : 0 ≤ tracePerCarrier := by
    dsimp [tracePerCarrier]
    exact
      cmp116SourceRestrictedUniformR1TraceCost_nonneg
        1 M Nc Delta hradius hAhead hgeom hmultiplier
  have htraceZ0 :
      traceCost ≤ (Z0.card : ℝ) * tracePerCarrier := by
    dsimp [traceCost, tracePerCarrier]
    exact
      cmp116SourceRestrictedUniformR1TraceCost_le_card_mul
        carrier Z0 e hcarrierZ0 hmultiplier hradius hAhead hgeom
  have htrace :
      traceCost ≤ (Z.card : ℝ) * tracePerCarrier :=
    htraceZ0.trans
      (mul_le_mul_of_nonneg_right hZcard htracePerCarrier)
  have hScardNat :
      S.card ≤ cmp116SourcePhysicalCoordinateRate M Nc * Z.card := by
    dsimp [S]
    calc
      (cmp116SourcePhysicalLocalizedCoordinates Dict Z).card ≤
          ((Z.card * M ^ 4) * 4) * (Nc ^ 2 - 1) :=
        card_cmp116SourcePhysicalLocalizedCoordinates_le Dict Z
      _ = cmp116SourcePhysicalCoordinateRate M Nc * Z.card := by
        simp [cmp116SourcePhysicalCoordinateRate]
        ring
  have hScard :
      (S.card : ℝ) ≤
        (cmp116SourcePhysicalCoordinateRate M Nc : ℝ) *
          (Z.card : ℝ) := by
    exact_mod_cast hScardNat
  have hprefactor :
      cmp116Eq225LocalizedSourceEnergyPrefactor S
          (cmp116PhysicalEndomorphismRealMatrix root) alpha 0 ≤
        Real.exp (rootCost * (Z.card : ℝ)) := by
    dsimp [S, rootCost]
    exact
      cmp116Eq225LocalizedSourceEnergyPrefactor_zero_le_exp_card_physical
        Dict Z root alpha halpha hrootSmall
  have hdet :
      Real.exp (determinantCost * (Z0.card : ℝ)) ≤
        Real.exp (|determinantCost| * (Z.card : ℝ)) := by
    apply Real.exp_le_exp.mpr
    calc
      determinantCost * (Z0.card : ℝ) ≤
          |determinantCost| * (Z0.card : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self determinantCost)
          (Nat.cast_nonneg _)
      _ ≤ |determinantCost| * (Z.card : ℝ) :=
        mul_le_mul_of_nonneg_left hZcard (abs_nonneg _)
  have htraceExponent :
      Real.exp
          (((traceCost + 2 * |beta| * (S.card : ℝ)) /
            (1 - qBound)) / 2) ≤
        Real.exp
          ((((tracePerCarrier +
              2 * |beta| *
                (cmp116SourcePhysicalCoordinateRate M Nc : ℝ)) /
              (1 - qBound)) / 2) *
            (Z.card : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hdenom : 0 < 1 - qBound := sub_pos.mpr hq1
    have hsourceCard :
        2 * |beta| * (S.card : ℝ) ≤
          2 * |beta| *
            ((cmp116SourcePhysicalCoordinateRate M Nc : ℝ) *
              (Z.card : ℝ)) := by
      gcongr
    calc
      ((traceCost + 2 * |beta| * (S.card : ℝ)) /
          (1 - qBound)) / 2 ≤
        (((Z.card : ℝ) * tracePerCarrier +
            2 * |beta| *
              ((cmp116SourcePhysicalCoordinateRate M Nc : ℝ) *
                (Z.card : ℝ))) /
          (1 - qBound)) / 2 := by
            gcongr
      _ =
        (((tracePerCarrier +
            2 * |beta| *
              (cmp116SourcePhysicalCoordinateRate M Nc : ℝ)) /
            (1 - qBound)) / 2) *
          (Z.card : ℝ) := by ring
  have hdetNonneg :
      0 ≤ Real.exp (determinantCost * (Z0.card : ℝ)) :=
    Real.exp_nonneg _
  have hprefactorNonneg :
      0 ≤ cmp116Eq225LocalizedSourceEnergyPrefactor S
        (cmp116PhysicalEndomorphismRealMatrix root) alpha 0 := by
    unfold cmp116Eq225LocalizedSourceEnergyPrefactor
    positivity
  calc
    (Real.exp (determinantCost * (Z0.card : ℝ)) *
        cmp116Eq225LocalizedSourceEnergyPrefactor S
          (cmp116PhysicalEndomorphismRealMatrix root) alpha 0) *
      Real.exp
        (((traceCost + 2 * |beta| * (S.card : ℝ)) /
          (1 - qBound)) / 2) ≤
      (Real.exp (|determinantCost| * (Z.card : ℝ)) *
        Real.exp (rootCost * (Z.card : ℝ))) *
      Real.exp
        ((((tracePerCarrier +
            2 * |beta| *
              (cmp116SourcePhysicalCoordinateRate M Nc : ℝ)) /
            (1 - qBound)) / 2) *
          (Z.card : ℝ)) := by
            gcongr
    _ = Real.exp
        (cmp116SourceRestrictedConditionedPhysicalOuterPerCarrierCost
          K root hc hmass hK Z0 Delta radius rate Ahead rho
            alpha sourceRate qBound determinantCost *
          (Z.card : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [cmp116SourceRestrictedConditionedPhysicalOuterPerCarrierCost,
        cmp116SourceRestrictedPhysicalOuterPerCarrierCost,
        multiplier, tracePerCarrier, beta, rootCost]
      ring

end

end YangMills.RG
