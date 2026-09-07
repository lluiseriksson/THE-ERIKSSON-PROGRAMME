/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePhysicalCoordinateDictionary
import YangMills.RG.BalabanCMP116Eq226GaussianCardinality

/-!
# Carrier-linear cost of the physical restricted outer boundary

The integrated source boundary contains a restricted determinant, the
rank-localized source determinant, and the exact outer trace exponential.
This module absorbs all three into one explicit exponential linear in
`Z₀.card`.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Number of physical scalar coordinates per source localization block. -/
def cmp116SourcePhysicalCoordinateRate (M Nc : ℕ) : ℕ :=
  (M ^ 4 * 4) * (Nc ^ 2 - 1)

/-- Per-block logarithmic cost of the rank-localized source determinant. -/
noncomputable def cmp116SourcePhysicalRootCardinalityRate
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (root : PhysicalEndomorphism M Q Nc) (alpha : ℝ) : ℝ :=
  (((cmp116SourcePhysicalCoordinateRate M Nc : ℕ) : ℝ) / 2) *
    (-Real.log
      (1 - alpha *
        (@norm
          (Matrix
            (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
            (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℝ)
          Matrix.instL2OpNormedAddCommGroup.toNorm
          (cmp116PhysicalEndomorphismRealMatrix root)) ^ 2))

/-- The exact uniform trace cost is linear in the number of restricted
Cauchy coordinates. -/
theorem cmp116SourceRestrictedUniformR1TraceCost_eq_card_mul
    (q M Nc Delta : ℕ)
    (radius Rweak rate Ahead rho multiplierBound : ℝ) :
    cmp116SourceRestrictedUniformR1TraceCost
        q M Nc Delta radius Rweak rate Ahead rho multiplierBound =
      (q : ℝ) *
        cmp116SourceRestrictedUniformR1TraceCost
          1 M Nc Delta radius Rweak rate Ahead rho multiplierBound := by
  unfold cmp116SourceRestrictedUniformR1TraceCost
  dsimp only
  ring

/-- Restricting the Cauchy carrier to `Z₀` turns the exact trace cost into a
per-`Z₀`-block cost. -/
theorem cmp116SourceRestrictedUniformR1TraceCost_le_card_mul
    {q M Q Nc Delta : ℕ}
    (carrier Z0 : Finset (FinBox 4 (2 * Q)))
    (e : Fin q ≃ ↥carrier)
    (hcarrier : carrier ⊆ Z0)
    {radius Rweak rate Ahead rho multiplierBound : ℝ}
    (hmultiplier : 0 ≤ multiplierBound)
    (hradius : 0 ≤ radius) (hAhead : 0 ≤ Ahead)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1) :
    cmp116SourceRestrictedUniformR1TraceCost
        q M Nc Delta radius Rweak rate Ahead rho multiplierBound ≤
      (Z0.card : ℝ) *
        cmp116SourceRestrictedUniformR1TraceCost
          1 M Nc Delta radius Rweak rate Ahead rho multiplierBound := by
  have hqcard : q = carrier.card := by
    simpa using Fintype.card_congr e
  have hcard : q ≤ Z0.card := by
    rw [hqcard]
    exact Finset.card_le_card hcarrier
  rw [cmp116SourceRestrictedUniformR1TraceCost_eq_card_mul]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hcard
  · exact
      cmp116SourceRestrictedUniformR1TraceCost_nonneg
        1 M Nc Delta hradius hAhead hgeom hmultiplier

/-- The localized determinant in the source-energy prefactor has one
explicit cost per localization block. -/
theorem cmp116Eq225LocalizedSourceEnergyPrefactor_zero_le_exp_card_physical
    {M Q Nc L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (root : PhysicalEndomorphism M Q Nc)
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (hsmall :
      alpha *
        (@norm
          (Matrix
            (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
            (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℝ)
          Matrix.instL2OpNormedAddCommGroup.toNorm
          (cmp116PhysicalEndomorphismRealMatrix root)) ^ 2 < 1) :
    cmp116Eq225LocalizedSourceEnergyPrefactor
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z0)
        (cmp116PhysicalEndomorphismRealMatrix root) alpha 0 ≤
      Real.exp
        (cmp116SourcePhysicalRootCardinalityRate root alpha *
          (Z0.card : ℝ)) := by
  let rootNorm :=
    @norm
      (Matrix
        (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
        (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℝ)
      Matrix.instL2OpNormedAddCommGroup.toNorm
      (cmp116PhysicalEndomorphismRealMatrix root)
  let beta := alpha * rootNorm ^ 2 / 2
  have hbeta0 : 0 ≤ beta := by
    dsimp [beta, rootNorm]
    positivity
  have hbeta : 2 * beta < 1 := by
    dsimp [beta, rootNorm]
    linarith
  have hn :
      (cmp116SourcePhysicalLocalizedCoordinates Dict Z0).card ≤
        cmp116SourcePhysicalCoordinateRate M Nc * Z0.card := by
    calc
      (cmp116SourcePhysicalLocalizedCoordinates Dict Z0).card ≤
          ((Z0.card * M ^ 4) * 4) * (Nc ^ 2 - 1) :=
        card_cmp116SourcePhysicalLocalizedCoordinates_le Dict Z0
      _ = cmp116SourcePhysicalCoordinateRate M Nc * Z0.card := by
        simp [cmp116SourcePhysicalCoordinateRate]
        ring
  have hfactor :=
    inv_sqrt_one_sub_two_mul_pow_le_exp_card beta
      (cmp116SourcePhysicalLocalizedCoordinates Dict Z0).card
      (cmp116SourcePhysicalCoordinateRate M Nc) Z0.card
      hbeta0 hbeta hn
  have hbase :
      1 - 2 * beta = 1 - alpha * rootNorm ^ 2 := by
    dsimp [beta]
    ring
  rw [hbase] at hfactor
  unfold cmp116Eq225LocalizedSourceEnergyPrefactor
  simp only [mul_zero, Real.exp_zero, mul_one]
  simpa [cmp116SourcePhysicalRootCardinalityRate, beta, rootNorm] using hfactor

/-- Complete per-block cost of the integrated physical outer boundary. -/
noncomputable def cmp116SourceRestrictedPhysicalOuterPerCarrierCost
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ)
    (radius rate Ahead rho alpha sourceRate qBound determinantCost : ℝ) : ℝ :=
  let multiplier :=
    cmp116SourcePi4PhysicalComplexR1TraceMultiplierBound
      K root hc hmass hK Z0 Delta
        Ahead rho rate radius (1 + radius)
  let tracePerCarrier :=
    cmp116SourceRestrictedUniformR1TraceCost
      1 M Nc Delta radius (1 + radius) rate Ahead rho multiplier
  let beta :=
    cmp116Eq225SourceCoefficient
      (cmp116PhysicalEndomorphismRealMatrix root) alpha * sourceRate
  determinantCost +
    cmp116SourcePhysicalRootCardinalityRate root alpha +
    ((tracePerCarrier +
      2 * |beta| * (cmp116SourcePhysicalCoordinateRate M Nc : ℝ)) /
        (1 - qBound)) / 2

set_option maxHeartbeats 4000000 in
/-- The complete source outer boundary is uniformly polymer-local: its cost
is one explicit exponential linear in `Z₀.card`. -/
theorem cmp116SourceRestrictedPhysicalOuterBoundary_le_exp_card
    {nDelta M Q Nc Delta L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero L] [NeZero lieDim]
    (carrier Z0 : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥carrier)
    (hcarrier : carrier ⊆ Z0)
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
    let S := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
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
        (cmp116SourceRestrictedPhysicalOuterPerCarrierCost
          K root hc hmass hK Z0 Delta radius rate Ahead rho
            alpha sourceRate qBound determinantCost *
          (Z0.card : ℝ)) := by
  dsimp only
  let S := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
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
  have htrace :
      traceCost ≤ (Z0.card : ℝ) * tracePerCarrier := by
    dsimp [traceCost, tracePerCarrier]
    exact
      cmp116SourceRestrictedUniformR1TraceCost_le_card_mul
        carrier Z0 e hcarrier hmultiplier hradius hAhead hgeom
  have hScardNat :
      S.card ≤ cmp116SourcePhysicalCoordinateRate M Nc * Z0.card := by
    dsimp [S]
    calc
      (cmp116SourcePhysicalLocalizedCoordinates Dict Z0).card ≤
          ((Z0.card * M ^ 4) * 4) * (Nc ^ 2 - 1) :=
        card_cmp116SourcePhysicalLocalizedCoordinates_le Dict Z0
      _ = cmp116SourcePhysicalCoordinateRate M Nc * Z0.card := by
        simp [cmp116SourcePhysicalCoordinateRate]
        ring
  have hScard :
      (S.card : ℝ) ≤
        (cmp116SourcePhysicalCoordinateRate M Nc : ℝ) *
          (Z0.card : ℝ) := by
    exact_mod_cast hScardNat
  have hprefactor :
      cmp116Eq225LocalizedSourceEnergyPrefactor S
          (cmp116PhysicalEndomorphismRealMatrix root) alpha 0 ≤
        Real.exp (rootCost * (Z0.card : ℝ)) := by
    dsimp [S, rootCost]
    exact
      cmp116Eq225LocalizedSourceEnergyPrefactor_zero_le_exp_card_physical
        Dict Z0 root alpha halpha hrootSmall
  have htraceExponent :
      Real.exp
          (((traceCost + 2 * |beta| * (S.card : ℝ)) /
            (1 - qBound)) / 2) ≤
        Real.exp
          ((((tracePerCarrier +
              2 * |beta| *
                (cmp116SourcePhysicalCoordinateRate M Nc : ℝ)) /
              (1 - qBound)) / 2) *
            (Z0.card : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hdenom : 0 < 1 - qBound := sub_pos.mpr hq1
    have hsourceCard :
        2 * |beta| * (S.card : ℝ) ≤
          2 * |beta| *
            ((cmp116SourcePhysicalCoordinateRate M Nc : ℝ) *
              (Z0.card : ℝ)) := by
      gcongr
    calc
      ((traceCost + 2 * |beta| * (S.card : ℝ)) /
          (1 - qBound)) / 2 ≤
        (((Z0.card : ℝ) * tracePerCarrier +
            2 * |beta| *
              ((cmp116SourcePhysicalCoordinateRate M Nc : ℝ) *
                (Z0.card : ℝ))) /
          (1 - qBound)) / 2 := by
            gcongr
      _ =
        (((tracePerCarrier +
            2 * |beta| *
              (cmp116SourcePhysicalCoordinateRate M Nc : ℝ)) /
            (1 - qBound)) / 2) *
          (Z0.card : ℝ) := by ring
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
      (Real.exp (determinantCost * (Z0.card : ℝ)) *
        Real.exp (rootCost * (Z0.card : ℝ))) *
      Real.exp
        ((((tracePerCarrier +
            2 * |beta| *
              (cmp116SourcePhysicalCoordinateRate M Nc : ℝ)) /
            (1 - qBound)) / 2) *
          (Z0.card : ℝ)) := by
            gcongr
    _ = Real.exp
        (cmp116SourceRestrictedPhysicalOuterPerCarrierCost
          K root hc hmass hK Z0 Delta radius rate Ahead rho
            alpha sourceRate qBound determinantCost *
          (Z0.card : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [cmp116SourceRestrictedPhysicalOuterPerCarrierCost,
        multiplier, tracePerCarrier, beta, rootCost]
      ring

end

end YangMills.RG
