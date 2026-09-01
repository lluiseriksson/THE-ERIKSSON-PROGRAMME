/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249CentralStabilizedComplexRadius

/-!
# PRE-VALIDATION: nonvanishing central averaging pair on the CMP89 strip

The complete solution of (2.46) must not accept nonvanishing of its central
row as an unrelated physical hypothesis.  The row is one factor of the named
opposite-momentum pair.  This file gives that pair its own literal strip
window: the sealed vertical variation is smaller than the scale-uniform real
floor `((2/pi)^4)^2`.

This is a scalar reduction.  A later joint-radius producer must make this
window hold together with the existing amplitude, noncentral-gap and
stabilized-denominator windows.

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- Scale-uniform real floor of the four-dimensional central averaging pair. -/
def cmp89Eq249CentralAveragePairLowerConstant : ℝ :=
  ((2 / Real.pi) ^ 4) ^ 2

/-- Literal strip window that preserves the central averaging pair away from
zero. -/
def CMP89Eq249CentralAveragePairComplexWindow (rho : ℝ) : Prop :=
  cmp89Eq249CentralAveragePairVerticalBound rho <
    cmp89Eq249CentralAveragePairLowerConstant

/-- The real floor minus the vertical variation remains below the norm of the
central holomorphic pair. -/
theorem sub_variation_le_norm_cmp89Eq249CentralEntireAveragePair
    {L j : ℕ} [NeZero L] {rho : ℝ} (hrho : 0 ≤ rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho) :
    cmp89Eq249CentralAveragePairLowerConstant -
        cmp89Eq249CentralAveragePairVerticalBound rho ≤
      ‖cmp89Eq249CentralEntireAveragePair 4 L j z‖ := by
  let z0 : Fin 4 → ℂ := cmp89Eq245ComplexMomentumRealSlice z
  let pair := cmp89Eq249CentralEntireAveragePair 4 L j z
  let pair0 := cmp89Eq249CentralEntireAveragePair 4 L j z0
  let floor := cmp89Eq249CentralAveragePairLowerConstant
  let variation := cmp89Eq249CentralAveragePairVerticalBound rho
  have hz0 : z0 = fun mu => (p mu : ℂ) := by
    funext mu
    simp [z0, cmp89Eq245ComplexMomentumRealSlice, hreal mu]
  have hN : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hvariation : ‖pair - pair0‖ ≤ variation := by
    have hraw :=
      norm_cmp89Eq245EntireAverageAmplitude_pair_sub_realSlice_le
        (d := 4) (N := L ^ j) hN hrho himag
    simpa [pair, pair0, z0, cmp89Eq249CentralEntireAveragePair,
      cmp89Eq245EntireAveragePair,
      cmp89Eq249CentralAveragePairVerticalBound, variation] using hraw
  have hamp :=
    pow_two_div_pi_le_norm_cmp89Eq245ComplexAverageAmplitude_inverseScale
      (d := 4) (L := L) (j := j) hp
  have hbase : 0 ≤ (2 / Real.pi) ^ 4 := by positivity
  have hfloorReal :
      floor ≤
        ‖cmp89Eq245ComplexAverageAmplitude
          4 (((L : ℝ) ^ j)⁻¹) p‖ ^ 2 := by
    dsimp [floor, cmp89Eq249CentralAveragePairLowerConstant]
    exact (sq_le_sq₀ hbase (norm_nonneg _)).2 hamp
  have hfloorNorm : floor ≤ ‖pair0‖ := by
    change floor ≤ ‖cmp89Eq249CentralEntireAveragePair 4 L j z0‖
    rw [hz0]
    rw [cmp89Eq249CentralEntireAveragePair_ofReal_eq hp]
    simpa [abs_of_nonneg (sq_nonneg _)] using hfloorReal
  have htriangle : ‖pair0‖ ≤ ‖pair‖ + ‖pair - pair0‖ := by
    calc
      ‖pair0‖ = ‖pair - (pair - pair0)‖ := by
        congr 1
        ring
      _ ≤ ‖pair‖ + ‖pair - pair0‖ := norm_sub_le _ _
  linarith

/-- The literal pair window makes the central holomorphic pair nonzero on the
full four-dimensional strip. -/
theorem cmp89Eq249CentralEntireAveragePair_ne_zero
    {L j : ℕ} [NeZero L] {rho : ℝ} (hrho : 0 ≤ rho)
    (hwindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho) :
    cmp89Eq249CentralEntireAveragePair 4 L j z ≠ 0 := by
  have hlower :=
    sub_variation_le_norm_cmp89Eq249CentralEntireAveragePair
      (L := L) (j := j) hrho hp hreal himag
  have hpos :
      0 < cmp89Eq249CentralAveragePairLowerConstant -
        cmp89Eq249CentralAveragePairVerticalBound rho := by
    simpa [CMP89Eq249CentralAveragePairComplexWindow] using hwindow
  exact norm_pos_iff.mp (hpos.trans_le hlower)

/-- The pair-variation budget is continuous at zero strip width. -/
theorem continuousAt_cmp89Eq249CentralAveragePairVerticalBound :
    ContinuousAt cmp89Eq249CentralAveragePairVerticalBound 0 := by
  unfold cmp89Eq249CentralAveragePairVerticalBound
  fun_prop

/-- The pair-variation budget vanishes at zero strip width. -/
theorem cmp89Eq249CentralAveragePairVerticalBound_zero :
    cmp89Eq249CentralAveragePairVerticalBound 0 = 0 := by
  simp [cmp89Eq249CentralAveragePairVerticalBound]

/-- One positive strip radius satisfies the original three scalar gates and
the central-pair gate simultaneously.  Adding the row requirement therefore
does not make the CMP89 strip regime vacuous. -/
theorem exists_cmp89Eq249CentralStabilizedComplexRadius_with_pair
    {a : ℝ} (ha : 0 < a) :
    ∃ rho : ℝ, 0 < rho ∧
      rho * Real.exp rho ≤ 1 / 6 ∧
      CMP89Eq249UniformNoncentralComplexRadiusCondition rho ∧
      CMP89Eq249CentralStabilizedComplexWindow a rho ∧
      CMP89Eq249CentralAveragePairComplexWindow rho := by
  let amplitude : ℝ → ℝ := fun rho => rho * Real.exp rho
  let gapLhs : ℝ → ℝ := fun rho =>
    let eps := rho * Real.exp rho
    eps * (4 * Real.pi + 4 * eps)
  let gapRhs : ℝ := ((1 / (3 * Real.pi)) ^ 2 * Real.pi ^ 2) / 2
  let variation : ℝ → ℝ := fun rho =>
    cmp89Eq249CentralStabilizedDenominatorVariationBound a rho
  let floor : ℝ := cmp89Eq249CentralStabilizedLowerConstant 4 a
  let pairVariation : ℝ → ℝ :=
    cmp89Eq249CentralAveragePairVerticalBound
  let pairFloor : ℝ := cmp89Eq249CentralAveragePairLowerConstant
  have hfloorPos : 0 < floor := by
    dsimp [floor]
    rw [cmp89Eq249CentralStabilizedLowerConstant]
    positivity
  have hpairFloorPos : 0 < pairFloor := by
    dsimp [pairFloor, cmp89Eq249CentralAveragePairLowerConstant]
    positivity
  have hgapRhsPos : 0 < gapRhs := by
    dsimp [gapRhs]
    positivity
  have hampCont : ContinuousAt amplitude 0 := by
    dsimp [amplitude]
    fun_prop
  have hgapCont : ContinuousAt gapLhs 0 := by
    dsimp [gapLhs]
    fun_prop
  have hvariationCont : ContinuousAt variation 0 := by
    simpa [variation] using
      continuousAt_cmp89Eq249CentralStabilizedDenominatorVariationBound a
  have hpairVariationCont : ContinuousAt pairVariation 0 := by
    simpa [pairVariation] using
      continuousAt_cmp89Eq249CentralAveragePairVerticalBound
  have hampEventually :
      ∀ᶠ rho in nhds (0 : ℝ), amplitude rho < 1 / 6 := by
    exact hampCont.eventually (eventually_lt_nhds (by norm_num [amplitude]))
  have hgapEventually :
      ∀ᶠ rho in nhds (0 : ℝ), gapLhs rho < gapRhs := by
    have hzero : gapLhs 0 = 0 := by simp [gapLhs]
    exact hgapCont.eventually
      (eventually_lt_nhds (by simpa [hzero] using hgapRhsPos))
  have hvariationEventually :
      ∀ᶠ rho in nhds (0 : ℝ), variation rho < floor := by
    have hzero : variation 0 = 0 := by
      simpa [variation] using
        cmp89Eq249CentralStabilizedDenominatorVariationBound_zero a
    exact hvariationCont.eventually
      (eventually_lt_nhds (by simpa [hzero] using hfloorPos))
  have hpairEventually :
      ∀ᶠ rho in nhds (0 : ℝ), pairVariation rho < pairFloor := by
    have hzero : pairVariation 0 = 0 := by
      simpa [pairVariation] using
        cmp89Eq249CentralAveragePairVerticalBound_zero
    exact hpairVariationCont.eventually
      (eventually_lt_nhds (by simpa [hzero] using hpairFloorPos))
  rcases
      (hampEventually.and
        (hgapEventually.and
          (hvariationEventually.and hpairEventually))).exists_gt with
    ⟨rho, hrho, hamp, hgap, hvariation, hpair⟩
  refine ⟨rho, hrho, hamp.le, ?_, ?_, ?_⟩
  · simpa [CMP89Eq249UniformNoncentralComplexRadiusCondition, gapLhs, gapRhs]
      using hgap.le
  · simpa [CMP89Eq249CentralStabilizedComplexWindow, variation, floor]
      using hvariation
  · simpa [CMP89Eq249CentralAveragePairComplexWindow, pairVariation, pairFloor]
      using hpair

end

end YangMills.RG
