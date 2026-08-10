/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116CMP89PhysicalFineNormalizedStabilizedIntegralBound

/-!
# Uniform physical fine-lattice normalized owner bound

This module bounds the exact coefficient of the sealed physical fine-lattice
owner estimate uniformly in localization depth.  It uses only the literal
fine spacing `xi = (L^(depth+1))^(-1)` and the exact cancellation
`(rho*xi)*L^(depth+1) = rho`.

The resulting constant remains the coefficient of the source-shaped Fourier
integral.  The Fourier/operator identification with the printed Holder
difference of `partial_mu^xi (G_j Q_j^*)`, physical `B0`, window 15 and
terminal fields remain open.
-/

namespace YangMills.RG

noncomputable section

/-- Depth-uniform coefficient for the physical fine-lattice normalized owner
bound.  It is not yet the complete physical `B0`. -/
def cmp116CMP89PhysicalFineUniformNormalizedStabilizedIntegralAmplitudeBound
    (a rho : ℝ) : ℝ :=
  (1 + Real.exp rho) * Real.exp (2 * rho) *
    cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho

/-- The depth-uniform physical fine-lattice coefficient is nonnegative. -/
theorem cmp116CMP89PhysicalFineUniformNormalizedStabilizedIntegralAmplitudeBound_nonneg
    {a rho : ℝ} (hrho : 0 ≤ rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho) :
    0 ≤ cmp116CMP89PhysicalFineUniformNormalizedStabilizedIntegralAmplitudeBound
      a rho := by
  rw [cmp116CMP89PhysicalFineUniformNormalizedStabilizedIntegralAmplitudeBound]
  have hmajorant :
      0 ≤ cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho :=
    cmp89Eq251ComplexStabilizedEndpointAmplitudeBound_nonneg hrho hwindow
  positivity

/-- The exact physical fine-lattice coefficient is bounded uniformly in
localization depth.  The endpoint cost is at most `exp rho`; the inverse-scale
block-boundary exponent is at most `2*rho`. -/
theorem cmp116CMP89PhysicalFineNormalizedStabilizedIntegralAmplitudeBound_le_uniform
    {L depth : ℕ} [NeZero L] {a rho : ℝ} (hrho : 0 ≤ rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho) :
    cmp116CMP89PhysicalFineNormalizedStabilizedIntegralAmplitudeBound
        L depth a rho ≤
      cmp116CMP89PhysicalFineUniformNormalizedStabilizedIntegralAmplitudeBound
        a rho := by
  let xi : ℝ := cmp89Eq249FineLatticeSpacing L (depth + 1)
  let rate : ℝ := rho * xi
  have hxi : 0 ≤ xi :=
    (cmp89Eq249FineLatticeSpacing_pos L (depth + 1)).le
  have hrate : 0 ≤ rate := mul_nonneg hrho hxi
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  have hpow : (L : ℝ) ^ (depth + 1) ≠ 0 := pow_ne_zero _ hL
  have hscale : rate * (L ^ (depth + 1) : ℝ) = rho := by
    dsimp [rate, xi, cmp89Eq249FineLatticeSpacing]
    rw [Nat.cast_pow]
    rw [mul_assoc, inv_mul_cancel₀ hpow, mul_one]
  have hpowNat : L ^ (depth + 1) ≠ 0 := pow_ne_zero _ (NeZero.ne L)
  have honePowNat : 1 ≤ L ^ (depth + 1) :=
    Nat.one_le_iff_ne_zero.mpr hpowNat
  have hrate_le : rate ≤ rho := by
    calc
      rate = rate * 1 := by ring
      _ ≤ rate * (L ^ (depth + 1) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hrate
        exact_mod_cast honePowNat
      _ = rho := hscale
  have hboundaryNat :
      2 * (L ^ (depth + 1) - 1) ≤ 2 * L ^ (depth + 1) :=
    Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
  have hboundaryReal :
      ((2 * (L ^ (depth + 1) - 1) : ℕ) : ℝ) ≤
        2 * (L ^ (depth + 1) : ℝ) := by
    exact_mod_cast hboundaryNat
  have hboundary :
      rate * (2 * (L ^ (depth + 1) - 1) : ℕ) ≤ 2 * rho := by
    calc
      rate * (2 * (L ^ (depth + 1) - 1) : ℕ) ≤
          rate * (2 * (L ^ (depth + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_left hboundaryReal hrate
      _ = 2 * (rate * (L ^ (depth + 1) : ℝ)) := by ring
      _ = 2 * rho := by rw [hscale]
  have hedge : Real.exp rate ≤ Real.exp rho :=
    Real.exp_le_exp.mpr hrate_le
  have hboundaryExp :
      Real.exp (rate * (2 * (L ^ (depth + 1) - 1) : ℕ)) ≤
        Real.exp (2 * rho) :=
    Real.exp_le_exp.mpr hboundary
  have hone : 1 + Real.exp rate ≤ 1 + Real.exp rho := by
    linarith [hedge]
  have hmajorant :
      0 ≤ cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho :=
    cmp89Eq251ComplexStabilizedEndpointAmplitudeBound_nonneg hrho hwindow
  have hproduct :
      (1 + Real.exp rate) *
          Real.exp (rate * (2 * (L ^ (depth + 1) - 1) : ℕ)) ≤
        (1 + Real.exp rho) * Real.exp (2 * rho) := by
    exact mul_le_mul hone hboundaryExp
      (Real.exp_pos _).le (by positivity)
  rw [cmp116CMP89PhysicalFineNormalizedStabilizedIntegralAmplitudeBound,
    cmp116CMP89PhysicalFineUniformNormalizedStabilizedIntegralAmplitudeBound]
  dsimp [rate, xi] at hproduct
  exact mul_le_mul_of_nonneg_right hproduct hmajorant

/-- The physical fine-lattice normalized integral has a depth-uniform
coefficient at the fixed owner rate `rho`. -/
theorem norm_cmp116CMP89PhysicalFineNormalizedStabilizedIntegral_le_uniformOwner
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ) {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ‖cmp89Eq249NormalizedFineLatticeStabilizedIntegral
        L (depth + 1) mass a mu
        (cmp116CMP89PhysicalBondHolderDisplacement b)
        (cmp116CMP89PhysicalBondTransportDisplacement b y)‖ ≤
      cmp116CMP89PhysicalFineUniformNormalizedStabilizedIntegralAmplitudeBound
          a rho *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (cmp116BondTarget b))
            (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ)) := by
  have hphysical :=
    norm_cmp116CMP89PhysicalFineNormalizedStabilizedIntegral_le_owner
      depth ha hmassPos hrho hamplitude hradius hwindow hmass mu b y
  have hcoefficient :=
    cmp116CMP89PhysicalFineNormalizedStabilizedIntegralAmplitudeBound_le_uniform
      (L := L) (depth := depth) hrho hwindow
  exact hphysical.trans (mul_le_mul_of_nonneg_right hcoefficient
    (Real.exp_pos _).le)

end

end YangMills.RG
