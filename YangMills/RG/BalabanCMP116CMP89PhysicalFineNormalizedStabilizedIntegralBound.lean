/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249FineLatticeNormalizedStabilizedIntegralRecombination
import YangMills.RG.BalabanCMP116CMP89PhysicalOwnerExponentialTransport
import YangMills.RG.BalabanCMP116CMP89PhysicalNormalizedStabilizedIntegralBound

/-!
# Physical fine-lattice normalized integral owner bound

This module installs the already sealed physical-bond and fine-site
displacement dictionaries in the source-faithful normalized fine-lattice
recombination. At physical spacing `(L^(depth+1))^(-1)`, the inverse-scale
owner bridge turns the fine rate into the exact fixed owner rate `rho`.

The unit-edge cost `exp (rho * (L^(depth+1))^(-1))` and the inverse-scale
block-boundary factor remain separate and literal. The Fourier/operator
dictionary, a depth-uniform simplification of the displayed coefficient,
physical `B0`, window 15 and terminal fields remain open.
-/

namespace YangMills.RG

noncomputable section

/-- Exact coefficient obtained after installing the physical link and the
inverse-scale owner transport in the fine-lattice normalized integral. -/
def cmp116CMP89PhysicalFineNormalizedStabilizedIntegralAmplitudeBound
    (L depth : ℕ) (a rho : ℝ) : ℝ :=
  (1 + Real.exp
      (rho * cmp89Eq249FineLatticeSpacing L (depth + 1))) *
    Real.exp
      ((rho * cmp89Eq249FineLatticeSpacing L (depth + 1)) *
        (2 * (L ^ (depth + 1) - 1) : ℕ)) *
      cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho

/-- The displayed physical fine-lattice owner coefficient is nonnegative. -/
theorem cmp116CMP89PhysicalFineNormalizedStabilizedIntegralAmplitudeBound_nonneg
    {L depth : ℕ} {a rho : ℝ} (hrho : 0 ≤ rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho) :
    0 ≤ cmp116CMP89PhysicalFineNormalizedStabilizedIntegralAmplitudeBound
      L depth a rho := by
  rw [cmp116CMP89PhysicalFineNormalizedStabilizedIntegralAmplitudeBound]
  have hmajorant :
      0 ≤ cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho :=
    cmp89Eq251ComplexStabilizedEndpointAmplitudeBound_nonneg hrho hwindow
  positivity

/-- The source-normalized fine-lattice integral, specialized to the literal
physical bond and fine-site transport, has fixed owner rate `rho`. The exact
unit-edge and inverse-scale boundary costs remain visible in its coefficient. -/
theorem norm_cmp116CMP89PhysicalFineNormalizedStabilizedIntegral_le_owner
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
      cmp116CMP89PhysicalFineNormalizedStabilizedIntegralAmplitudeBound
          L depth a rho *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (cmp116BondTarget b))
            (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ)) := by
  let xi : ℝ := cmp89Eq249FineLatticeSpacing L (depth + 1)
  let rate : ℝ := rho * xi
  let transport : Fin 4 → ℤ :=
    cmp116CMP89PhysicalBondTransportDisplacement b y
  let first : Fin 4 → ℤ := fun nu =>
    cmp116CMP89PhysicalBondHolderDisplacement b nu + transport nu
  let ownerDist : ℝ :=
    finBoxDist
      (cmp99Eq389SourceLocalizationOwner L K Q depth (cmp116BondTarget b))
      (cmp99Eq389SourceLocalizationOwner L K Q depth y)
  have hxi : 0 ≤ xi := by
    exact (cmp89Eq249FineLatticeSpacing_pos L (depth + 1)).le
  have hrate : 0 ≤ rate := mul_nonneg hrho hxi
  have hweight (u : Fin 4 → ℤ) :
      Real.exp (-(rho * cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L (depth + 1)) u))) =
        cmp89SignedLatticeL1ExponentialWeight rate u := by
    rw [cmp89Eq251DisplacementL1_physicalFineLatticeDisplacement hxi,
      cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
    unfold cmp89Eq251LatticeL1Length
    congr 1
    dsimp [rate, xi]
    ring
  have hscale : rate * (L ^ (depth + 1) : ℝ) = rho := by
    have hL : (L : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
    have hpow : (L : ℝ) ^ (depth + 1) ≠ 0 := pow_ne_zero _ hL
    dsimp [rate, xi, cmp89Eq249FineLatticeSpacing]
    rw [Nat.cast_pow]
    rw [mul_assoc, inv_mul_cancel₀ hpow, mul_one]
  have hnormalized :=
    norm_cmp89Eq249NormalizedFineLatticeStabilizedIntegral_le
      (L := L) (j := depth + 1) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass mu
      (cmp116CMP89PhysicalBondHolderDisplacement b) transport
  rw [hweight, hweight] at hnormalized
  have hweights :=
    cmp116CMP89PhysicalEndpointWeights_le_ownerWeight
      depth hrate b y
  have hweights' :
      cmp89SignedLatticeL1ExponentialWeight rate first +
        cmp89SignedLatticeL1ExponentialWeight rate transport ≤
      (1 + Real.exp rate) *
        (Real.exp
            (rate * (2 * (L ^ (depth + 1) - 1) : ℕ)) *
          Real.exp (-rho * ownerDist)) := by
    rw [← hscale]
    calc
      cmp89SignedLatticeL1ExponentialWeight rate first +
          cmp89SignedLatticeL1ExponentialWeight rate transport =
        cmp89SignedLatticeL1ExponentialWeight rate transport +
          cmp89SignedLatticeL1ExponentialWeight rate first := add_comm _ _
      _ ≤ _ := by
        simpa [first, transport, ownerDist,
          cmp116CMP89PhysicalBondFirstEndpointDisplacement] using hweights
  have hmajorant :
      0 ≤ cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho :=
    cmp89Eq251ComplexStabilizedEndpointAmplitudeBound_nonneg hrho hwindow
  have htransport := mul_le_mul_of_nonneg_right hweights' hmajorant
  calc
    ‖cmp89Eq249NormalizedFineLatticeStabilizedIntegral
        L (depth + 1) mass a mu
        (cmp116CMP89PhysicalBondHolderDisplacement b)
        (cmp116CMP89PhysicalBondTransportDisplacement b y)‖ ≤
      (cmp89SignedLatticeL1ExponentialWeight rate first +
        cmp89SignedLatticeL1ExponentialWeight rate transport) *
          cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho := by
      simpa [first, transport, xi] using hnormalized
    _ ≤ ((1 + Real.exp rate) *
        (Real.exp (rate * (2 * (L ^ (depth + 1) - 1) : ℕ)) *
          Real.exp (-rho * ownerDist))) *
        cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho :=
      htransport
    _ = cmp116CMP89PhysicalFineNormalizedStabilizedIntegralAmplitudeBound
          L depth a rho * Real.exp (-rho * ownerDist) := by
      rw [cmp116CMP89PhysicalFineNormalizedStabilizedIntegralAmplitudeBound]
      dsimp [rate, xi]
      ring
    _ = cmp116CMP89PhysicalFineNormalizedStabilizedIntegralAmplitudeBound
          L depth a rho *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (cmp116BondTarget b))
            (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ)) := by
      rfl

end

end YangMills.RG
