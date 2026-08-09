/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249NormalizedStabilizedIntegralRecombination
import YangMills.RG.BalabanCMP116CMP89PhysicalOwnerExponentialTransport

/-!
# PRE-VALIDATION: physical owner bound for the normalized CMP89 integral

Source is present, but this module's `.olean` has not yet been materialized
and its declarations have not yet been verified by the compiler.

The normalized complete stabilized integral is specialized to the exact
physical Holder and transport displacements.  The already sealed endpoint
comparison is cited by name, so the one-link factor `1 + exp rho`, the block
boundary factor and the owner decay remain separate and literal.

This module does not sum localization owners, construct the full CMP99
regional Green certificate, attain window 15, discharge rows 23--24 or
inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- The scale-uniform endpoint-amplitude coefficient after the exact
one-link and block-boundary transports have been exposed. -/
def cmp116CMP89PhysicalNormalizedStabilizedIntegralAmplitudeBound
    (L depth : ℕ) (a rho : ℝ) : ℝ :=
  (1 + Real.exp rho) *
    Real.exp (rho * (2 * (L ^ (depth + 1) - 1) : ℕ)) *
      cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho

/-- The explicit stabilized endpoint-amplitude majorant is nonnegative under
the same central-window hypothesis used by its reciprocal factor. -/
theorem cmp89Eq251ComplexStabilizedEndpointAmplitudeBound_nonneg
    {a rho : ℝ} (hrho : 0 ≤ rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho) :
    0 ≤ cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho := by
  have hrecip :
      0 ≤ cmp89Eq249CentralStabilizedComplexReciprocalBound a rho := by
    rw [cmp89Eq249CentralStabilizedComplexReciprocalBound]
    have hgap :
        0 < cmp89Eq249CentralStabilizedLowerConstant 4 a -
          cmp89Eq249CentralStabilizedDenominatorVariationBound a rho := by
      simpa [CMP89Eq249CentralStabilizedComplexWindow] using hwindow
    exact inv_nonneg.mpr hgap.le
  have hcentral :
      0 ≤ cmp89Eq251ComplexCentralEndpointAmplitudeBound rho := by
    rw [cmp89Eq251ComplexCentralEndpointAmplitudeBound]
    positivity
  have hfine :
      0 ≤ cmp89Eq251CentralFineSymbolStripUpperBound rho := by
    rw [cmp89Eq251CentralFineSymbolStripUpperBound,
      cmp89Eq249CentralFineSymbolVerticalBound,
      cmp89Eq249CentralFineSymbolRealBound]
    positivity
  have hnoncentral :
      0 ≤ cmp89Eq251ComplexNoncentralEndpointQuotientSumBound rho := by
    rw [cmp89Eq251ComplexNoncentralEndpointQuotientSumBound,
      cmp89Eq251ComplexNoncentralEndpointQuotientConstant,
      cmp89Eq251ComplexNoncentralEndpointRadialConstant,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hamplitude :
      0 ≤ cmp89Eq251ComplexEndpointAmplitudeBound rho := by
    rw [cmp89Eq251ComplexEndpointAmplitudeBound]
    exact add_nonneg hcentral (mul_nonneg hfine hnoncentral)
  rw [cmp89Eq251ComplexStabilizedEndpointAmplitudeBound]
  exact mul_nonneg hamplitude hrecip

/-- The literal normalized physical integral is bounded by one owner decay.
The coefficient retains the exact one-link and block-boundary factors. -/
theorem norm_cmp116CMP89PhysicalNormalizedStabilizedIntegral_le_owner
    {L K Q j : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ) {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ‖cmp89Eq249NormalizedFourDimensionalStabilizedIntegral
        L j mass a alpha mu
        (cmp116CMP89PhysicalBondHolderDisplacement b)
        (cmp116CMP89PhysicalBondTransportDisplacement b y)‖ ≤
      cmp116CMP89PhysicalNormalizedStabilizedIntegralAmplitudeBound
          L depth a rho *
        Real.exp (-(rho * (L ^ (depth + 1) : ℝ)) *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (cmp116BondTarget b))
            (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ)) := by
  have hnormalized :=
    norm_cmp89Eq249NormalizedFourDimensionalStabilizedIntegral_le
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hmassPos hrho hradius hmass hwindow hamplitude mu
      (holderU := cmp116CMP89PhysicalBondHolderDisplacement b)
      (transportU := cmp116CMP89PhysicalBondTransportDisplacement b y)
      (cmp116CMP89PhysicalBondHolderDisplacement_unit b)
  have hweights :=
    cmp116CMP89PhysicalEndpointWeights_le_ownerWeight depth hrho b y
  have hweights' :
      cmp89SignedLatticeL1ExponentialWeight rho
          (fun nu ↦ cmp116CMP89PhysicalBondHolderDisplacement b nu +
            cmp116CMP89PhysicalBondTransportDisplacement b y nu) +
        cmp89SignedLatticeL1ExponentialWeight rho
          (cmp116CMP89PhysicalBondTransportDisplacement b y) ≤
      (1 + Real.exp rho) *
        (Real.exp (rho * (2 * (L ^ (depth + 1) - 1) : ℕ)) *
          Real.exp (-(rho * (L ^ (depth + 1) : ℝ)) *
            (finBoxDist
              (cmp99Eq389SourceLocalizationOwner L K Q depth
                (cmp116BondTarget b))
              (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ))) := by
    calc
      cmp89SignedLatticeL1ExponentialWeight rho
          (fun nu ↦ cmp116CMP89PhysicalBondHolderDisplacement b nu +
            cmp116CMP89PhysicalBondTransportDisplacement b y nu) +
        cmp89SignedLatticeL1ExponentialWeight rho
          (cmp116CMP89PhysicalBondTransportDisplacement b y) =
        cmp89SignedLatticeL1ExponentialWeight rho
            (cmp116CMP89PhysicalBondTransportDisplacement b y) +
          cmp89SignedLatticeL1ExponentialWeight rho
            (fun nu ↦ cmp116CMP89PhysicalBondHolderDisplacement b nu +
              cmp116CMP89PhysicalBondTransportDisplacement b y nu) :=
        add_comm _ _
      _ ≤ _ := by
        simpa [cmp116CMP89PhysicalBondFirstEndpointDisplacement] using hweights
  have hmajorantNonneg :
      0 ≤ cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho :=
    cmp89Eq251ComplexStabilizedEndpointAmplitudeBound_nonneg hrho hwindow
  have htransport :=
    mul_le_mul_of_nonneg_right hweights' hmajorantNonneg
  calc
    ‖cmp89Eq249NormalizedFourDimensionalStabilizedIntegral
        L j mass a alpha mu
        (cmp116CMP89PhysicalBondHolderDisplacement b)
        (cmp116CMP89PhysicalBondTransportDisplacement b y)‖ ≤
      (cmp89SignedLatticeL1ExponentialWeight rho
          (fun nu ↦ cmp116CMP89PhysicalBondHolderDisplacement b nu +
            cmp116CMP89PhysicalBondTransportDisplacement b y nu) +
        cmp89SignedLatticeL1ExponentialWeight rho
          (cmp116CMP89PhysicalBondTransportDisplacement b y)) *
        cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho :=
      hnormalized
    _ ≤ ((1 + Real.exp rho) *
          (Real.exp (rho * (2 * (L ^ (depth + 1) - 1) : ℕ)) *
            Real.exp (-(rho * (L ^ (depth + 1) : ℝ)) *
              (finBoxDist
                (cmp99Eq389SourceLocalizationOwner L K Q depth
                  (cmp116BondTarget b))
                (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ)))) *
          cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho :=
      htransport
    _ = cmp116CMP89PhysicalNormalizedStabilizedIntegralAmplitudeBound
          L depth a rho *
        Real.exp (-(rho * (L ^ (depth + 1) : ℝ)) *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (cmp116BondTarget b))
            (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ)) := by
      rw [cmp116CMP89PhysicalNormalizedStabilizedIntegralAmplitudeBound]
      ring

end

end YangMills.RG
