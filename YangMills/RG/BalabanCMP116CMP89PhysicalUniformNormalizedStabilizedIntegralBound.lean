/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116CMP89PhysicalFixedRateOwnerTransport
import YangMills.RG.BalabanCMP116CMP89PhysicalNormalizedStabilizedIntegralBound

/-!
# Uniform-coefficient physical CMP89 integral bound

This module and its audit were compiler-verified in the cold run recorded in
the verification ledger.

The normalized complete stabilized integral is specialized to the literal
physical Holder and transport displacements.  The fixed-rate owner bridge
removes the depth-dependent block-boundary coefficient while retaining the
exact endpoint factor `1 + exp rho`.

Primary-source scope is deliberately narrower than the old generic label:
CMP89 equation (2.49) is the Fourier integral for the normalized Holder
difference of the left derivative of `G_j Q_j^*`.  The integrand in this
module has that literal source shape, but the equality to the source Green
operator is still an open Fourier/operator dictionary.  Consequently this
theorem is not called a construction of the complete `B0` or of a regional
Green certificate.

This module does not attain window 15, discharge rows 23--24, or inhabit a
`TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Depth-independent endpoint coefficient for the source-shaped normalized
CMP89 (2.49) integral.  It is not yet the complete physical `B0`, because the
Fourier integral has not been identified with the literal Green operator. -/
def cmp116CMP89PhysicalUniformNormalizedStabilizedIntegralAmplitudeBound
    (a rho : ℝ) : ℝ :=
  (1 + Real.exp rho) *
    cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho

/-- The literal source-shaped normalized integral has a coefficient uniform
in localization depth at the fixed owner rate `rho`. -/
theorem norm_cmp116CMP89PhysicalNormalizedStabilizedIntegral_le_fixedRateOwner
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
      cmp116CMP89PhysicalUniformNormalizedStabilizedIntegralAmplitudeBound
          a rho *
        Real.exp (-rho *
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
    cmp116CMP89PhysicalEndpointWeights_le_fixedRateOwnerWeight
      depth hrho b y
  have hweights' :
      cmp89SignedLatticeL1ExponentialWeight rho
          (fun nu ↦ cmp116CMP89PhysicalBondHolderDisplacement b nu +
            cmp116CMP89PhysicalBondTransportDisplacement b y nu) +
        cmp89SignedLatticeL1ExponentialWeight rho
          (cmp116CMP89PhysicalBondTransportDisplacement b y) ≤
      (1 + Real.exp rho) *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (cmp116BondTarget b))
            (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ)) := by
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
          Real.exp (-rho *
            (finBoxDist
              (cmp99Eq389SourceLocalizationOwner L K Q depth
                (cmp116BondTarget b))
              (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ))) *
          cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho :=
      htransport
    _ = cmp116CMP89PhysicalUniformNormalizedStabilizedIntegralAmplitudeBound
          a rho *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (cmp116BondTarget b))
            (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ)) := by
      rw [cmp116CMP89PhysicalUniformNormalizedStabilizedIntegralAmplitudeBound]
      ring

end

end YangMills.RG
