/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116CMP89PhysicalOwnerExponentialTransport
import YangMills.RG.BalabanCMP99SourceLocalizationOwnerForwardDistanceBridge

/-!
# PRE-VALIDATION: fixed-rate CMP89 transport to CMP99 owners

Source is present at the checkpoint containing this file; its `.olean` has not
yet been materialized and the result is not yet compiler-verified.

The earlier inverse-scale transport keeps the stronger owner rate
`rho * L^(depth+1)` but necessarily exposes the block-boundary factor
`exp (2*rho*(L^(depth+1)-1))`.  For the scale-uniform coefficient needed by
the source Green estimate, this module instead uses the complementary sealed
metric direction

`ownerDist <= transportL1`.

It therefore retains the fixed positive rate `rho` and removes the
depth-dependent boundary coefficient.  The two independently displaced
endpoints are recombined through the literal unit-edge theorem, leaving the
exact factor `1 + exp rho`.

Honest scope: this module transports only exponential geometry.  It does not
identify the normalized CMP89 Fourier integral with the printed Holder
difference of `D G_j Q_j^*`, construct the complete physical `B0`, attain
window 15, discharge a terminal field, or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Fine-lattice transport decay gives fixed-rate owner decay with no
depth-dependent boundary factor. -/
theorem cmp116CMP89PhysicalTransportWeight_le_fixedRateOwnerWeight
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ) {rho : ℝ} (hrho : 0 ≤ rho)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp89SignedLatticeL1ExponentialWeight rho
        (cmp116CMP89PhysicalBondTransportDisplacement b y) ≤
      Real.exp (-rho *
        (finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth
            (cmp116BondTarget b))
          (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ)) := by
  let transport := cmp116CMP89PhysicalBondTransportDisplacement b y
  let ownerDist : ℝ :=
    finBoxDist
      (cmp99Eq389SourceLocalizationOwner L K Q depth (cmp116BondTarget b))
      (cmp99Eq389SourceLocalizationOwner L K Q depth y)
  have hmetric : ownerDist ≤ cmp89Eq251LatticeL1Length transport := by
    simpa [ownerDist, transport] using
      cmp99Eq389SourceLocalizationOwner_dist_le_transportL1 depth b y
  have hmul := mul_le_mul_of_nonneg_left hmetric hrho
  have hexponent :
      -rho * cmp89Eq251LatticeL1Length transport ≤ -rho * ownerDist := by
    nlinarith
  rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
  simpa [transport, ownerDist, cmp89Eq251LatticeL1Length] using
    (Real.exp_le_exp.mpr hexponent)

/-- Both physical endpoint weights are controlled by one fixed-rate owner
decay.  The only recombination cost is the exact one-link factor
`1 + exp rho`. -/
theorem cmp116CMP89PhysicalEndpointWeights_le_fixedRateOwnerWeight
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ) {rho : ℝ} (hrho : 0 ≤ rho)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp89SignedLatticeL1ExponentialWeight rho
        (cmp116CMP89PhysicalBondTransportDisplacement b y) +
      cmp89SignedLatticeL1ExponentialWeight rho
        (cmp116CMP89PhysicalBondFirstEndpointDisplacement b y) ≤
      (1 + Real.exp rho) *
        Real.exp (-rho *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (cmp116BondTarget b))
            (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ)) := by
  let transport := cmp116CMP89PhysicalBondTransportDisplacement b y
  let common :=
    Real.exp (-rho *
      (finBoxDist
        (cmp99Eq389SourceLocalizationOwner L K Q depth (cmp116BondTarget b))
        (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ))
  have htransport :
      cmp89SignedLatticeL1ExponentialWeight rho transport ≤ common := by
    exact cmp116CMP89PhysicalTransportWeight_le_fixedRateOwnerWeight
      depth hrho b y
  have hfirst0 :=
    cmp89SignedLatticeL1ExponentialWeight_add_le_exp_mul_transport
      (holder := cmp116CMP89PhysicalBondHolderDisplacement b)
      (transport := transport) hrho
      (cmp116CMP89PhysicalBondHolderDisplacement_unit b)
  have hfirst :
      cmp89SignedLatticeL1ExponentialWeight rho
          (cmp116CMP89PhysicalBondFirstEndpointDisplacement b y) ≤
        Real.exp rho * common := by
    calc
      cmp89SignedLatticeL1ExponentialWeight rho
          (cmp116CMP89PhysicalBondFirstEndpointDisplacement b y) ≤
          Real.exp rho *
            cmp89SignedLatticeL1ExponentialWeight rho transport := by
              simpa [cmp116CMP89PhysicalBondFirstEndpointDisplacement,
                transport] using hfirst0
      _ ≤ Real.exp rho * common :=
        mul_le_mul_of_nonneg_left htransport (Real.exp_pos rho).le
  calc
    cmp89SignedLatticeL1ExponentialWeight rho transport +
        cmp89SignedLatticeL1ExponentialWeight rho
          (cmp116CMP89PhysicalBondFirstEndpointDisplacement b y) ≤
      common + Real.exp rho * common := add_le_add htransport hfirst
    _ = (1 + Real.exp rho) * common := by ring

end

end YangMills.RG
