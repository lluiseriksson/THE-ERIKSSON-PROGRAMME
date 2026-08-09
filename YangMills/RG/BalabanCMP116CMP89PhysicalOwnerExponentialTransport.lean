/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceLocalizationOwnerDistanceBridge

/-!
# PRE-VALIDATION: CMP89 fine decay transported to CMP99 owners

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.

The preceding sealed metric bridge proves

`ell * ownerDist <= transportL1 + 2*(ell-1)`.

This file exponentiates that inequality in the decreasing direction.  The
result retains separately

* owner rate `rho * ell`,
* block-boundary cost `exp (rho * 2*(ell-1))`, and
* the one-link endpoint cost `exp rho`.

The two endpoint weights are finally bounded by the literal factor
`1 + exp rho`; no cost is hidden in `B0`.  The reverse endpoint comparison is
proved from the negative of the already sealed unit Holder edge, rather than
assuming a second geometric premise.

Honest scope: this module transports only exponential geometry.  It does not
bound the stabilized endpoint amplitudes, construct the complete `B0`, attain
window 15, discharge a terminal field, or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Negating an integer displacement preserves its literal lattice `l1`
length. -/
theorem cmp89Eq251LatticeL1Length_neg {d : ℕ} (u : Fin d → ℤ) :
    cmp89Eq251LatticeL1Length (fun mu ↦ -u mu) =
      cmp89Eq251LatticeL1Length u := by
  unfold cmp89Eq251LatticeL1Length
  simp

/-- The negative of a named unit displacement is again a unit displacement. -/
theorem CMP89Eq251UnitLatticeBondDisplacement.neg {d : ℕ}
    {u : Fin d → ℤ} (hunit : CMP89Eq251UnitLatticeBondDisplacement u) :
    CMP89Eq251UnitLatticeBondDisplacement (fun mu ↦ -u mu) := by
  unfold CMP89Eq251UnitLatticeBondDisplacement at hunit ⊢
  rw [cmp89Eq251LatticeL1Length_neg]
  exact hunit

/-- The first endpoint weight is at most `exp rho` times the transport
endpoint weight.  This is the orientation needed to use the target-owner
metric for both endpoint terms. -/
theorem cmp89SignedLatticeL1ExponentialWeight_add_le_exp_mul_transport
    {d : ℕ} {rho : ℝ} (hrho : 0 ≤ rho)
    {holder transport : Fin d → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holder) :
    cmp89SignedLatticeL1ExponentialWeight rho
        (fun mu ↦ holder mu + transport mu) ≤
      Real.exp rho * cmp89SignedLatticeL1ExponentialWeight rho transport := by
  let first : Fin d → ℤ := fun mu ↦ holder mu + transport mu
  have hnegUnit : CMP89Eq251UnitLatticeBondDisplacement
      (fun mu ↦ -holder mu) := hunit.neg
  have hlength0 :=
    cmp89Eq251LatticeL1Length_add_le_add_one_of_unit
      (holder := fun mu ↦ -holder mu) (transport := first) hnegUnit
  have hcancel : (fun mu ↦ -holder mu + first mu) = transport := by
    funext mu
    simp [first]
  have hlength : cmp89Eq251LatticeL1Length transport ≤
      cmp89Eq251LatticeL1Length first + 1 := by
    rw [hcancel] at hlength0
    exact hlength0
  rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs,
    cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
  have hexponent :
      -rho * cmp89Eq251LatticeL1Length first ≤
        rho + -rho * cmp89Eq251LatticeL1Length transport := by
    have hmul := mul_le_mul_of_nonneg_left hlength hrho
    nlinarith
  calc
    Real.exp (-rho * ∑ mu, (((holder mu + transport mu).natAbs : ℕ) : ℝ)) ≤
        Real.exp (rho + -rho * ∑ mu, ((transport mu).natAbs : ℝ)) := by
      simpa [first, cmp89Eq251LatticeL1Length] using
        (Real.exp_le_exp.mpr hexponent)
    _ = Real.exp rho *
        Real.exp (-rho * ∑ mu, ((transport mu).natAbs : ℝ)) := by
      rw [Real.exp_add]

/-- Fine-lattice transport decay becomes owner-block decay with exact rate
and boundary factor. -/
theorem cmp116CMP89PhysicalTransportWeight_le_ownerWeight
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ) {rho : ℝ} (hrho : 0 ≤ rho)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp89SignedLatticeL1ExponentialWeight rho
        (cmp116CMP89PhysicalBondTransportDisplacement b y) ≤
      Real.exp (rho * (2 * (L ^ (depth + 1) - 1) : ℕ)) *
        Real.exp (-(rho * (L ^ (depth + 1) : ℝ)) *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (cmp116BondTarget b))
            (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ)) := by
  let transport := cmp116CMP89PhysicalBondTransportDisplacement b y
  let ownerDist : ℝ :=
    finBoxDist
      (cmp99Eq389SourceLocalizationOwner L K Q depth (cmp116BondTarget b))
      (cmp99Eq389SourceLocalizationOwner L K Q depth y)
  let boundary : ℝ := (2 * (L ^ (depth + 1) - 1) : ℕ)
  have hmetric :=
    cmp99Eq389SourceLocalizationOwner_mul_dist_le_transportL1_add_boundary
      depth b y
  have hmul := mul_le_mul_of_nonneg_left hmetric hrho
  have hexponent :
      -rho * cmp89Eq251LatticeL1Length transport ≤
        rho * boundary +
          -(rho * (L ^ (depth + 1) : ℝ)) * ownerDist := by
    dsimp [transport, ownerDist, boundary] at hmul ⊢
    nlinarith
  rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
  calc
    Real.exp (-rho * ∑ mu, ((transport mu).natAbs : ℝ)) ≤
        Real.exp (rho * boundary +
          -(rho * (L ^ (depth + 1) : ℝ)) * ownerDist) := by
      simpa [transport, cmp89Eq251LatticeL1Length] using
        (Real.exp_le_exp.mpr hexponent)
    _ = Real.exp (rho * boundary) *
        Real.exp (-(rho * (L ^ (depth + 1) : ℝ)) * ownerDist) := by
      rw [Real.exp_add]

/-- Both physical endpoint weights are controlled by one target-owner decay.
The neighbour factor and block-boundary factor remain separate and literal. -/
theorem cmp116CMP89PhysicalEndpointWeights_le_ownerWeight
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
        (Real.exp (rho * (2 * (L ^ (depth + 1) - 1) : ℕ)) *
          Real.exp (-(rho * (L ^ (depth + 1) : ℝ)) *
            (finBoxDist
              (cmp99Eq389SourceLocalizationOwner L K Q depth
                (cmp116BondTarget b))
              (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ))) := by
  let transport := cmp116CMP89PhysicalBondTransportDisplacement b y
  let common :=
    Real.exp (rho * (2 * (L ^ (depth + 1) - 1) : ℕ)) *
      Real.exp (-(rho * (L ^ (depth + 1) : ℝ)) *
        (finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth
            (cmp116BondTarget b))
          (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ))
  have htransport :
      cmp89SignedLatticeL1ExponentialWeight rho transport ≤ common := by
    exact cmp116CMP89PhysicalTransportWeight_le_ownerWeight depth hrho b y
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
